// Solver detection and status reporting for dMATH tool binaries
//
// Searches PATH and common installation locations for each dMATH solver
// binary, parses version output, and reports availability.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde::Serialize;

/// Known dMATH solver tools and the proof levels they support.
const KNOWN_SOLVERS: &[SolverSpec] = &[
    SolverSpec {
        name: "z4",
        binary: "z4",
        description: "Primary SMT solver (80-90% of obligations)",
        proof_levels: &["L0"],
    },
    SolverSpec {
        name: "zani",
        binary: "zani",
        description: "Bounded model checking, counterexamples",
        proof_levels: &["L0"],
    },
    SolverSpec {
        name: "certus",
        binary: "certus",
        description: "Ownership-aware verification",
        proof_levels: &["L0"],
    },
    SolverSpec {
        name: "sunder",
        binary: "sunder",
        description: "Deductive verification, strongest postconditions",
        proof_levels: &["L1"],
    },
    SolverSpec {
        name: "tla2",
        binary: "tla2",
        description: "Temporal logic for distributed protocols",
        proof_levels: &["L2"],
    },
    SolverSpec {
        name: "lean5",
        binary: "lean5",
        description: "Higher-order prover, induction",
        proof_levels: &["L2"],
    },
];

/// Static specification of a known solver.
struct SolverSpec {
    name: &'static str,
    binary: &'static str,
    description: &'static str,
    proof_levels: &'static [&'static str],
}

/// Information about a detected (or missing) solver.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct SolverInfo {
    pub(crate) name: String,
    pub(crate) description: String,
    pub(crate) proof_levels: Vec<String>,
    pub(crate) available: bool,
    pub(crate) path: Option<PathBuf>,
    pub(crate) version: Option<String>,
}

/// Common installation directories to search beyond PATH.
fn common_search_dirs() -> Vec<PathBuf> {
    let mut dirs = Vec::new();

    // Cargo bin directory
    if let Some(home) = home_dir() {
        dirs.push(home.join(".cargo/bin"));
    }

    // Homebrew paths
    dirs.push(PathBuf::from("/opt/homebrew/bin"));
    dirs.push(PathBuf::from("/usr/local/bin"));

    // dMATH-specific install locations
    if let Some(home) = home_dir() {
        dirs.push(home.join(".dmath/bin"));
        dirs.push(home.join("dmath/bin"));
    }

    dirs
}

/// Get the user's home directory.
fn home_dir() -> Option<PathBuf> {
    std::env::var("HOME")
        .ok()
        .map(PathBuf::from)
}

/// Search for a binary by name on PATH and in common locations.
fn find_binary(name: &str) -> Option<PathBuf> {
    // First: check if `which` finds it on PATH.
    if let Ok(output) = Command::new("which").arg(name).output() {
        if output.status.success() {
            let path_str = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !path_str.is_empty() {
                let path = PathBuf::from(&path_str);
                if path.is_file() {
                    return Some(path);
                }
            }
        }
    }

    // Second: search common directories.
    for dir in common_search_dirs() {
        let candidate = dir.join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }

    None
}

/// Try to extract a version string from a binary's `--version` output.
fn detect_version(binary_path: &Path) -> Option<String> {
    let output = Command::new(binary_path)
        .arg("--version")
        .output()
        .ok()?;

    if !output.status.success() {
        return None;
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let first_line = stdout.lines().next()?.trim().to_string();
    if first_line.is_empty() {
        return None;
    }
    Some(first_line)
}

/// Detect a single solver by name.
///
/// Returns `SolverInfo` with `available: true` if found, `false` otherwise.
pub(crate) fn detect_solver(name: &str) -> SolverInfo {
    let spec = KNOWN_SOLVERS.iter().find(|s| s.name == name);

    let (description, proof_levels) = match spec {
        Some(s) => (
            s.description.to_string(),
            s.proof_levels.iter().map(|l| l.to_string()).collect(),
        ),
        None => (
            format!("Unknown solver: {name}"),
            vec![],
        ),
    };

    let binary_name = spec.map_or(name, |s| s.binary);

    match find_binary(binary_name) {
        Some(path) => {
            let version = detect_version(&path);
            SolverInfo {
                name: name.to_string(),
                description,
                proof_levels,
                available: true,
                path: Some(path),
                version,
            }
        }
        None => SolverInfo {
            name: name.to_string(),
            description,
            proof_levels,
            available: false,
            path: None,
            version: None,
        },
    }
}

/// Detect all known solvers and return their status.
pub(crate) fn detect_all_solvers() -> Vec<SolverInfo> {
    KNOWN_SOLVERS.iter().map(|spec| detect_solver(spec.name)).collect()
}

/// Validate that a solver name is known.
pub(crate) fn is_known_solver(name: &str) -> bool {
    KNOWN_SOLVERS.iter().any(|s| s.name == name)
}

/// Get the list of known solver names.
pub(crate) fn known_solver_names() -> Vec<&'static str> {
    KNOWN_SOLVERS.iter().map(|s| s.name).collect()
}

/// Render solver status to terminal.
pub(crate) fn render_solvers_terminal(solvers: &[SolverInfo]) {
    eprintln!();
    eprintln!("=== tRust Solver Status ===");
    eprintln!();

    // Group by proof level for clarity.
    let mut by_level: HashMap<String, Vec<&SolverInfo>> = HashMap::new();
    for solver in solvers {
        for level in &solver.proof_levels {
            by_level.entry(level.clone()).or_default().push(solver);
        }
        if solver.proof_levels.is_empty() {
            by_level.entry("unknown".to_string()).or_default().push(solver);
        }
    }

    let mut available_count = 0;
    let total = solvers.len();

    for solver in solvers {
        let status = if solver.available {
            available_count += 1;
            "FOUND"
        } else {
            "MISSING"
        };

        let version_str = solver
            .version
            .as_deref()
            .map(|v| format!(" ({v})"))
            .unwrap_or_default();

        let path_str = solver
            .path
            .as_deref()
            .map(|p| format!(" at {}", p.display()))
            .unwrap_or_default();

        let levels = if solver.proof_levels.is_empty() {
            String::new()
        } else {
            format!(" [{}]", solver.proof_levels.join(", "))
        };

        eprintln!(
            "  [{status:>7}] {:<10} {}{levels}{version_str}{path_str}",
            solver.name, solver.description
        );
    }

    eprintln!();
    eprintln!(
        "Summary: {available_count}/{total} solvers available"
    );

    if available_count == 0 {
        eprintln!();
        eprintln!("No solvers found. Verification will produce only Unknown results.");
        eprintln!(
            "Install solvers from their dMATH repos (see cargo-trust/README.md for install notes)."
        );
        eprintln!();
        eprintln!("Solver requirements by proof level:");
        eprintln!("  L0 (basic):    z4 + zani + certus");
        eprintln!("  L1 (moderate): L0 + sunder");
        eprintln!("  L2 (full):     L1 + tla2 + lean5");
    } else if available_count < total {
        eprintln!();
        eprintln!(
            "Some solvers are missing. Full verification requires all solvers."
        );
    }

    eprintln!("===========================");
}

/// Render solver status as JSON.
pub(crate) fn render_solvers_json(solvers: &[SolverInfo]) {
    #[derive(Serialize)]
    struct SolverReport {
        solvers: Vec<SolverInfo>,
        available: usize,
        total: usize,
    }

    let available = solvers.iter().filter(|s| s.available).count();
    let report = SolverReport {
        solvers: solvers.to_vec(),
        available,
        total: solvers.len(),
    };

    match serde_json::to_string_pretty(&report) {
        Ok(json) => println!("{json}"),
        Err(e) => eprintln!("cargo-trust: failed to serialize solver report: {e}"),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_known_solver_names() {
        let names = known_solver_names();
        assert!(names.contains(&"z4"));
        assert!(names.contains(&"zani"));
        assert!(names.contains(&"sunder"));
        assert!(names.contains(&"certus"));
        assert!(names.contains(&"tla2"));
        assert!(names.contains(&"lean5"));
        assert_eq!(names.len(), 6);
    }

    #[test]
    fn test_is_known_solver() {
        assert!(is_known_solver("z4"));
        assert!(is_known_solver("lean5"));
        assert!(!is_known_solver("nonexistent"));
        assert!(!is_known_solver(""));
    }

    #[test]
    fn test_detect_unknown_solver() {
        let info = detect_solver("definitely_not_a_real_solver_xyz");
        assert!(!info.available);
        assert!(info.path.is_none());
        assert!(info.version.is_none());
        assert_eq!(info.name, "definitely_not_a_real_solver_xyz");
    }

    #[test]
    fn test_detect_all_solvers_returns_all() {
        let solvers = detect_all_solvers();
        assert_eq!(solvers.len(), 6);
        // All should have names matching known solvers
        let names: Vec<&str> = solvers.iter().map(|s| s.name.as_str()).collect();
        assert!(names.contains(&"z4"));
        assert!(names.contains(&"lean5"));
    }

    #[test]
    fn test_solver_info_serialization() {
        let info = SolverInfo {
            name: "z4".to_string(),
            description: "SMT solver".to_string(),
            proof_levels: vec!["L0".to_string()],
            available: true,
            path: Some(PathBuf::from("/usr/local/bin/z4")),
            version: Some("z4 4.13.0".to_string()),
        };
        let json = serde_json::to_string(&info).expect("should serialize");
        assert!(json.contains("\"available\":true"));
        assert!(json.contains("\"name\":\"z4\""));
    }

    #[test]
    fn test_common_search_dirs_non_empty() {
        let dirs = common_search_dirs();
        // Should always include at least the homebrew paths
        assert!(!dirs.is_empty());
    }
}
