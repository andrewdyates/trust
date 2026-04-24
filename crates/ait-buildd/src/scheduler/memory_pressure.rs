//! Read macOS system memory pressure.
//!
//! On macOS we prefer `memory_pressure -Q`, which prints a short human-readable
//! status. If that tool is not on `PATH` (for example in a minimal container or
//! on a non-Darwin host where this code is nonetheless compiled), we fall back
//! to `vm_stat` and derive a rough pressure level from the page counts. If
//! neither tool is available, callers get [`MemoryPressureError::NoTool`].
//!
//! Parsing is factored out into [`parse_memory_pressure_output`] and
//! [`parse_vm_stat_output`] so the unit tests can exercise the classification
//! logic without invoking subprocesses.
//!
//! Part of #895, epic #894.

use std::io;
use std::process::Command;

use thiserror::Error;

/// Coarse system memory pressure state.
///
/// The scheduler uses this to decide how aggressively to cap parallelism.
/// The variants mirror what `memory_pressure -Q` emits on macOS.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum MemoryPressure {
    /// Plenty of free memory; full parallelism is fine.
    #[default]
    Normal,
    /// Memory is getting tight; scheduler should halve job caps.
    Warn,
    /// Memory is critically low; scheduler should collapse caps to 1 and
    /// consider pausing builds via SIGSTOP.
    Critical,
}

/// Errors produced by [`read_memory_pressure`] and its parsing helpers.
#[derive(Debug, Error)]
pub enum MemoryPressureError {
    /// The backing subprocess (`memory_pressure` or `vm_stat`) ran but failed,
    /// or its stdout was not valid UTF-8.
    #[error("memory-pressure command failed: {0}")]
    CommandFailed(#[from] io::Error),
    /// The tool's output did not match any pattern we recognise.
    #[error("unrecognised memory-pressure output: {0}")]
    UnrecognizedOutput(String),
    /// Neither `memory_pressure` nor `vm_stat` is on `PATH`.
    #[error("no memory-pressure tool available (tried memory_pressure, vm_stat)")]
    NoTool,
}

/// Read the current system memory pressure.
///
/// Tries `memory_pressure -Q` first; falls back to `vm_stat` if the primary
/// tool is not installed. Returns [`MemoryPressureError::NoTool`] if neither
/// is available.
pub fn read_memory_pressure() -> Result<MemoryPressure, MemoryPressureError> {
    match Command::new("memory_pressure").arg("-Q").output() {
        Ok(output) if output.status.success() => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            return parse_memory_pressure_output(&stdout);
        }
        Ok(_) => {
            // Tool exists but returned non-zero; fall through to vm_stat.
        }
        Err(err) if err.kind() == io::ErrorKind::NotFound => {
            // memory_pressure not installed; try vm_stat.
        }
        Err(err) => return Err(err.into()),
    }

    match Command::new("vm_stat").output() {
        Ok(output) if output.status.success() => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            parse_vm_stat_output(&stdout)
        }
        Ok(output) => Err(MemoryPressureError::UnrecognizedOutput(format!(
            "vm_stat exited {}",
            output.status
        ))),
        Err(err) if err.kind() == io::ErrorKind::NotFound => Err(MemoryPressureError::NoTool),
        Err(err) => Err(err.into()),
    }
}

/// Parse the output of `memory_pressure -Q`.
///
/// Accepts two shapes:
///
/// 1. A multi-line report where one line begins with `System-wide memory
///    pressure:` and ends with `Normal` / `Warn` / `Warning` / `Critical`.
/// 2. A bare one-word status like `normal` / `warn` / `critical` (used by some
///    older or stripped-down macOS builds).
///
/// Anything else is reported as [`MemoryPressureError::UnrecognizedOutput`].
pub(crate) fn parse_memory_pressure_output(
    raw: &str,
) -> Result<MemoryPressure, MemoryPressureError> {
    // First look for a "System-wide memory pressure: <WORD>" line.
    for line in raw.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        let lower = trimmed.to_ascii_lowercase();
        if let Some(rest) = lower.strip_prefix("system-wide memory pressure:") {
            let token = rest.trim();
            return classify_word(token)
                .ok_or_else(|| MemoryPressureError::UnrecognizedOutput(trimmed.to_string()));
        }
    }

    // Fallback: accept a bare one-word output.
    let collapsed = raw.trim();
    if !collapsed.is_empty()
        && collapsed.split_whitespace().count() == 1
        && let Some(state) = classify_word(collapsed)
    {
        return Ok(state);
    }

    Err(MemoryPressureError::UnrecognizedOutput(raw.trim().to_string()))
}

/// Parse the output of `vm_stat` and derive a coarse pressure level.
///
/// macOS `vm_stat` prints a header like
/// `Mach Virtual Memory Statistics: (page size of 16384 bytes)` followed by
/// lines of the form `Pages free: 12345.`. We sum the page categories that
/// are effectively "available" (`free`, `inactive`, `purgeable`,
/// `speculative`) and divide by the total of all known categories.
///
/// Thresholds: >=20% free -> Normal; >=8% free -> Warn; else Critical.
/// Missing the header or any required `Pages` line is treated as unrecognised
/// output so we don't silently return a wrong pressure level on non-macOS
/// hosts.
pub(crate) fn parse_vm_stat_output(raw: &str) -> Result<MemoryPressure, MemoryPressureError> {
    if !raw.contains("Mach Virtual Memory Statistics") {
        return Err(MemoryPressureError::UnrecognizedOutput("missing vm_stat header".to_string()));
    }

    // Categories we need for the ratio. All are "Pages <name>" lines.
    let required = ["free", "active", "inactive", "wired down", "purgeable", "speculative"];
    // `occupied by compressor` is optional — older macOS versions omit it.
    let optional = ["occupied by compressor"];

    let mut total: u64 = 0;
    let mut available: u64 = 0;

    for key in required {
        let value = find_pages_line(raw, key).ok_or_else(|| {
            MemoryPressureError::UnrecognizedOutput(format!("missing Pages {key}"))
        })?;
        total = total.saturating_add(value);
        if matches!(key, "free" | "inactive" | "purgeable" | "speculative") {
            available = available.saturating_add(value);
        }
    }
    for key in optional {
        if let Some(value) = find_pages_line(raw, key) {
            total = total.saturating_add(value);
        }
    }

    if total == 0 {
        return Err(MemoryPressureError::UnrecognizedOutput("total pages was zero".to_string()));
    }

    // Use integer math: ratio*1000 to avoid floats.
    let permille = available.saturating_mul(1000) / total;
    let pressure = if permille >= 200 {
        MemoryPressure::Normal
    } else if permille >= 80 {
        MemoryPressure::Warn
    } else {
        MemoryPressure::Critical
    };
    Ok(pressure)
}

/// Classify a single status word. Case-insensitive. Returns `None` on unknown
/// tokens so callers can surface `UnrecognizedOutput` with better context.
fn classify_word(word: &str) -> Option<MemoryPressure> {
    match word.trim().to_ascii_lowercase().as_str() {
        "normal" => Some(MemoryPressure::Normal),
        "warn" | "warning" => Some(MemoryPressure::Warn),
        "critical" => Some(MemoryPressure::Critical),
        _ => None,
    }
}

/// Find a line of the form `Pages <key>: <number>.` in `raw` and return the
/// number. Returns `None` if the line is missing or the number fails to parse.
fn find_pages_line(raw: &str, key: &str) -> Option<u64> {
    let needle = format!("Pages {key}:");
    for line in raw.lines() {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix(&needle) {
            // Strip trailing period and whitespace, then parse.
            let digits: String =
                rest.trim().trim_end_matches('.').chars().filter(|c| c.is_ascii_digit()).collect();
            return digits.parse::<u64>().ok();
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---------- memory_pressure -Q parsing ----------

    #[test]
    fn test_parse_memory_pressure_output_normal() {
        let out = "\
System-wide memory free percentage: 73%\n\
System-wide memory pressure: Normal\n";
        assert_eq!(
            parse_memory_pressure_output(out).expect("normal parses"),
            MemoryPressure::Normal
        );
    }

    #[test]
    fn test_parse_memory_pressure_output_warn() {
        let out = "\
System-wide memory free percentage: 12%\n\
System-wide memory pressure: Warn\n";
        assert_eq!(parse_memory_pressure_output(out).expect("warn parses"), MemoryPressure::Warn);
    }

    #[test]
    fn test_parse_memory_pressure_output_warning_alias() {
        let out = "System-wide memory pressure: Warning\n";
        assert_eq!(
            parse_memory_pressure_output(out).expect("warning parses"),
            MemoryPressure::Warn
        );
    }

    #[test]
    fn test_parse_memory_pressure_output_critical() {
        let out = "\
System-wide memory free percentage: 3%\n\
System-wide memory pressure: Critical\n";
        assert_eq!(
            parse_memory_pressure_output(out).expect("critical parses"),
            MemoryPressure::Critical
        );
    }

    #[test]
    fn test_parse_memory_pressure_output_bare_word_normal() {
        assert_eq!(
            parse_memory_pressure_output("normal\n").expect("bare normal"),
            MemoryPressure::Normal
        );
    }

    #[test]
    fn test_parse_memory_pressure_output_bare_word_mixed_case() {
        assert_eq!(
            parse_memory_pressure_output("Critical\n").expect("bare critical"),
            MemoryPressure::Critical
        );
    }

    #[test]
    fn test_parse_memory_pressure_output_bare_word_warn() {
        assert_eq!(parse_memory_pressure_output("warn").expect("bare warn"), MemoryPressure::Warn);
    }

    #[test]
    fn test_parse_memory_pressure_output_unrecognized_returns_error() {
        let err =
            parse_memory_pressure_output("something totally unexpected\n").expect_err("not ok");
        assert!(matches!(err, MemoryPressureError::UnrecognizedOutput(_)));
    }

    #[test]
    fn test_parse_memory_pressure_output_unknown_word_after_prefix() {
        let out = "System-wide memory pressure: Meltdown\n";
        let err = parse_memory_pressure_output(out).expect_err("unknown word");
        assert!(matches!(err, MemoryPressureError::UnrecognizedOutput(_)));
    }

    // ---------- vm_stat parsing ----------

    /// Fixture with ~50% of pages "available"; should classify as Normal.
    fn vm_stat_normal_fixture() -> String {
        "\
Mach Virtual Memory Statistics: (page size of 16384 bytes)\n\
Pages free:                               50000.\n\
Pages active:                             30000.\n\
Pages inactive:                           40000.\n\
Pages speculative:                         5000.\n\
Pages throttled:                              0.\n\
Pages wired down:                         15000.\n\
Pages purgeable:                           5000.\n\
Pages occupied by compressor:              5000.\n"
            .to_string()
    }

    /// Fixture with ~5% available; should classify as Critical.
    fn vm_stat_critical_fixture() -> String {
        "\
Mach Virtual Memory Statistics: (page size of 16384 bytes)\n\
Pages free:                                2000.\n\
Pages active:                             80000.\n\
Pages inactive:                            2000.\n\
Pages speculative:                          500.\n\
Pages throttled:                              0.\n\
Pages wired down:                         15000.\n\
Pages purgeable:                            500.\n\
Pages occupied by compressor:              5000.\n"
            .to_string()
    }

    /// Fixture with ~10% available; should classify as Warn.
    fn vm_stat_warn_fixture() -> String {
        "\
Mach Virtual Memory Statistics: (page size of 16384 bytes)\n\
Pages free:                                5000.\n\
Pages active:                             75000.\n\
Pages inactive:                            4000.\n\
Pages speculative:                          500.\n\
Pages throttled:                              0.\n\
Pages wired down:                         15000.\n\
Pages purgeable:                            500.\n\
Pages occupied by compressor:              5000.\n"
            .to_string()
    }

    #[test]
    fn test_parse_vm_stat_output_mostly_free_is_normal() {
        assert_eq!(
            parse_vm_stat_output(&vm_stat_normal_fixture()).expect("normal fixture parses"),
            MemoryPressure::Normal
        );
    }

    #[test]
    fn test_parse_vm_stat_output_mid_pressure_is_warn() {
        assert_eq!(
            parse_vm_stat_output(&vm_stat_warn_fixture()).expect("warn fixture parses"),
            MemoryPressure::Warn
        );
    }

    #[test]
    fn test_parse_vm_stat_output_tight_is_critical() {
        assert_eq!(
            parse_vm_stat_output(&vm_stat_critical_fixture()).expect("critical fixture parses"),
            MemoryPressure::Critical
        );
    }

    #[test]
    fn test_parse_vm_stat_output_missing_header_returns_error() {
        let raw = "Pages free: 1.\nPages active: 1.\n";
        let err = parse_vm_stat_output(raw).expect_err("no header -> err");
        assert!(matches!(err, MemoryPressureError::UnrecognizedOutput(_)));
    }

    #[test]
    fn test_parse_vm_stat_output_missing_required_line_returns_error() {
        // Header present but `Pages free` is missing.
        let raw = "\
Mach Virtual Memory Statistics: (page size of 16384 bytes)\n\
Pages active:                             30000.\n\
Pages inactive:                           40000.\n\
Pages speculative:                         5000.\n\
Pages wired down:                         15000.\n\
Pages purgeable:                           5000.\n";
        let err = parse_vm_stat_output(raw).expect_err("missing free -> err");
        assert!(matches!(err, MemoryPressureError::UnrecognizedOutput(_)));
    }
}
