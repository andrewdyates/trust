// trust-driver/parser.rs: Parse tRust verification output from rustc stderr
//
// Parses lines matching the format:
//   note: tRust [TAG]: description -- PROVED/FAILED (backend, Nms)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{BinOp, ProofStrength, Ty, VcKind, VerificationResult};

/// A single parsed verification condition from compiler output.
#[derive(Debug, Clone)]
pub(crate) struct ParsedVc {
    /// The kind of VC that was checked.
    pub vc_kind: VcKind,
    /// Whether the VC was proved or failed.
    pub result: VerificationResult,
    /// Description text from the diagnostic (e.g., "`a + b` may overflow").
    pub description: String,
}

/// Parse tRust verification output from rustc stderr.
///
/// Extracts lines matching the pattern:
///   `note: tRust [TAG]: description -- PROVED/FAILED (backend, Nms)`
///
/// Lines that don't match the pattern are silently skipped.
pub(crate) fn parse_trust_output(stderr: &str) -> Vec<ParsedVc> {
    stderr.lines().filter_map(parse_line).collect()
}

/// Parse a single line of compiler output.
///
/// Expected format:
///   `note: tRust [TAG]: description -- PROVED (backend, 8ms)`
///   `note: tRust [TAG]: description -- FAILED (backend, 12ms)`
fn parse_line(line: &str) -> Option<ParsedVc> {
    // Find "tRust [" prefix after "note:"
    let trust_idx = line.find("tRust [")?;
    let after_trust = &line[trust_idx + 7..]; // skip "tRust ["

    // Extract tag between [ and ]
    let close_bracket = after_trust.find(']')?;
    let tag = &after_trust[..close_bracket];

    // Skip "]: " to get description
    let after_tag = after_trust.get(close_bracket + 2..)?; // skip "]:"
    let after_tag = after_tag.strip_prefix(' ').unwrap_or(after_tag);

    // Split on " \u{2014} " (em-dash) or " -- " to separate description from result
    let (description, result_part) = split_on_separator(after_tag)?;

    // Parse "PROVED (z4, 8ms)" or "FAILED (z4, 12ms)"
    let result = parse_result(result_part)?;

    let vc_kind = tag_to_vc_kind(tag)?;

    Some(ParsedVc {
        vc_kind,
        result,
        description: description.to_string(),
    })
}

/// Split on either em-dash or double-dash separator.
fn split_on_separator(s: &str) -> Option<(&str, &str)> {
    // Try em-dash first (Unicode \u{2014}, often rendered as "—")
    if let Some(idx) = s.find(" \u{2014} ") {
        return Some((&s[..idx], &s[idx + 4..]));
    }
    // Fall back to " -- "
    if let Some(idx) = s.find(" -- ") {
        return Some((&s[..idx], &s[idx + 4..]));
    }
    None
}

/// Parse "PROVED (z4, 8ms)" or "FAILED (z4, 12ms)" into VerificationResult.
fn parse_result(s: &str) -> Option<VerificationResult> {
    let s = s.trim();
    let (status, rest) = if let Some(rest) = s.strip_prefix("PROVED") {
        ("proved", rest)
    } else if let Some(rest) = s.strip_prefix("FAILED") {
        ("failed", rest)
    } else if let Some(rest) = s.strip_prefix("UNKNOWN") {
        ("unknown", rest)
    } else if let Some(rest) = s.strip_prefix("TIMEOUT") {
        ("timeout", rest)
    } else {
        return None;
    };

    // Parse "(backend, Nms)" - optional parenthesized details
    let (solver, time_ms) = parse_parenthesized_details(rest.trim());

    match status {
        "proved" => Some(VerificationResult::Proved {
            solver,
            time_ms,
            strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }),
        "failed" => Some(VerificationResult::Failed {
            solver,
            time_ms,
            counterexample: None,
        }),
        "unknown" => Some(VerificationResult::Unknown {
            solver,
            time_ms,
            reason: String::new(),
        }),
        "timeout" => Some(VerificationResult::Timeout {
            solver,
            timeout_ms: time_ms,
        }),
        _ => None,
    }
}

/// Parse "(z4, 8ms)" returning (solver_name, time_in_ms).
fn parse_parenthesized_details(s: &str) -> (String, u64) {
    let default = ("unknown".to_string(), 0);

    let s = s.trim();
    let inner = match s.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
        Some(inner) => inner,
        None => return default,
    };

    let parts: Vec<&str> = inner.splitn(2, ',').collect();
    if parts.len() != 2 {
        return default;
    }

    let solver = parts[0].trim().to_string();
    let time_str = parts[1].trim();

    // Parse "8ms" -> 8
    let time_ms = time_str
        .strip_suffix("ms")
        .and_then(|n| n.trim().parse::<u64>().ok())
        .unwrap_or(0);

    (solver, time_ms)
}

/// Map a tag string to the corresponding VcKind.
///
/// Tags from compiler output:
///   overflow:add, overflow:sub, overflow:mul, div:zero, rem:zero,
///   bounds, assert, cast, neg, shift, unreachable
fn tag_to_vc_kind(tag: &str) -> Option<VcKind> {
    // Default type for overflow operations: i32 (most common in Rust)
    let default_ty = || Ty::Int {
        width: 32,
        signed: true,
    };
    let default_tys = || (default_ty(), default_ty());

    match tag {
        "overflow:add" => Some(VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: default_tys(),
        }),
        "overflow:sub" => Some(VcKind::ArithmeticOverflow {
            op: BinOp::Sub,
            operand_tys: default_tys(),
        }),
        "overflow:mul" => Some(VcKind::ArithmeticOverflow {
            op: BinOp::Mul,
            operand_tys: default_tys(),
        }),
        "div:zero" => Some(VcKind::DivisionByZero),
        "rem:zero" => Some(VcKind::RemainderByZero),
        "bounds" => Some(VcKind::IndexOutOfBounds),
        "assert" => Some(VcKind::Assertion {
            message: String::new(),
        }),
        "cast" => Some(VcKind::CastOverflow {
            from_ty: default_ty(),
            to_ty: default_ty(),
        }),
        "neg" => Some(VcKind::NegationOverflow { ty: default_ty() }),
        "shift" => Some(VcKind::ShiftOverflow {
            op: BinOp::Shl,
            operand_ty: default_ty(),
            shift_ty: Ty::Int { width: 32, signed: false },
        }),
        "unreachable" => Some(VcKind::Unreachable),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- parse_trust_output tests --

    #[test]
    fn test_parse_single_proved_line() {
        let stderr = "note: tRust [overflow:add]: `a + b` may overflow \u{2014} PROVED (z4, 8ms)\n";
        let results = parse_trust_output(stderr);
        assert_eq!(results.len(), 1);

        let vc = &results[0];
        assert!(matches!(vc.vc_kind, VcKind::ArithmeticOverflow { ref op, .. } if matches!(op, BinOp::Add)));
        assert!(vc.result.is_proved());
        assert_eq!(vc.result.solver_name(), "z4");
        assert_eq!(vc.result.time_ms(), 8);
        assert_eq!(vc.description, "`a + b` may overflow");
    }

    #[test]
    fn test_parse_multiple_lines() {
        let stderr = "\
note: tRust [overflow:add]: `a + b` may overflow \u{2014} PROVED (z4, 8ms)
note: tRust [overflow:sub]: `mid - low` may underflow \u{2014} PROVED (z4, 3ms)
note: tRust [div:zero]: division by zero check \u{2014} PROVED (z4, 1ms)
";
        let results = parse_trust_output(stderr);
        assert_eq!(results.len(), 3);

        // First: overflow:add
        assert!(matches!(
            results[0].vc_kind,
            VcKind::ArithmeticOverflow { ref op, .. } if matches!(op, BinOp::Add)
        ));
        assert!(results[0].result.is_proved());

        // Second: overflow:sub
        assert!(matches!(
            results[1].vc_kind,
            VcKind::ArithmeticOverflow { ref op, .. } if matches!(op, BinOp::Sub)
        ));
        assert_eq!(results[1].result.time_ms(), 3);

        // Third: div:zero
        assert!(matches!(results[2].vc_kind, VcKind::DivisionByZero));
        assert_eq!(results[2].result.time_ms(), 1);
    }

    #[test]
    fn test_parse_failed_result() {
        let stderr = "note: tRust [bounds]: array index out of bounds \u{2014} FAILED (z4, 15ms)\n";
        let results = parse_trust_output(stderr);
        assert_eq!(results.len(), 1);

        let vc = &results[0];
        assert!(matches!(vc.vc_kind, VcKind::IndexOutOfBounds));
        assert!(vc.result.is_failed());
        assert_eq!(vc.result.solver_name(), "z4");
        assert_eq!(vc.result.time_ms(), 15);
    }

    #[test]
    fn test_parse_double_dash_separator() {
        let stderr = "note: tRust [overflow:mul]: multiply overflow -- PROVED (z4, 5ms)\n";
        let results = parse_trust_output(stderr);
        assert_eq!(results.len(), 1);
        assert!(results[0].result.is_proved());
        assert_eq!(results[0].description, "multiply overflow");
    }

    #[test]
    fn test_parse_skips_non_trust_lines() {
        let stderr = "\
warning: unused variable `x`
note: tRust [assert]: assertion check \u{2014} PROVED (z4, 2ms)
error[E0308]: mismatched types
note: some other note
";
        let results = parse_trust_output(stderr);
        assert_eq!(results.len(), 1);
        assert!(matches!(results[0].vc_kind, VcKind::Assertion { .. }));
    }

    #[test]
    fn test_parse_empty_input() {
        let results = parse_trust_output("");
        assert!(results.is_empty());
    }

    #[test]
    fn test_parse_no_matching_lines() {
        let stderr = "warning: unused import\nerror: aborting due to previous error\n";
        let results = parse_trust_output(stderr);
        assert!(results.is_empty());
    }

    // -- tag_to_vc_kind tests --

    #[test]
    fn test_tag_overflow_add() {
        let kind = tag_to_vc_kind("overflow:add").unwrap();
        assert!(matches!(
            kind,
            VcKind::ArithmeticOverflow { ref op, .. } if matches!(op, BinOp::Add)
        ));
    }

    #[test]
    fn test_tag_overflow_sub() {
        let kind = tag_to_vc_kind("overflow:sub").unwrap();
        assert!(matches!(
            kind,
            VcKind::ArithmeticOverflow { ref op, .. } if matches!(op, BinOp::Sub)
        ));
    }

    #[test]
    fn test_tag_overflow_mul() {
        let kind = tag_to_vc_kind("overflow:mul").unwrap();
        assert!(matches!(
            kind,
            VcKind::ArithmeticOverflow { ref op, .. } if matches!(op, BinOp::Mul)
        ));
    }

    #[test]
    fn test_tag_div_zero() {
        assert!(matches!(tag_to_vc_kind("div:zero"), Some(VcKind::DivisionByZero)));
    }

    #[test]
    fn test_tag_rem_zero() {
        assert!(matches!(tag_to_vc_kind("rem:zero"), Some(VcKind::RemainderByZero)));
    }

    #[test]
    fn test_tag_bounds() {
        assert!(matches!(tag_to_vc_kind("bounds"), Some(VcKind::IndexOutOfBounds)));
    }

    #[test]
    fn test_tag_assert() {
        assert!(matches!(tag_to_vc_kind("assert"), Some(VcKind::Assertion { .. })));
    }

    #[test]
    fn test_tag_cast() {
        assert!(matches!(tag_to_vc_kind("cast"), Some(VcKind::CastOverflow { .. })));
    }

    #[test]
    fn test_tag_neg() {
        assert!(matches!(tag_to_vc_kind("neg"), Some(VcKind::NegationOverflow { .. })));
    }

    #[test]
    fn test_tag_shift() {
        assert!(matches!(tag_to_vc_kind("shift"), Some(VcKind::ShiftOverflow { .. })));
    }

    #[test]
    fn test_tag_unreachable() {
        assert!(matches!(tag_to_vc_kind("unreachable"), Some(VcKind::Unreachable)));
    }

    #[test]
    fn test_tag_unknown_returns_none() {
        assert!(tag_to_vc_kind("nonexistent").is_none());
    }

    // -- parse_result tests --

    #[test]
    fn test_parse_result_proved() {
        let result = parse_result("PROVED (z4, 8ms)").unwrap();
        assert!(result.is_proved());
        assert_eq!(result.solver_name(), "z4");
        assert_eq!(result.time_ms(), 8);
    }

    #[test]
    fn test_parse_result_failed() {
        let result = parse_result("FAILED (zani, 120ms)").unwrap();
        assert!(result.is_failed());
        assert_eq!(result.solver_name(), "zani");
        assert_eq!(result.time_ms(), 120);
    }

    #[test]
    fn test_parse_result_unknown() {
        let result = parse_result("UNKNOWN (sunder, 50ms)").unwrap();
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_parse_result_timeout() {
        let result = parse_result("TIMEOUT (z4, 30000ms)").unwrap();
        assert!(matches!(result, VerificationResult::Timeout { timeout_ms: 30000, .. }));
    }

    #[test]
    fn test_parse_result_invalid() {
        assert!(parse_result("INVALID (z4, 8ms)").is_none());
    }

    // -- parse_parenthesized_details tests --

    #[test]
    fn test_parse_details_normal() {
        let (solver, time) = parse_parenthesized_details("(z4, 8ms)");
        assert_eq!(solver, "z4");
        assert_eq!(time, 8);
    }

    #[test]
    fn test_parse_details_large_time() {
        let (solver, time) = parse_parenthesized_details("(lean5, 12345ms)");
        assert_eq!(solver, "lean5");
        assert_eq!(time, 12345);
    }

    #[test]
    fn test_parse_details_missing_parens() {
        let (solver, time) = parse_parenthesized_details("z4, 8ms");
        assert_eq!(solver, "unknown");
        assert_eq!(time, 0);
    }

    // -- Integration-style test with realistic output --

    #[test]
    fn test_parse_realistic_midpoint_output() {
        // Matches the real midpoint.rs golden test output
        let stderr = "\
warning: unused variable `x`
 --> midpoint.rs:1:5
note: tRust [overflow:add]: `a + b` may overflow \u{2014} PROVED (z4, 8ms)
note: tRust [overflow:sub]: `mid - low` may underflow \u{2014} PROVED (z4, 3ms)
note: tRust [div:zero]: division by zero check \u{2014} PROVED (z4, 1ms)
error: aborting due to 1 previous error
";
        let results = parse_trust_output(stderr);
        assert_eq!(results.len(), 3);

        // All proved
        assert!(results.iter().all(|vc| vc.result.is_proved()));

        // All by z4
        assert!(results.iter().all(|vc| vc.result.solver_name() == "z4"));

        // Correct kinds
        assert!(matches!(
            results[0].vc_kind,
            VcKind::ArithmeticOverflow { ref op, .. } if matches!(op, BinOp::Add)
        ));
        assert!(matches!(
            results[1].vc_kind,
            VcKind::ArithmeticOverflow { ref op, .. } if matches!(op, BinOp::Sub)
        ));
        assert!(matches!(results[2].vc_kind, VcKind::DivisionByZero));

        // Time values
        assert_eq!(results[0].result.time_ms(), 8);
        assert_eq!(results[1].result.time_ms(), 3);
        assert_eq!(results[2].result.time_ms(), 1);
    }

    #[test]
    fn test_parse_mixed_proved_and_failed() {
        let stderr = "\
note: tRust [overflow:add]: `x + y` may overflow \u{2014} PROVED (z4, 5ms)
note: tRust [bounds]: array access `arr[i]` \u{2014} FAILED (z4, 12ms)
note: tRust [assert]: user assertion \u{2014} PROVED (z4, 2ms)
";
        let results = parse_trust_output(stderr);
        assert_eq!(results.len(), 3);
        assert!(results[0].result.is_proved());
        assert!(results[1].result.is_failed());
        assert!(results[2].result.is_proved());
    }

    #[test]
    fn test_parse_summary_counts() {
        let stderr = "\
note: tRust [overflow:add]: check 1 \u{2014} PROVED (z4, 1ms)
note: tRust [overflow:sub]: check 2 \u{2014} PROVED (z4, 2ms)
note: tRust [div:zero]: check 3 \u{2014} FAILED (z4, 3ms)
note: tRust [bounds]: check 4 \u{2014} PROVED (z4, 4ms)
note: tRust [neg]: check 5 \u{2014} FAILED (z4, 5ms)
";
        let results = parse_trust_output(stderr);
        assert_eq!(results.len(), 5);

        let proved = results.iter().filter(|vc| vc.result.is_proved()).count();
        let failed = results.iter().filter(|vc| vc.result.is_failed()).count();
        assert_eq!(proved, 3);
        assert_eq!(failed, 2);
    }
}
