// trust-testgen/mutation/source_mutation.rs: Source-level mutation generation
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::types::{Mutant, MutationType};
use crate::GeneratedTest;

// ---------------------------------------------------------------------------
// Source-level mutation (original API)
// ---------------------------------------------------------------------------

/// Generate mutants from source code.
///
/// Scans the source for mutable patterns and produces a `Mutant` for each
/// possible single-point mutation.
#[must_use]
pub fn generate_mutants(source: &str) -> Vec<Mutant> {
    let mut mutants = Vec::new();

    for (line_idx, line) in source.lines().enumerate() {
        let line_num = line_idx + 1;
        let trimmed = line.trim();

        // Skip comments and empty lines
        if trimmed.starts_with("//") || trimmed.is_empty() {
            continue;
        }

        let base_offset = source.lines().take(line_idx).map(|l| l.len() + 1).sum::<usize>();

        // Arithmetic operator mutations
        generate_arith_mutants(&mut mutants, line, line_num, base_offset);

        // Comparison operator mutations
        generate_comp_mutants(&mut mutants, line, line_num, base_offset);

        // Boolean operator mutations
        generate_bool_mutants(&mut mutants, line, line_num, base_offset);

        // Boundary shift mutations (integer constants)
        generate_boundary_mutants(&mut mutants, line, line_num, base_offset);

        // Return value mutations
        generate_return_mutants(&mut mutants, trimmed, line_num, base_offset);

        // Condition negation mutations
        generate_condition_mutants(&mut mutants, trimmed, line_num, base_offset);
    }

    mutants
}

/// Generate arithmetic operator replacement mutants.
fn generate_arith_mutants(
    mutants: &mut Vec<Mutant>,
    line: &str,
    line_num: usize,
    base_offset: usize,
) {
    // Find ` + ` (with spaces to avoid false positives in comments/strings)
    for (i, _) in line.match_indices(" + ") {
        if !is_likely_in_string(line, i) {
            mutants.push(Mutant {
                offset: base_offset + i,
                line: line_num,
                mutation_type: MutationType::ArithOp,
                original: " + ".to_string(),
                mutated: " - ".to_string(),
            });
        }
    }
    for (i, _) in line.match_indices(" - ") {
        if !is_likely_in_string(line, i) {
            mutants.push(Mutant {
                offset: base_offset + i,
                line: line_num,
                mutation_type: MutationType::ArithOp,
                original: " - ".to_string(),
                mutated: " + ".to_string(),
            });
        }
    }
    for (i, _) in line.match_indices(" * ") {
        if !is_likely_in_string(line, i) {
            mutants.push(Mutant {
                offset: base_offset + i,
                line: line_num,
                mutation_type: MutationType::ArithOp,
                original: " * ".to_string(),
                mutated: " / ".to_string(),
            });
        }
    }
    for (i, _) in line.match_indices(" / ") {
        if !is_likely_in_string(line, i) && !line[i..].starts_with(" // ") {
            mutants.push(Mutant {
                offset: base_offset + i,
                line: line_num,
                mutation_type: MutationType::ArithOp,
                original: " / ".to_string(),
                mutated: " * ".to_string(),
            });
        }
    }
}

/// Generate comparison operator replacement mutants.
fn generate_comp_mutants(
    mutants: &mut Vec<Mutant>,
    line: &str,
    line_num: usize,
    base_offset: usize,
) {
    for (i, _) in line.match_indices(" >= ") {
        if !is_likely_in_string(line, i) {
            mutants.push(Mutant {
                offset: base_offset + i,
                line: line_num,
                mutation_type: MutationType::CompOp,
                original: " >= ".to_string(),
                mutated: " > ".to_string(),
            });
        }
    }
    for (i, _) in line.match_indices(" <= ") {
        if !is_likely_in_string(line, i) {
            mutants.push(Mutant {
                offset: base_offset + i,
                line: line_num,
                mutation_type: MutationType::CompOp,
                original: " <= ".to_string(),
                mutated: " < ".to_string(),
            });
        }
    }
    for (i, _) in line.match_indices(" == ") {
        if !is_likely_in_string(line, i) {
            mutants.push(Mutant {
                offset: base_offset + i,
                line: line_num,
                mutation_type: MutationType::CompOp,
                original: " == ".to_string(),
                mutated: " != ".to_string(),
            });
        }
    }
    for (i, _) in line.match_indices(" != ") {
        if !is_likely_in_string(line, i) {
            mutants.push(Mutant {
                offset: base_offset + i,
                line: line_num,
                mutation_type: MutationType::CompOp,
                original: " != ".to_string(),
                mutated: " == ".to_string(),
            });
        }
    }
}

/// Generate boolean operator replacement mutants.
fn generate_bool_mutants(
    mutants: &mut Vec<Mutant>,
    line: &str,
    line_num: usize,
    base_offset: usize,
) {
    for (i, _) in line.match_indices(" && ") {
        if !is_likely_in_string(line, i) {
            mutants.push(Mutant {
                offset: base_offset + i,
                line: line_num,
                mutation_type: MutationType::BoolOp,
                original: " && ".to_string(),
                mutated: " || ".to_string(),
            });
        }
    }
    for (i, _) in line.match_indices(" || ") {
        if !is_likely_in_string(line, i) {
            mutants.push(Mutant {
                offset: base_offset + i,
                line: line_num,
                mutation_type: MutationType::BoolOp,
                original: " || ".to_string(),
                mutated: " && ".to_string(),
            });
        }
    }
}

/// Generate boundary shift mutants for integer constants.
fn generate_boundary_mutants(
    mutants: &mut Vec<Mutant>,
    line: &str,
    line_num: usize,
    base_offset: usize,
) {
    let trimmed = line.trim();
    if trimmed.starts_with("//") {
        return;
    }

    let mut i = 0;
    let bytes = line.as_bytes();
    while i < bytes.len() {
        if bytes[i].is_ascii_digit()
            && (i == 0 || !bytes[i - 1].is_ascii_alphanumeric() && bytes[i - 1] != b'_')
        {
            let start = i;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            if i < bytes.len() && (bytes[i].is_ascii_alphabetic() || bytes[i] == b'_') {
                continue;
            }
            let num_str = &line[start..i];
            if let Ok(n) = num_str.parse::<i64>() {
                mutants.push(Mutant {
                    offset: base_offset + start,
                    line: line_num,
                    mutation_type: MutationType::BoundaryShift,
                    original: num_str.to_string(),
                    mutated: format!("{}", n + 1),
                });
                if n > 0 {
                    mutants.push(Mutant {
                        offset: base_offset + start,
                        line: line_num,
                        mutation_type: MutationType::BoundaryShift,
                        original: num_str.to_string(),
                        mutated: format!("{}", n - 1),
                    });
                }
            }
            continue;
        }
        i += 1;
    }
}

/// Generate return value replacement mutants.
fn generate_return_mutants(
    mutants: &mut Vec<Mutant>,
    trimmed: &str,
    line_num: usize,
    base_offset: usize,
) {
    if let Some(rest) = trimmed.strip_prefix("return ") {
        let rest = rest.trim_end_matches(';').trim();
        if rest != "0" && rest != "false" && !rest.is_empty() {
            mutants.push(Mutant {
                offset: base_offset,
                line: line_num,
                mutation_type: MutationType::ReturnValue,
                original: format!("return {rest}"),
                mutated: "return Default::default()".to_string(),
            });
        }
    }
}

/// Generate condition negation mutants.
fn generate_condition_mutants(
    mutants: &mut Vec<Mutant>,
    trimmed: &str,
    line_num: usize,
    base_offset: usize,
) {
    if let Some(rest) = trimmed.strip_prefix("if ")
        && let Some(brace_pos) = rest.find('{') {
            let condition = rest[..brace_pos].trim();
            if !condition.is_empty() {
                mutants.push(Mutant {
                    offset: base_offset,
                    line: line_num,
                    mutation_type: MutationType::ConditionNegation,
                    original: format!("if {condition}"),
                    mutated: format!("if !({condition})"),
                });
            }
        }
}

/// Rough heuristic: check if a position is likely inside a string literal.
pub(super) fn is_likely_in_string(line: &str, pos: usize) -> bool {
    let before = &line[..pos];
    let quote_count = before.chars().filter(|&c| c == '"').count();
    quote_count % 2 != 0
}

/// Calculate the mutation score using structural analysis.
///
/// A mutant is considered "killed" if at least one test structurally constrains
/// the mutated operation -- meaning the test contains an assertion that exercises
/// the operation being mutated (not just string containment of the operator).
///
/// Structural checks:
/// - For operator mutations (ArithOp, CompOp, BoolOp): the test must contain
///   an assertion (`assert`) that references the relevant operation AND uses
///   a concrete expected value or comparison (not just mentioning the operator).
/// - For BoundaryShift: the test must assert on a value near the mutated constant.
/// - For ReturnValue/ConditionNegation: the test must assert on the function's
///   output or control flow behavior.
///
/// Falls back to heuristic matching for cases where structural analysis is
/// not applicable.
#[must_use]
pub fn mutation_score(tests: &[GeneratedTest], mutants: &[Mutant]) -> f64 {
    if mutants.is_empty() {
        return 1.0;
    }

    let killed = mutants
        .iter()
        .filter(|m| test_structurally_kills_mutant(tests, m))
        .count();

    killed as f64 / mutants.len() as f64
}

/// Calculate the mutation score using the original heuristic (string containment).
///
/// A mutant is considered "killed" if at least one test contains a reference
/// to the mutated pattern. This is a weak heuristic -- use `mutation_score()`
/// for structural analysis.
#[must_use]
pub fn mutation_score_heuristic(tests: &[GeneratedTest], mutants: &[Mutant]) -> f64 {
    if mutants.is_empty() {
        return 1.0;
    }

    let killed = mutants
        .iter()
        .filter(|m| {
            tests.iter().any(|t| {
                t.code.contains(&m.original)
                    || t.boundary_values.iter().any(|v| v.contains(&m.original))
            })
        })
        .count();

    killed as f64 / mutants.len() as f64
}

/// Determine if a test suite structurally kills a mutant.
///
/// A test "structurally kills" a mutant when it has an assertion that constrains
/// the specific operation being mutated. This goes beyond string containment:
/// the test must demonstrate behavioral sensitivity to the mutation.
fn test_structurally_kills_mutant(tests: &[GeneratedTest], mutant: &Mutant) -> bool {
    tests.iter().any(|t| {
        let code = &t.code;
        match mutant.mutation_type {
            MutationType::ArithOp | MutationType::CompOp | MutationType::BoolOp => {
                // The test must:
                // 1. Reference the operation (contains the original operator)
                // 2. Have an assertion that constrains the result (assert with
                //    a concrete value or comparison, not just assert!(true))
                let has_operator_ref = code.contains(&mutant.original);
                let has_constraining_assert = has_value_constraining_assert(code, &mutant.original);
                has_operator_ref && has_constraining_assert
            }
            MutationType::BoundaryShift => {
                // The test must assert on a value related to the constant.
                // Check: test has an assertion AND references the original constant
                // value (or the mutated value -- if it checks the boundary).
                let has_original_ref = code.contains(&mutant.original);
                let has_assert = code.contains("assert");
                let has_boundary_value = t
                    .boundary_values
                    .iter()
                    .any(|v| v.contains(&mutant.original) || v.contains(&mutant.mutated));
                has_assert && (has_original_ref || has_boundary_value)
            }
            MutationType::ReturnValue | MutationType::ConditionNegation => {
                // The test must assert on the function's output or control flow.
                // A test that merely calls the function without checking the result
                // cannot kill a return-value or condition-negation mutant.
                let has_assert = code.contains("assert");
                let mentions_result = code.contains("result")
                    || code.contains("output")
                    || code.contains("ret")
                    || code.contains("==")
                    || code.contains("!=");
                has_assert && mentions_result
            }
        }
    })
}

/// Check if the test code has an assertion that constrains the value of an
/// expression involving the given operator.
///
/// A "value-constraining assertion" is an `assert*!()` call that compares the
/// result to a concrete expected value (e.g., `assert_eq!(result, 42)`) or
/// performs a relational check (e.g., `assert!(result > 0)`).
///
/// This rejects tests that merely mention the operator without actually
/// testing the output -- e.g., `let x = a + b;` without any assertion on `x`.
pub(super) fn has_value_constraining_assert(code: &str, _operator: &str) -> bool {
    // Look for assert patterns that constrain a value
    for line in code.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("//") {
            continue;
        }
        // assert_eq!/assert_ne! with a concrete value always constrains
        if trimmed.contains("assert_eq!") || trimmed.contains("assert_ne!") {
            return true;
        }
        // assert!() with a comparison operator constrains
        if trimmed.contains("assert!(") {
            // Check for relational operators inside the assert
            let after_assert = if let Some(pos) = trimmed.find("assert!(") {
                &trimmed[pos + 8..]
            } else {
                trimmed
            };
            if after_assert.contains("==")
                || after_assert.contains("!=")
                || after_assert.contains(">=")
                || after_assert.contains("<=")
                || after_assert.contains('>')
                || after_assert.contains('<')
            {
                return true;
            }
        }
    }
    false
}
