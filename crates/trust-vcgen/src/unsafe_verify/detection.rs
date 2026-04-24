// trust-vcgen/unsafe_verify/detection.rs: Unsafe block detection and safety comment parsing
//
// Detects unsafe blocks in MIR, extracts // SAFETY: comments from source spans,
// parses structured safety claims, and generates Assertion VCs that encode the
// claimed invariants.
//
// Part of #79, #137: Unsafe code verification
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use super::{SafetyClaim, UnsafeBlock};

/// Detect unsafe blocks in a verifiable function.
///
/// In MIR, unsafe blocks manifest as Call terminators to functions that require
/// unsafe (e.g., `ptr::read`, `ptr::write`, `slice::from_raw_parts`), or
/// as blocks containing raw pointer dereferences (Deref projections on raw ptrs).
///
/// We also detect explicit unsafe annotations via the function's contracts
/// and trust annotations.
#[must_use]
pub fn detect_unsafe_blocks(func: &VerifiableFunction) -> Vec<UnsafeBlock> {
    let mut blocks = Vec::new();

    for block in &func.body.blocks {
        // Check for unsafe call patterns in the terminator
        if let Terminator::Call { func: callee, span, .. } = &block.terminator
            && is_unsafe_fn_call(callee)
        {
            blocks.push(UnsafeBlock {
                span: span.clone(),
                safety_comment: None,
                safety_claim: None,
                block_id: block.id,
            });
        }

        // Check for raw pointer dereferences in statements
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, span, .. } = stmt
                && has_raw_deref(func, rvalue)
            {
                blocks.push(UnsafeBlock {
                    span: span.clone(),
                    safety_comment: None,
                    safety_claim: None,
                    block_id: block.id,
                });
            }
        }
    }

    blocks
}

/// Attach safety comments to detected unsafe blocks.
///
/// In a full compiler integration, comments would come from the source map.
/// This function accepts pre-extracted comment text and matches them to blocks
/// by source span proximity.
pub fn attach_safety_comments(blocks: &mut [UnsafeBlock], comments: &[(SourceSpan, String)]) {
    for block in blocks.iter_mut() {
        // Find the closest preceding SAFETY comment
        for (comment_span, text) in comments {
            if comment_span.file == block.span.file
                && comment_span.line_end <= block.span.line_start
                && block.span.line_start - comment_span.line_end <= 2
                && text.contains("SAFETY:")
            {
                block.safety_comment = Some(text.clone());
                block.safety_claim = Some(parse_safety_comment(text));
            }
        }
    }
}

/// Parse a `// SAFETY:` comment into a structured safety claim.
///
/// Expected format:
/// ```text
/// // SAFETY: <invariant>
/// // <justification>
/// ```
///
/// Or single-line:
/// ```text
/// // SAFETY: <invariant> because <justification>
/// ```
///
/// If only the invariant line is present, justification defaults to
/// "no justification provided".
#[must_use]
pub fn parse_safety_comment(comment: &str) -> SafetyClaim {
    // Strip comment markers and find the SAFETY: prefix
    let lines: Vec<&str> = comment
        .lines()
        .map(|line| line.trim().trim_start_matches("//").trim())
        .filter(|line| !line.is_empty())
        .collect();

    if lines.is_empty() {
        return SafetyClaim {
            invariant: String::new(),
            justification: "no justification provided".to_string(),
        };
    }

    // Find the line with SAFETY:
    let safety_idx =
        lines.iter().position(|line| line.starts_with("SAFETY:") || line.starts_with("SAFETY :"));

    let safety_line = match safety_idx {
        Some(idx) => lines[idx],
        None => {
            // No SAFETY: prefix found, treat entire comment as invariant
            return SafetyClaim {
                invariant: lines.join(" "),
                justification: "no justification provided".to_string(),
            };
        }
    };

    // Extract the invariant (text after "SAFETY:")
    let after_safety =
        safety_line.trim_start_matches("SAFETY:").trim_start_matches("SAFETY :").trim();

    // Check for "because" separator in single-line format
    if let Some(because_idx) = after_safety.to_lowercase().find(" because ") {
        let invariant = after_safety[..because_idx].trim().to_string();
        let justification = after_safety[because_idx + 9..].trim().to_string();
        return SafetyClaim { invariant, justification };
    }

    let invariant = after_safety.to_string();

    // Justification is the remaining lines after the SAFETY: line
    let justification_lines: Vec<&str> = match safety_idx {
        Some(idx) => lines[idx + 1..].to_vec(),
        None => vec![],
    };

    let justification = if justification_lines.is_empty() {
        "no justification provided".to_string()
    } else {
        justification_lines.join(" ")
    };

    SafetyClaim { invariant, justification }
}

/// Generate verification conditions for unsafe blocks.
///
/// For each unsafe block with a parsed safety claim, we generate an Assertion
/// VC encoding the invariant. Unsafe blocks without safety comments get a
/// "missing SAFETY comment" assertion that is trivially satisfiable (always
/// a finding).
///
/// The convention is: Assertion VCs with `message` prefixed by `[unsafe]`
/// are from unsafe verification. This lets reporters distinguish them.
pub fn generate_safety_vcs(
    func: &VerifiableFunction,
    blocks: &[UnsafeBlock],
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for block in blocks {
        match &block.safety_claim {
            Some(claim) if !claim.invariant.is_empty() => {
                // Generate a conservative VC for the claimed invariant.
                //
                // SOUNDNESS FIX (#165): The old code used an unconstrained
                // boolean variable `safety_invariant_N` wrapped in Not().
                // The solver could set it to true, making Not(true) = UNSAT,
                // which vacuously "proved" every safety claim without checking
                // anything. We now use Formula::Bool(true) as the violation
                // formula — always SAT — meaning this VC conservatively
                // reports "cannot mechanically verify this claim" unless
                // downstream analysis constrains it further.
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe] SAFETY claim (unverified): {}",
                            claim.invariant,
                        ),
                    },
                    function: func.name.as_str().into(),
                    location: block.span.clone(),
                    // Always SAT = conservatively "cannot verify".
                    // A downstream pass with actual program constraints can
                    // strengthen this into a real check.
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                });

                // If the justification references nullability, generate
                // a non-null check VC.
                if claim.invariant.to_lowercase().contains("non-null")
                    || claim.invariant.to_lowercase().contains("not null")
                    || claim.invariant.to_lowercase().contains("nonnull")
                {
                    vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!(
                                "[unsafe] null pointer check for: {}",
                                claim.invariant,
                            ),
                        },
                        function: func.name.as_str().into(),
                        location: block.span.clone(),
                        formula: Formula::Eq(
                            Box::new(Formula::Var(format!("ptr_{}", block.block_id.0), Sort::Int)),
                            Box::new(Formula::Int(0)),
                        ),
                        contract_metadata: None,
                    });
                }

                // If the justification references alignment, generate
                // an alignment check VC.
                if claim.invariant.to_lowercase().contains("align") {
                    vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!(
                                "[unsafe] alignment check (unverified) for: {}",
                                claim.invariant,
                            ),
                        },
                        function: func.name.as_str().into(),
                        location: block.span.clone(),
                        formula: Formula::Bool(true),
                        contract_metadata: None,
                    });
                }
            }
            _ => {
                // No safety claim: generate a "missing comment" assertion.
                // This is always SAT (Bool(true)) = always a finding.
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: "[unsafe] missing SAFETY comment on unsafe block".to_string(),
                    },
                    function: func.name.as_str().into(),
                    location: block.span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                });
            }
        }
    }

    vcs
}

/// Check whether a function call name refers to an inherently unsafe function.
pub(crate) fn is_unsafe_fn_call(callee: &str) -> bool {
    const UNSAFE_PATTERNS: &[&str] = &[
        // Core pointer operations
        "ptr::read",
        "ptr::write",
        "ptr::read_volatile",
        "ptr::write_volatile",
        "ptr::copy",
        "ptr::copy_nonoverlapping",
        "ptr::swap",
        "ptr::replace",
        "ptr::drop_in_place",
        "ptr::read_unaligned",
        "ptr::write_unaligned",
        // Slice from raw parts
        "slice::from_raw_parts",
        "slice::from_raw_parts_mut",
        // String from raw
        "str::from_utf8_unchecked",
        "String::from_raw_parts",
        // Transmute
        "mem::transmute",
        "mem::transmute_copy",
        "mem::zeroed",
        "mem::uninitialized",
        // Alloc
        "alloc::alloc",
        "alloc::dealloc",
        "alloc::realloc",
        // Intrinsics
        "intrinsics::",
        // FFI / extern calls (heuristic: contains "extern" or "ffi")
        "::ffi::",
    ];

    let lower = callee.to_lowercase();
    UNSAFE_PATTERNS.iter().any(|p| lower.contains(&p.to_lowercase()))
}

/// Check whether an rvalue contains a raw pointer dereference.
pub(crate) fn has_raw_deref(func: &VerifiableFunction, rvalue: &Rvalue) -> bool {
    match rvalue {
        Rvalue::Use(operand) => crate::operand_has_raw_deref(func, operand),
        Rvalue::Ref { place, .. } | Rvalue::CopyForDeref(place) => {
            crate::place_has_raw_deref(func, place)
        }
        _ => false,
    }
}
