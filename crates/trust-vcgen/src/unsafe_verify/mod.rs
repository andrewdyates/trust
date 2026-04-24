// trust-vcgen/unsafe_verify: Unsafe code verification with SAFETY comment extraction
//
// Detects unsafe blocks in MIR, extracts // SAFETY: comments from source spans,
// parses structured safety claims, and generates Assertion VCs that encode the
// claimed invariants. This lets the solver check whether the safety justification
// is consistent with the surrounding code.
//
// Extended in #137 with:
// - UnsafeVcKind enum for typed unsafe VC categorization
// - UnsafeVerifier struct for stateful VC generation across a function
// - Memory safety VCs: pointer alignment, provenance, bounds checking
// - Transmute VCs: layout compatibility, validity invariant preservation
// - FFI VCs: pre/post conditions on extern calls, null pointer checks
//
// Part of #79, #137: Unsafe code verification
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::*;

pub(crate) mod detection;
#[cfg(test)]
mod tests;
pub(crate) mod verifier;

// Re-export public API for external consumers.
pub use detection::{attach_safety_comments, detect_unsafe_blocks, generate_safety_vcs};

// ────────────────────────────────────────────────────────────────────────────
// Core types
// ────────────────────────────────────────────────────────────────────────────

/// An unsafe block discovered in MIR, with its optional safety claim.
#[derive(Debug, Clone)]
pub struct UnsafeBlock {
    /// Source location of the unsafe block.
    pub span: SourceSpan,
    /// The raw `// SAFETY:` comment text, if found.
    pub safety_comment: Option<String>,
    /// Parsed safety claim, if the comment was successfully parsed.
    pub safety_claim: Option<SafetyClaim>,
    /// The block index in MIR where the unsafe code lives.
    pub block_id: BlockId,
}

/// A structured safety claim extracted from a `// SAFETY:` comment.
///
/// Convention: Rust's `// SAFETY:` comments should state:
/// 1. The invariant that makes this unsafe code sound.
/// 2. The justification for why that invariant holds at this call site.
///
/// We parse these into structured form so the solver can attempt to verify
/// the claimed invariant against the surrounding code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafetyClaim {
    /// The invariant being claimed (e.g., "pointer is non-null and aligned").
    pub invariant: String,
    /// The justification for why the invariant holds (e.g., "checked above on line 42").
    pub justification: String,
}

// ────────────────────────────────────────────────────────────────────────────
// New types (#137): UnsafeVcKind, UnsafeVc
// ────────────────────────────────────────────────────────────────────────────

/// Categorized kinds of unsafe verification conditions.
///
/// Each variant corresponds to a specific unsafe operation that requires
/// verification. This is orthogonal to `VcKind` (which is solver-facing);
/// `UnsafeVcKind` captures the *reason* the VC was generated from an unsafe
/// context so reporters and audit tools can provide targeted guidance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
#[allow(dead_code)]
pub enum UnsafeVcKind {
    /// Raw pointer dereference: pointer must be non-null, aligned, and point
    /// to a valid allocation with sufficient size.
    RawPointerDeref {
        /// Human-readable pointer expression (e.g., "`*ptr`").
        pointer_expr: String,
    },
    /// `mem::transmute` or `mem::transmute_copy`: source and target layouts
    /// must be compatible, and the bit pattern must satisfy the target type's
    /// validity invariant.
    Transmute { from_ty: String, to_ty: String },
    /// Union field access: reading a union field reinterprets the bits, so
    /// the active variant must match the accessed field.
    UnionAccess { union_name: String, field_name: String },
    /// FFI call: extern function has no Rust-side safety guarantees. Pre/post
    /// conditions must be stated and verified.
    FfiCall { callee: String },
    /// Inline assembly: opaque to the compiler, safety cannot be inferred.
    InlineAsm {
        /// A diagnostic label for the asm block.
        label: String,
    },
    /// Access to a mutable static variable: data races and aliasing are
    /// the caller's responsibility.
    MutableStaticAccess { static_name: String },
}

impl UnsafeVcKind {
    /// Human-readable description for reports.
    #[must_use]
    #[allow(dead_code)]
    pub fn description(&self) -> String {
        match self {
            Self::RawPointerDeref { pointer_expr } => {
                format!("raw pointer dereference: {pointer_expr}")
            }
            Self::Transmute { from_ty, to_ty } => {
                format!("transmute from {from_ty} to {to_ty}")
            }
            Self::UnionAccess { union_name, field_name } => {
                format!("union field access: {union_name}.{field_name}")
            }
            Self::FfiCall { callee } => {
                format!("FFI call to {callee}")
            }
            Self::InlineAsm { label } => {
                format!("inline assembly: {label}")
            }
            Self::MutableStaticAccess { static_name } => {
                format!("mutable static access: {static_name}")
            }
        }
    }
}

/// A tagged unsafe verification condition, pairing the solver-facing VC with
/// the unsafe-specific categorization.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct UnsafeVc {
    /// The solver-facing verification condition.
    pub vc: VerificationCondition,
    /// The categorized unsafe operation that produced this VC.
    pub unsafe_kind: UnsafeVcKind,
}

// ────────────────────────────────────────────────────────────────────────────
// Entry point
// ────────────────────────────────────────────────────────────────────────────

/// Top-level entry point: check a function for unsafe code and generate VCs.
///
/// Called from `generate_vcs` in lib.rs. Detects unsafe blocks, attaches
/// safety comments (when available), and generates assertion VCs.
pub(crate) fn check_unsafe(
    func: &VerifiableFunction,
    comments: &[(SourceSpan, String)],
    vcs: &mut Vec<VerificationCondition>,
) {
    let mut blocks = detect_unsafe_blocks(func);
    if blocks.is_empty() {
        return;
    }

    attach_safety_comments(&mut blocks, comments);
    let safety_vcs = generate_safety_vcs(func, &blocks);
    vcs.extend(safety_vcs);
}
