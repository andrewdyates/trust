// trust-router/certus_backend/unsafe_script.rs: Unsafe-code SMT script generation
//
// tRust #360: Generates SMT-LIB2 scripts for unsafe-code VCs with certus
// ownership annotations, separation logic axioms, and provenance tracking.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt::Write;

use trust_types::*;

use crate::smtlib_backend::generate_smtlib_script;

use super::unsafe_classify::{classify_unsafe_vc, UnsafeVcClass};

/// tRust #360: Generate an SMT-LIB2 script for unsafe-code VCs with certus
/// ownership annotations.
///
/// Extends the standard ownership script with:
/// - `(set-option :unsafe-mode true)` — enables certus's unsafe-code reasoning
/// - Separation logic axioms for heap/pointer safety
/// - Provenance tracking annotations for raw pointer origins
/// - Classification comment so certus can select proof strategies
pub(crate) fn generate_unsafe_ownership_script(vc: &VerificationCondition) -> String {
    let base_script = generate_smtlib_script(&vc.formula);
    let unsafe_class = classify_unsafe_vc(vc);

    let mut script = String::with_capacity(base_script.len() + 512);

    // -- Certus header with unsafe-mode enabled --
    script.push_str("; certus ownership-aware verification (unsafe code)\n");
    script.push_str("(set-option :ownership-mode true)\n");
    script.push_str("(set-option :borrow-check true)\n");
    script.push_str("(set-option :unsafe-mode true)\n");
    script.push_str("(set-option :provenance-tracking true)\n");

    // Classification annotation
    if let Some(class) = unsafe_class {
        let _ = writeln!(script, "; certus unsafe class: {}", class.label());
    }

    // VC kind annotation
    let kind_annotation = match &vc.kind {
        VcKind::UnsafeOperation { desc } => {
            format!("; certus VC kind: unsafe operation: {desc}")
        }
        VcKind::Assertion { message } => {
            format!("; certus VC kind: {message}")
        }
        other => format!("; certus VC kind: {}", other.description()),
    };
    script.push_str(&kind_annotation);
    script.push('\n');

    // -- Class-specific axioms --
    if let Some(class) = unsafe_class {
        match class {
            UnsafeVcClass::RawDeref | UnsafeVcClass::RawWrite => {
                script.push_str("\n; === Raw pointer safety axioms ===\n");
                // Null pointer is never a valid address
                script.push_str("(assert (= null_ptr 0))\n");
                // Unallocated sentinel value
                script.push_str("(assert (= unalloc_sentinel (- 1)))\n");
                if class == UnsafeVcClass::RawWrite {
                    // Write requires mutable access
                    script.push_str("; Write permission required for raw pointer write\n");
                    script.push_str("(assert (=> writing_through_ptr (= ptr_perm 2)))\n");
                }
            }
            UnsafeVcClass::Transmute => {
                script.push_str("\n; === Transmute safety axioms ===\n");
                // Layout compatibility is the primary safety condition
                script.push_str("; size_of(Src) == size_of(Dst) required\n");
                script.push_str("; alignment(Dst) <= alignment(Src) required\n");
            }
            UnsafeVcClass::FfiCall => {
                script.push_str("\n; === FFI safety axioms ===\n");
                // FFI calls have arbitrary side effects on the heap
                script.push_str("; Pointer arguments must be non-null\n");
                script.push_str("; Heap state is invalidated after FFI call\n");
            }
            UnsafeVcClass::SepFrame => {
                script.push_str("\n; === Separation logic frame rule ===\n");
                // Frame addresses must be disjoint from operation footprint
                script.push_str("; Frame preservation: footprint disjoint from frame\n");
            }
            UnsafeVcClass::UseAfterFree => {
                script.push_str("\n; === Use-after-free detection ===\n");
                // Freed allocations cannot be accessed
                script.push_str("; Accessing freed memory is undefined behavior\n");
            }
            UnsafeVcClass::PermissionDenied => {
                script.push_str("\n; === Permission violation detection ===\n");
                // Read-only pointer cannot be written through
                script.push_str("; Pointer permission level must allow the access\n");
            }
            UnsafeVcClass::SepHeapCondition | UnsafeVcClass::GenericUnsafe => {
                // No additional axioms needed; the base formula encodes the check.
            }
        }
    }

    // -- Base script (declarations + assertions + check-sat) --
    script.push_str("\n; === Base verification condition ===\n");
    script.push_str(&base_script);

    script
}
