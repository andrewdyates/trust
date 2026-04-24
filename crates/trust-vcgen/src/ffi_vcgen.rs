// trust-vcgen/ffi_vcgen.rs: FFI call site VC generation (#460)
//
// Bridges FfiSummaryDb contracts into the verification pipeline. When
// generate_vcs() encounters an extern call, this module looks up the callee
// in the summary database and generates targeted VCs (null checks, range
// checks, aliasing checks, return contract assumptions) instead of the
// conservative Bool(true) VCs from unsafe_verify.
//
// Inspired by angr's SimProcedures (replace foreign calls with executable
// summaries) and Ghidra's type recovery at FFI boundaries.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

use crate::ffi_summary::{FfiSummaryDb, SideEffect, apply_summary, generate_ffi_vcs};

/// Detect whether a callee name refers to an extern/FFI function.
///
/// Uses heuristics on the MIR callee name:
/// - `libc::*` or `::libc::*` prefixes
/// - Known libc function names from the summary database
/// - Names containing `extern` or `ffi` (from MIR metadata)
#[must_use]
pub(crate) fn is_extern_call(callee: &str, db: &FfiSummaryDb) -> bool {
    let lower = callee.to_lowercase();

    // Pattern 1: libc:: prefix
    if lower.starts_with("libc::") || lower.contains("::libc::") {
        return true;
    }

    // Pattern 2: extern or ffi in name
    if lower.contains("extern") || lower.contains("::ffi::") {
        return true;
    }

    // Pattern 3: Last segment matches a known summary
    let last_segment = callee.rsplit("::").next().unwrap_or(callee);
    if db.lookup(last_segment).is_some() {
        return true;
    }

    // Pattern 4: Full name matches a known summary
    db.lookup(callee).is_some()
}

/// Extract the short function name from a possibly qualified callee string.
///
/// E.g., `libc::malloc` -> `malloc`, `std::ffi::c_str::strlen` -> `strlen`.
fn extract_callee_name(callee: &str) -> &str {
    callee.rsplit("::").next().unwrap_or(callee)
}

/// Generate targeted VCs for an FFI call site using summary-based contracts.
///
/// This is the main entry point called from `generate_vcs()` in lib.rs.
/// Returns a non-empty vec if a summary was found, or empty vec if not
/// (in which case the caller falls through to conservative VCs).
///
/// For each matching summary, generates:
/// 1. Parameter contract VCs (null, range, aliasing) via `generate_ffi_vcs()`
/// 2. Return contract assumption constraining the dest variable
/// 3. Side effect VCs for allocation/deallocation operations
#[must_use]
pub(crate) fn generate_call_site_vcs(
    func_name: &str,
    callee: &str,
    args: &[Formula],
    dest_var: &str,
    span: &SourceSpan,
    db: &FfiSummaryDb,
) -> Vec<VerificationCondition> {
    let short_name = extract_callee_name(callee);
    let summary = match db.lookup(short_name).or_else(|| db.lookup(callee)) {
        Some(s) => s,
        None => return Vec::new(),
    };

    let mut vcs = Vec::new();

    // 1. Parameter contract VCs (null checks, range checks, aliasing)
    // Use the existing generate_ffi_vcs but re-tag with FfiBoundaryViolation kind.
    let param_vcs = generate_ffi_vcs(func_name, summary, args);
    for vc in param_vcs {
        // Re-wrap the Assertion VCs as FfiBoundaryViolation for richer categorization.
        let desc = match &vc.kind {
            VcKind::Assertion { message } => message.clone(),
            _ => vc.kind.description(),
        };
        vcs.push(VerificationCondition {
            kind: VcKind::FfiBoundaryViolation { callee: short_name.to_string(), desc },
            function: func_name.into(),
            location: span.clone(),
            formula: vc.formula,
            contract_metadata: None,
        });
    }

    // 2. Return contract: constrain dest_var using the summary's return contract.
    let return_formula = apply_summary(summary, args);
    if return_formula != Formula::Bool(true) {
        // Substitute __ffi_ret with the actual dest variable.
        let instantiated = return_formula.rename_var("__ffi_ret", dest_var);
        // The return contract is an assumption (the caller can rely on it).
        // We generate a VC asserting the negation: if UNSAT, the contract holds.
        // For now, we add it as a FfiBoundaryViolation with descriptive text.
        vcs.push(VerificationCondition {
            kind: VcKind::FfiBoundaryViolation {
                callee: short_name.to_string(),
                desc: format!("return contract: {dest_var} satisfies summary"),
            },
            function: func_name.into(),
            location: span.clone(),
            formula: Formula::Not(Box::new(instantiated)),
            contract_metadata: None,
        });
    }

    // 3. Side effect VCs for allocation/deallocation operations.
    for effect in &summary.side_effects {
        match effect {
            SideEffect::AllocatesMemory => {
                // VC: the returned pointer is either null or a valid allocation.
                // This is already captured by the return contract for malloc/calloc.
                // Generate an additional VC asserting the allocation is non-null
                // (conservative: caller should check return value).
                vcs.push(VerificationCondition {
                    kind: VcKind::FfiBoundaryViolation {
                        callee: short_name.to_string(),
                        desc: "allocation may return null".to_string(),
                    },
                    function: func_name.into(),
                    location: span.clone(),
                    formula: Formula::Eq(
                        Box::new(Formula::Var(dest_var.to_string(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    contract_metadata: None,
                });
            }
            SideEffect::FreesMemory => {
                // VC: the freed pointer must have been previously allocated.
                // Conservative: we assert the pointer is non-null (as a necessary
                // condition for a valid free, though free(NULL) is technically ok).
                if let Some(_arg) = args.first() {
                    vcs.push(VerificationCondition {
                        kind: VcKind::FfiBoundaryViolation {
                            callee: short_name.to_string(),
                            desc: "freed pointer must be valid allocation".to_string(),
                        },
                        function: func_name.into(),
                        location: span.clone(),
                        // Conservative: always SAT = "cannot verify allocation provenance"
                        formula: Formula::Bool(true),
                        contract_metadata: None,
                    });
                }
            }
            SideEffect::WritesGlobal(name) => {
                // Havoc the global: subsequent reads get a fresh value.
                // We generate a VC noting the side effect for audit purposes.
                vcs.push(VerificationCondition {
                    kind: VcKind::FfiBoundaryViolation {
                        callee: short_name.to_string(),
                        desc: format!("writes global `{name}` (state invalidated)"),
                    },
                    function: func_name.into(),
                    location: span.clone(),
                    // Informational: always SAT to flag the side effect.
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                });
            }
            SideEffect::CallsCallback => {
                // Conservative: callback may modify any non-local state.
                vcs.push(VerificationCondition {
                    kind: VcKind::FfiBoundaryViolation {
                        callee: short_name.to_string(),
                        desc: "calls callback (non-local state havoced)".to_string(),
                    },
                    function: func_name.into(),
                    location: span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                });
            }
            // ReadsGlobal and None have no verification obligations.
            _ => {}
        }
    }

    vcs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ffi_summary::FfiSummaryDb;

    #[test]
    fn test_is_extern_call_libc_prefix() {
        let db = FfiSummaryDb::new();
        assert!(is_extern_call("libc::malloc", &db));
        assert!(is_extern_call("std::libc::free", &db));
        assert!(is_extern_call("core::ffi::c_str::strlen", &db));
    }

    #[test]
    fn test_is_extern_call_known_name() {
        let db = FfiSummaryDb::new();
        assert!(is_extern_call("malloc", &db));
        assert!(is_extern_call("some::module::memcpy", &db));
    }

    #[test]
    fn test_is_extern_call_unknown() {
        let db = FfiSummaryDb::new();
        assert!(!is_extern_call("std::vec::Vec::push", &db));
        assert!(!is_extern_call("my_safe_function", &db));
    }

    #[test]
    fn test_extract_callee_name() {
        assert_eq!(extract_callee_name("libc::malloc"), "malloc");
        assert_eq!(extract_callee_name("std::ffi::c_str::strlen"), "strlen");
        assert_eq!(extract_callee_name("malloc"), "malloc");
    }

    #[test]
    fn test_generate_call_site_vcs_malloc() {
        let db = FfiSummaryDb::new();
        let args = vec![Formula::Var("size".into(), Sort::Int)];
        let vcs = generate_call_site_vcs(
            "test_fn",
            "libc::malloc",
            &args,
            "_ret",
            &SourceSpan::default(),
            &db,
        );

        // malloc: non-null param + range param + return contract + allocation side effect
        assert!(!vcs.is_empty(), "malloc should produce VCs");

        // All VCs should be FfiBoundaryViolation
        for vc in &vcs {
            assert!(
                matches!(&vc.kind, VcKind::FfiBoundaryViolation { .. }),
                "all VCs should be FfiBoundaryViolation, got: {:?}",
                vc.kind
            );
        }

        // Should have null-check VC
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("non-null")
            )),
            "should have non-null parameter check"
        );

        // Should have allocation may return null VC
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("allocation may return null")
            )),
            "should have allocation null check"
        );
    }

    #[test]
    fn test_generate_call_site_vcs_memcpy() {
        let db = FfiSummaryDb::new();
        let args = vec![
            Formula::Var("dest".into(), Sort::Int),
            Formula::Var("src".into(), Sort::Int),
            Formula::Var("n".into(), Sort::Int),
        ];
        let vcs =
            generate_call_site_vcs("test_fn", "memcpy", &args, "_ret", &SourceSpan::default(), &db);

        assert!(!vcs.is_empty(), "memcpy should produce VCs");

        // Should have non-alias VC
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("must not alias")
            )),
            "should have aliasing check for memcpy"
        );
    }

    #[test]
    fn test_generate_call_site_vcs_unknown_returns_empty() {
        let db = FfiSummaryDb::new();
        let vcs = generate_call_site_vcs(
            "test_fn",
            "unknown_extern_fn",
            &[],
            "_ret",
            &SourceSpan::default(),
            &db,
        );
        assert!(vcs.is_empty(), "unknown function should return empty VCs");
    }

    #[test]
    fn test_generate_call_site_vcs_return_contract() {
        let db = FfiSummaryDb::new();
        let args = vec![Formula::Var("s".into(), Sort::Int)];
        let vcs =
            generate_call_site_vcs("test_fn", "strlen", &args, "_ret", &SourceSpan::default(), &db);

        // strlen: non-null param + return contract (ret >= 0)
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("return contract")
            )),
            "should have return contract VC"
        );
    }

    #[test]
    fn test_generate_call_site_vcs_free_side_effect() {
        let db = FfiSummaryDb::new();
        let args = vec![Formula::Var("ptr".into(), Sort::Int)];
        let vcs =
            generate_call_site_vcs("test_fn", "free", &args, "_ret", &SourceSpan::default(), &db);

        // free: nullable param (no null check) + FreesMemory side effect
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("freed pointer")
            )),
            "should have deallocation VC"
        );
    }

    #[test]
    fn test_ffi_boundary_violation_proof_level() {
        let kind =
            VcKind::FfiBoundaryViolation { callee: "malloc".into(), desc: "null check".into() };
        assert_eq!(
            kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "FFI boundary violations should be L0 safety"
        );
    }

    #[test]
    fn test_ffi_boundary_violation_description() {
        let kind = VcKind::FfiBoundaryViolation {
            callee: "memcpy".into(),
            desc: "parameters 0 and 1 must not alias".into(),
        };
        let desc = kind.description();
        assert!(desc.contains("memcpy"));
        assert!(desc.contains("must not alias"));
    }

    #[test]
    fn test_ffi_boundary_violation_no_runtime_fallback() {
        let kind = VcKind::FfiBoundaryViolation { callee: "malloc".into(), desc: "test".into() };
        assert!(
            !kind.has_runtime_fallback(true),
            "FFI boundary violations have no runtime fallback"
        );
    }
}
