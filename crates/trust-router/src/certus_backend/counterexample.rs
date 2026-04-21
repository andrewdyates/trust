// trust-router/certus_backend/counterexample.rs: Unsafe-specific counterexample interpretation
//
// tRust #360: Classifies ownership violations from certus counterexamples,
// mapping raw variable assignments to structured safety violation types.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use super::unsafe_classify::{classify_unsafe_vc, UnsafeVcClass};

/// tRust #360: Classify an ownership violation from a certus counterexample.
///
/// Examines the counterexample variable assignments to determine the specific
/// kind of unsafe-code violation certus found.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum OwnershipViolation {
    /// A null pointer was dereferenced.
    NullPointerDeref { pointer_var: String },
    /// A pointer was dereferenced into unallocated memory.
    InvalidAllocation { pointer_var: String },
    /// A pointer was misaligned for its target type.
    MisalignedAccess { pointer_var: String },
    /// A write was attempted through a read-only pointer.
    WritePermissionDenied { pointer_var: String },
    /// A freed allocation was accessed.
    UseAfterFree { pointer_var: String },
    /// Two exclusive regions alias (same base address).
    AliasingViolation { region_a: String, region_b: String },
    /// A transmute has incompatible layouts.
    IncompatibleLayout { src_ty: String, dst_ty: String },
    /// Generic ownership violation.
    Generic { description: String },
}

impl OwnershipViolation {
    /// Human-readable description for diagnostics.
    pub(crate) fn description(&self) -> String {
        match self {
            OwnershipViolation::NullPointerDeref { pointer_var } => {
                format!("null pointer dereference: {pointer_var} == 0")
            }
            OwnershipViolation::InvalidAllocation { pointer_var } => {
                format!("invalid allocation: {pointer_var} points to unallocated memory")
            }
            OwnershipViolation::MisalignedAccess { pointer_var } => {
                format!("misaligned access: {pointer_var} not properly aligned")
            }
            OwnershipViolation::WritePermissionDenied { pointer_var } => {
                format!("write permission denied: {pointer_var} is read-only")
            }
            OwnershipViolation::UseAfterFree { pointer_var } => {
                format!("use-after-free: {pointer_var} points to freed allocation")
            }
            OwnershipViolation::AliasingViolation { region_a, region_b } => {
                format!("aliasing violation: {region_a} and {region_b} have same base address")
            }
            OwnershipViolation::IncompatibleLayout { src_ty, dst_ty } => {
                format!("incompatible layout: size_of({src_ty}) != size_of({dst_ty})")
            }
            OwnershipViolation::Generic { description } => description.clone(),
        }
    }
}

/// tRust #360: Interpret a certus counterexample in the context of an unsafe VC.
///
/// Given the VC's classification and the raw counterexample from certus,
/// produces a structured `OwnershipViolation` describing the specific safety
/// issue found.
#[must_use]
pub(crate) fn interpret_unsafe_counterexample(
    vc: &VerificationCondition,
    cex: &Counterexample,
) -> OwnershipViolation {
    let class = classify_unsafe_vc(vc);

    // Look for characteristic variable patterns in the counterexample
    let has_null = cex.assignments.iter().any(|(name, val)| {
        name.starts_with("ptr_") && matches!(val, CounterexampleValue::Uint(0))
    });

    let has_unalloc = cex.assignments.iter().any(|(_, val)| {
        matches!(val, CounterexampleValue::Int(-1))
    });

    let has_writable_false = cex.assignments.iter().any(|(name, val)| {
        name.starts_with("writable_") && matches!(val, CounterexampleValue::Bool(false))
    });

    let ptr_var = cex.assignments.iter()
        .find(|(name, _)| name.starts_with("ptr_"))
        .map(|(name, _)| name.clone())
        .unwrap_or_else(|| "unknown".to_string());

    match class {
        Some(UnsafeVcClass::RawDeref) => {
            if has_null {
                OwnershipViolation::NullPointerDeref { pointer_var: ptr_var }
            } else if has_unalloc {
                OwnershipViolation::InvalidAllocation { pointer_var: ptr_var }
            } else {
                OwnershipViolation::MisalignedAccess { pointer_var: ptr_var }
            }
        }
        Some(UnsafeVcClass::RawWrite) => {
            if has_writable_false {
                OwnershipViolation::WritePermissionDenied { pointer_var: ptr_var }
            } else if has_null {
                OwnershipViolation::NullPointerDeref { pointer_var: ptr_var }
            } else {
                OwnershipViolation::InvalidAllocation { pointer_var: ptr_var }
            }
        }
        Some(UnsafeVcClass::UseAfterFree) => {
            OwnershipViolation::UseAfterFree { pointer_var: ptr_var }
        }
        Some(UnsafeVcClass::PermissionDenied) => {
            OwnershipViolation::WritePermissionDenied { pointer_var: ptr_var }
        }
        Some(UnsafeVcClass::Transmute) => {
            // Try to extract type names from counterexample variables
            let src = cex.assignments.iter()
                .find(|(name, _)| name.starts_with("size_"))
                .map(|(name, _)| name.strip_prefix("size_").unwrap_or("Src").to_string())
                .unwrap_or_else(|| "Src".to_string());
            let dst = cex.assignments.iter()
                .filter(|(name, _)| name.starts_with("size_"))
                .nth(1)
                .map(|(name, _)| name.strip_prefix("size_").unwrap_or("Dst").to_string())
                .unwrap_or_else(|| "Dst".to_string());
            OwnershipViolation::IncompatibleLayout { src_ty: src, dst_ty: dst }
        }
        Some(UnsafeVcClass::SepFrame) => {
            // Frame violation: look for equal region base addresses
            let region_vars: Vec<&String> = cex.assignments.iter()
                .filter(|(name, _)| name.contains("_base"))
                .map(|(name, _)| name)
                .collect();
            if region_vars.len() >= 2 {
                OwnershipViolation::AliasingViolation {
                    region_a: region_vars[0].clone(),
                    region_b: region_vars[1].clone(),
                }
            } else {
                OwnershipViolation::Generic {
                    description: "frame preservation violation".to_string(),
                }
            }
        }
        _ => {
            OwnershipViolation::Generic {
                description: format!(
                    "unsafe code violation in {} ({} assignments)",
                    vc.function, cex.assignments.len()
                ),
            }
        }
    }
}
