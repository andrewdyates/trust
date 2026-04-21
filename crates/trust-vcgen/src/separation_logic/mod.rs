// trust-vcgen/separation_logic/mod.rs: Separation logic primitives for unsafe Rust verification
//
// Implements separation logic formulas (PointsTo, SepStar, SepWand, Emp, Pure)
// and translates them to first-order logic with explicit heap encoding for
// SMT solving. Generates VCs for common unsafe operations: raw pointer deref,
// raw pointer write, and transmute.
//
// The heap is modeled as an SMT array (Int -> Int) with explicit disjointness
// constraints for the separating conjunction (*). This follows the standard
// symbolic heap encoding from separation logic literature (Reynolds 2002,
// O'Hearn/Pym 1999).
//
// Extended in #191 with:
// - Provenance tracking for raw pointers (SymbolicPointer, ProvenanceId)
// - Frame rule application for modular unsafe code verification
// - Symbolic heap representation (SymbolicHeap) for tracking heap state
// - Integration with UnsafeOpKind from unsafe_vc.rs
//
// Part of #191: Unsafe code verification via separation logic / provenance engine
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod formula;
mod provenance;
mod encoding;
mod heap;
mod frame;
pub(crate) mod unsafe_ops;
mod vc_gen;

#[cfg(test)]
mod tests;

// Re-export all public API items to preserve the existing module interface.
pub use formula::SepFormula;
pub use provenance::{PointerPermission, ProvenanceId, SymbolicPointer};
pub use encoding::{encode_heap_disjointness, encode_unsafe_block, sep_to_formula};
pub use heap::{HeapCell, SymbolicHeap};
pub use frame::{apply_frame_rule, encode_framed_unsafe_block};
pub use unsafe_ops::{address_of_sep_vc, ffi_call_sep_vc, unsafe_fn_call_sep_vc};
#[allow(unused_imports)]
pub(crate) use unsafe_ops::vcs_from_unsafe_op;
pub use vc_gen::{deref_vc, raw_write_vc, transmute_vc};
