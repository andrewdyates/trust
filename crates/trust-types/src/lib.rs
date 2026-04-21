//! trust-types: Verification IR for the tRust compiler
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// tRust: Allow unused crate deps when compiled in compiler context
// (serde_json used by downstream, thiserror reserved for error types)
// tRust: Allow std HashMap/HashSet — FxHash lint only applies to compiler internals
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]
#![allow(dead_code)]

// tRust #837: Deterministic hash collections for compilation reproducibility.
pub mod fx;

// tRust #696: String interning for Formula variable names.
mod interner;
pub use interner::{Interner, Symbol};

// tRust #467: pub(crate) mod for modules not accessed via trust_types::module:: paths externally.
// Items from these modules are re-exported via `pub use module::*` below where needed.
pub(crate) mod annotation;
// tRust #285: Bitvector theory types for fixed-width integer operations.
pub(crate) mod bitvector;
pub(crate) mod boundary;
pub mod call_graph;
// tRust #605: MIR atomic intrinsic detection and parsing.
mod atomic_intrinsics;
mod concurrency;
mod facts;
mod formula;
// tRust #695: Arena-allocated formula representation for reduced heap allocation.
pub mod formula_arena;
// tRust #792: formula_utils.rs removed — utilities now in formula/ submodules.
pub(crate) mod generics;
pub(crate) mod lifetime;
pub(crate) mod lifetime_analysis;
mod model;
pub(crate) mod resilience;
// tRust #792: sort_check.rs removed — sort checking now in formula/sort.rs.
// tRust #308: SMT-LIB2 pretty printer for formatted solver output.
pub mod smt_printer;
// tRust #713: Canonical SMT-LIB2 logic selection, free variable collection, and sort inference.
pub mod smt_logic;
// tRust #308: SMT-LIB2 string-based pretty printer for debugging and external solver interop.
pub(crate) mod smtlib2_printer;
mod result;
pub(crate) mod spec;
pub(crate) mod spec_attrs;
mod spec_parse;
// tRust #162: state_machine extraction lives in trust-temporal/extract.rs.
// Types (StateMachine, StateInfo, Transition) live in model.rs.
// tRust #375: Dead state_machine.rs (692 lines) removed — was never in module tree.
pub(crate) mod strengthen;
pub(crate) mod taint;
pub(crate) mod trait_resolution;
pub(crate) mod traits;
// tRust #150: Provenance tracking types for memory model Layer 2.
pub mod provenance;
// tRust #198: Unified memory model for sunder/certus cross-function proof composition.
pub mod unified_memory;
// tRust #223: MIR pattern matching for vulnerability detection.
pub(crate) mod patterns;
// tRust #160: Shared utility functions consolidated from multiple crates.
pub(crate) mod utils;
// tRust #458: Translation validation shared types (used by trust-vcgen and trust-transval).
pub mod translation_validation;
// tRust #571: z4_bindings conversion bridge for direct z4 integration.
pub mod z4_bridge;
// tRust #632: sunder-core PureExpr conversion bridge for native sunder integration.
#[cfg(feature = "sunder-bridge")]
pub mod sunder_bridge;

#[cfg(any(test, feature = "test-utils"))]
pub mod test_utils;

pub use annotation::*;
pub use boundary::*;
pub use atomic_intrinsics::parse_atomic_intrinsic;
pub use concurrency::*;
pub use facts::*;
pub use formula::*;
pub use generics::*;
pub use lifetime::*;
pub use lifetime_analysis::*;
pub use model::*;
pub use resilience::*;
pub use result::*;
pub use spec::*;
pub use spec_attrs::*;
pub use spec_parse::*;
pub use strengthen::*;
pub use taint::*;
pub use trait_resolution::*;
pub use traits::*;
pub use utils::{operand_place, strip_generics};
// tRust #713: Re-export canonical SMT-LIB2 utilities.
pub use smt_logic::{collect_free_var_decls, infer_sort, select_logic};
pub use smt_printer::{PrintConfig, SmtPrinter};
// tRust #458: Re-export translation validation types at crate root.
pub use translation_validation::{
    CheckKind, RefinementVc, SimulationRelation, TranslationCheck,
    TranslationValidationError, block_successors_list, detect_back_edges,
    infer_identity_relation,
};
