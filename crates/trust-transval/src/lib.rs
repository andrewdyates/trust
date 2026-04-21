//! trust-transval: Translation validation for tRust (#149)
//!
//! Proves that compiled code (post-optimization MIR or machine code) refines
//! the pre-optimization MIR semantics. Core theorem:
//!
//!   forall inputs, not UB_MIR(inputs) => Behavior(target, inputs) in Behavior(source, inputs)
//!
//! Architecture:
//!   - refinement:   RefinementChecker orchestrates per-function validation
//!   - simulation:   SimulationRelationBuilder constructs source<->target mappings
//!   - equivalence:  EquivalenceVcGenerator produces solver-ready VCs
//!   - optimization: OptimizationPassValidator applies pass-specific strategies
//!
//! References:
//!   - Pnueli, Siegel, Singerman. "Translation Validation" (TACAS 1998)
//!   - Necula. "Translation Validation for an Optimizing Compiler" (PLDI 2000)
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// tRust: Allow std HashMap/HashSet -- FxHash lint only applies to compiler internals
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]
#![allow(dead_code)]

pub(crate) mod bisimulation;
pub(crate) mod equivalence;
pub(crate) mod error;
pub(crate) mod optimization;
pub(crate) mod property_check;
pub(crate) mod refinement;
pub(crate) mod refinement_types;
pub(crate) mod simulation;
pub(crate) mod simulation_check;
// tRust #458: Core VC generation — authoritative implementation of generate_refinement_vcs.
pub(crate) mod vc_core;
pub(crate) mod z4_validator;

// Re-export primary API types.
pub use equivalence::{EquivalenceVcGenerator, VcClassification};
pub use error::TransvalError;
pub use optimization::{OptimizationPass, OptimizationPassValidator};
pub use refinement::{RefinementChecker, ValidationResult, ValidationVerdict};
pub use simulation::SimulationRelationBuilder;
pub use z4_validator::{SmtPropertyResult, SmtValidationResult, TranslationValidator, VcOutcome};

// tRust #458: Re-export translation validation types from trust-types and
// core VC generation from vc_core. trust-transval is the authoritative crate
// for translation validation; trust-vcgen delegates here.
pub use trust_types::{
    CheckKind, RefinementVc, SimulationRelation, TranslationCheck, TranslationValidationError,
    block_successors_list, detect_back_edges, infer_identity_relation,
};
pub use vc_core::generate_refinement_vcs;
