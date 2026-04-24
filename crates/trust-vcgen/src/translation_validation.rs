// trust-vcgen/translation_validation.rs: Translation validation types (#149, #458)
//
// tRust #458: This module is a thin re-export layer. The authoritative
// translation validation crate is `trust-transval`. Types live in `trust-types`
// (shared foundation); implementation lives in `trust-transval::vc_core`.
//
// Consumers should prefer importing from `trust_transval` directly for the
// full API (RefinementChecker, SimulationRelationBuilder, EquivalenceVcGenerator).
// This module exists for backward compatibility with code that imports
// translation validation types via `trust_vcgen::`.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// tRust #458: Re-export shared types from trust-types.
pub use trust_types::translation_validation::{
    CheckKind, RefinementVc, SimulationRelation, TranslationCheck, TranslationValidationError,
    infer_identity_relation,
};
