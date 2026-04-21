//! trust-type-recover: Multi-strategy type recovery for reverse compilation
//!
//! Recovers high-level types from binary analysis artifacts (DWARF debug info,
//! memory access patterns, value-set analysis). Part of the reverse compilation
//! pipeline (v6 Phase VII, step G3).
//!
//! Recovery combines multiple strategies, including DWARF-assisted recovery,
//! access-pattern analysis, value-range analysis, signature matching, and
//! caller/callee return-register analysis.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]
#![allow(dead_code)]

pub(crate) mod error;
pub(crate) mod evidence;
pub(crate) mod recoverer;
pub(crate) mod return_type;
pub(crate) mod strategy;
pub(crate) mod types;

pub use error::TypeRecoveryError;
pub use evidence::{EvidenceSource, SignaturePosition, TypeEvidence};
pub use recoverer::TypeRecoverer;
pub use return_type::{
    CalleeReturnObservation, CalleeReturnTypeStrategy, CallingConvArch, ExitRegisterState,
    ReturnRegisterUse, ReturnTypeObservation, ReturnTypeStrategy,
};
pub use strategy::{
    AccessObservation, AccessPatternStrategy, ArrayRecoveryStrategy, CallSiteObservation,
    DereferenceObservation, DwarfEntry, DwarfMember, DwarfStrategy, DwarfTag,
    IndexedAccessObservation, PointerRecoveryStrategy, RecoveryContext, SignatureMatchStrategy,
    StructAccessObservation, StructRecoveryStrategy, TypeRecoveryStrategy, ValueRangeObservation,
    ValueRangeStrategy,
};
pub use types::{RecoveredType, StructField};
