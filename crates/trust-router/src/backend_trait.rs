//! The VerificationBackend trait definition.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::formula_arena::{FormulaArena, FormulaRef};
use trust_types::*;

use crate::BackendRole;

/// A verification backend that can check verification conditions.
///
/// Implement this trait to add a new solver backend to the router.
/// The router calls `can_handle` to check compatibility, then `verify`
/// to dispatch the VC.
///
/// # Examples
///
/// ```
/// use trust_types::{VerificationCondition, VerificationResult, ProofStrength};
/// use trust_router::VerificationBackend;
///
/// struct MyBackend;
///
/// impl VerificationBackend for MyBackend {
///     fn name(&self) -> &str { "my-solver" }
///
///     fn can_handle(&self, vc: &VerificationCondition) -> bool {
///         // Accept only L0 safety VCs
///         vc.kind.proof_level() == trust_types::ProofLevel::L0Safety
///     }
///
///     fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
///         // Real implementation would call an SMT solver here
///         VerificationResult::Unknown {
///             solver: "my-solver".into(),
///             time_ms: 0,
///             reason: "not implemented".into(),
///         }
///     }
/// }
///
/// let backend = MyBackend;
/// assert_eq!(backend.name(), "my-solver");
/// ```
pub trait VerificationBackend: Send + Sync {
    fn name(&self) -> &str;

    /// tRust: Backend role used to rank solver families.
    ///
    /// Defaults to `General` so existing backends continue to compile even if
    /// they do not yet advertise a more specific capability.
    fn role(&self) -> BackendRole {
        BackendRole::General
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool;
    fn verify(&self, vc: &VerificationCondition) -> VerificationResult;

    /// tRust #708: Arena-aware verification entry point.
    ///
    /// Accepts a `VerificationCondition` whose formula field is an owned
    /// `Formula`, plus a `FormulaRef` root and `&FormulaArena` for
    /// arena-native processing. Backends that support arena-native SMT
    /// emission can override this to avoid the `to_formula()` round-trip.
    ///
    /// The default implementation materializes the formula from the arena
    /// and delegates to `verify()`, so existing backends work unchanged.
    fn verify_arena(
        &self,
        vc: &VerificationCondition,
        _root: FormulaRef,
        _arena: &FormulaArena,
    ) -> VerificationResult {
        self.verify(vc)
    }
}
