//! Backend selection and preference ranking for VC dispatch.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;

use trust_types::*;

use crate::ownership_encoding;
use crate::termination_dispatch;
use crate::{BackendRole, BackendSelection, VerificationBackend};

pub(crate) fn backend_plan(
    backends: &[Arc<dyn VerificationBackend>],
    vc: &VerificationCondition,
) -> Vec<BackendSelection> {
    let mut plan: Vec<BackendSelection> = ordered_backend_indices(backends, vc)
        .into_iter()
        .map(|index| {
            let backend = &backends[index];
            BackendSelection {
                index,
                name: backend.name().to_string().into(),
                role: backend.role(),
                can_handle: backend.can_handle(vc),
            }
        })
        .collect();

    // Keep the already-ranked plan stable for any tie groups.
    // The ordering is determined entirely by the index list above.
    plan.shrink_to_fit();
    plan
}

pub(crate) fn select_backend<'a>(
    backends: &'a [Arc<dyn VerificationBackend>],
    vc: &VerificationCondition,
) -> Option<&'a Arc<dyn VerificationBackend>> {
    // tRust #422: Classify the VC's property kind once, then validate each
    // candidate backend against it. This prevents unsound dispatch (e.g.,
    // routing termination VCs to PDR/k-induction which only prove safety).
    let property = termination_dispatch::classify_property(vc);

    for backend_idx in ordered_backend_indices(backends, vc) {
        let backend = &backends[backend_idx];
        if backend.can_handle(vc) {
            // tRust #422: Skip backends that are invalid for this property kind.
            let validity = termination_dispatch::validate_dispatch(property, backend.name());
            if validity.is_invalid() {
                continue;
            }
            return Some(backend);
        }
    }
    None
}

fn ordered_backend_indices(
    backends: &[Arc<dyn VerificationBackend>],
    vc: &VerificationCondition,
) -> Vec<usize> {
    let level = vc.kind.proof_level();
    // tRust: #178 Detect ownership VCs for certus priority routing.
    let is_ownership = ownership_encoding::is_ownership_vc(vc);
    let mut ranked: Vec<(usize, u8, u8)> = backends
        .iter()
        .enumerate()
        .map(|(index, backend)| {
            let can_handle = u8::from(!backend.can_handle(vc));
            (index, can_handle, backend_preference_rank(backend.role(), level, is_ownership))
        })
        .collect();

    ranked.sort_by_key(|(index, can_handle, rank)| (*can_handle, *rank, *index));
    ranked.into_iter().map(|(index, _, _)| index).collect()
}

fn backend_preference_rank(role: BackendRole, level: ProofLevel, is_ownership: bool) -> u8 {
    // tRust: #178 Ownership VCs rank the Ownership backend first.
    if is_ownership {
        return match role {
            BackendRole::Ownership => 0,
            BackendRole::SmtSolver => 1,
            BackendRole::Deductive => 2,
            BackendRole::BoundedModelChecker => 3,
            BackendRole::Cegar => 4,
            BackendRole::HigherOrder => 5,
            BackendRole::Temporal => 6,
            BackendRole::Neural => 7,
            BackendRole::General => 9,
        };
    }

    match level {
        ProofLevel::L0Safety => match role {
            BackendRole::SmtSolver => 0,
            BackendRole::BoundedModelChecker => 1,
            BackendRole::Cegar => 2,
            BackendRole::Deductive => 3,
            BackendRole::Ownership => 4,
            BackendRole::HigherOrder => 5,
            BackendRole::Temporal => 6,
            BackendRole::Neural => 7,
            BackendRole::General => 9,
        },
        ProofLevel::L1Functional => match role {
            BackendRole::Deductive => 0,
            BackendRole::Cegar => 1,
            BackendRole::HigherOrder => 2,
            BackendRole::SmtSolver => 3,
            BackendRole::BoundedModelChecker => 4,
            BackendRole::Ownership => 5,
            BackendRole::Temporal => 6,
            BackendRole::Neural => 7,
            BackendRole::General => 9,
        },
        // tRust #427: HigherOrder (lean5) ranked 1 for L2Domain — lean5 handles
        // induction proofs needed for domain-level properties (universal
        // quantification, recursive structures). Temporal (tla2) stays first
        // for liveness/fairness; lean5 is preferred over deductive (sunder)
        // for higher-order reasoning.
        ProofLevel::L2Domain => match role {
            BackendRole::Temporal => 0,
            BackendRole::HigherOrder => 1,
            BackendRole::Deductive => 2,
            BackendRole::Cegar => 3,
            BackendRole::Ownership => 4,
            BackendRole::Neural => 5,
            BackendRole::SmtSolver => 6,
            BackendRole::BoundedModelChecker => 7,
            BackendRole::General => 9,
        },
        // Default rank for any future ProofLevel variants.
        _ => 8,
    }
}
