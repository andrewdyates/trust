//! tRust: Query providers for trust_proof_results and trust_proof_telemetry.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0
//!
//! Stub providers that return None. The real implementation will be added
//! when the verification pipeline is wired into the query system (Epic #1).
//!
//! Gated: returns None immediately unless -Z trust-verify is enabled.
//! Follows the coverage_ids_info provider pattern in coverage/query.rs.
//!
//! Design: designs/2026-03-27-proof-carrying-mir.md

use rustc_middle::mir::trust_proof::{TrustProofResults, TrustProofTelemetry};
use rustc_middle::ty::{self, TyCtxt};

use crate::trust_verify;

/// tRust: Query provider for `trust_proof_results`.
///
/// Returns per-function verification results (semantic, deterministic, HashStable).
/// Currently a stub that returns None. When the verification pipeline is
/// integrated, this will run: MIR → extract → vcgen → router → results.
///
/// The `arena_cache` modifier handles allocation: we return `Option<TrustProofResults>`
/// (owned) and the query system arenas it to `Option<&'tcx TrustProofResults>`.
pub(crate) fn trust_proof_results<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance_def: ty::InstanceKind<'tcx>,
) -> Option<TrustProofResults> {
    if !trust_verify::verification_enabled(tcx.sess) {
        return None;
    }

    let mir_body = tcx.instance_mir(instance_def);
    trust_verify::collect_verification_artifacts(tcx, mir_body)
        .map(|artifacts| artifacts.proof_results)
}

/// tRust: Query provider for `trust_proof_telemetry`.
///
/// Returns per-function verification telemetry (non-deterministic, NOT HashStable).
/// Contains solver timings and counterexamples for reporting.
/// Currently a stub that returns None.
///
/// Uses `no_hash` modifier so timings don't affect incremental compilation.
pub(crate) fn trust_proof_telemetry<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance_def: ty::InstanceKind<'tcx>,
) -> Option<TrustProofTelemetry> {
    if !trust_verify::verification_enabled(tcx.sess) {
        return None;
    }

    let mir_body = tcx.instance_mir(instance_def);
    trust_verify::collect_verification_artifacts(tcx, mir_body).map(|artifacts| artifacts.telemetry)
}
