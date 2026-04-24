// dead_code audit: crate-level suppression removed (#939)
//! trust-router: VC dispatch to verification backends
//!
//! Routes VerificationConditions to appropriate solver backends and collects
//! results. Each backend implements the VerificationBackend trait.
//! This crate provides the Router, VerificationBackend trait, and MockBackend.
//!
//! tRust #791: Pipeline v2 adds MirRouter for MIR-level function classification
//! and dispatch to zani-lib (BMC), sunder-lib (deductive), or v1 fallback.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// --- Internal submodules (extracted from lib.rs for file-size compliance) ---
mod backend_trait;
mod router;
pub(crate) mod routing;
mod types;
// tRust #791: Pipeline v2 Phase 2 — MIR-level router for function classification
// and dispatch to zani-lib, sunder-lib, or v1 pipeline.
pub(crate) mod mir_router;
// tRust #791: Pipeline v2 Phase 2 — Obligation adapter that maps external tool
// results back to per-obligation identities (source span, VcKind, function name).
pub(crate) mod verification_obligation;

// --- Public re-exports preserving the crate's external API ---
pub use backend_trait::VerificationBackend;
pub use router::Router;
pub use types::{ArenaVc, BackendRole, BackendSelection, IndependenceResult};

// --- Internal re-exports so existing crate-internal callers still find these ---
pub(crate) use routing::select_backend;

// tRust #791: Pipeline v2 public re-exports — MIR-level router and obligation adapter.
pub use mir_router::build_v1_vcs;
#[cfg(feature = "pipeline-v2")]
pub use mir_router::{MirRouter, MirRouterConfig, MirStrategy};
#[cfg(feature = "pipeline-v2")]
pub use verification_obligation::VerificationObligation;

// tRust #703: Re-export the unified error type at the crate root.
pub(crate) mod error;
pub use error::RouterError;

// tRust #882: Memory guard re-exports for solver memory limit enforcement.
pub use memory_guard::{MemoryGuard, MemoryGuardError, MemorySnapshot};

// tRust #886: Incremental Z4 session re-exports.
pub use incremental_z4::{CommonAssertion, IncrementalZ4Session, IncrementalZ4Stats};

// tRust #870: LLVM2 codegen backend re-exports.
#[cfg(feature = "llvm2-backend")]
pub use llvm2_backend::{
    Llvm2Backend as Llvm2CodegenBackend, Llvm2BackendConfig, Llvm2BackendError,
};

// --- Existing submodules (unchanged) ---
// tRust #970: adaptive removed — dead code cleanup
// tRust #970: cache_integration removed — dead code cleanup
pub mod cegar_backend;
pub(crate) mod cegar_classifier;
// tRust #970: certus_backend removed — dead code cleanup
// tRust #970: cex_reuse removed — dead code cleanup
// tRust #970: classifier removed — dead code cleanup
pub mod enrichment;
pub mod fallback;
// tRust #970: governor removed — dead code cleanup
pub mod health;
// tRust #970: health_monitor removed — dead code cleanup
pub mod independence;
// tRust #970: isolation removed — IsolationError inlined into error.rs
// tRust #792: lean5_replay, lean5_tactics, lean5_templates removed — lean5 cluster deleted.
// tRust #970: metrics removed — dead code cleanup
pub mod mock_backend;
// tRust #970: obligation_priority removed — dead code cleanup
// tRust #970: optimizer removed — dead code cleanup
pub(crate) mod ownership_encoding;
// tRust #970: parallel removed — dead code cleanup
// tRust: parallel_dispatch removed (#950 dead code cleanup)
// tRust #970: unified_memory removed — dead code cleanup
// tRust #970: portfolio removed — dead code cleanup
pub mod query_cache;
pub mod replay;
pub(crate) mod result_cache;
// tRust #970: routing_metrics removed — dead code cleanup
pub mod scheduler;
// tRust #798: smt2_export provides SMT-LIB2 text serialization used by multiple
// modules (ownership_encoding, certus_backend, smtlib_backend). Always compiled.
pub(crate) mod smt2_export;
// tRust #798: smtlib_backend provides utility functions (generate_smtlib_script,
// parse_solver_output) used by certus_backend and ownership_encoding. The
// SmtLibBackend struct (subprocess z4 invocation) is feature-gated inside
// the module behind `not(pipeline-v2)`. Always compiled as a module.
pub mod smtlib_backend;
// tRust #798: Persistent solver with incremental SMT-LIB2 push/pop protocol.
// Superseded by Pipeline v2 direct library calls.
#[cfg(not(feature = "pipeline-v2"))]
pub(crate) mod incremental_smtlib_backend;
// tRust #886: Incremental Z4 session with push/pop scoping for batch VC
// verification. Maintains a persistent solver context and shares common
// assertions across multiple VCs. Always compiled (not feature-gated by
// pipeline-v2) since it provides a higher-level API over the subprocess path.
pub mod incremental_z4;
pub mod strategies;
// tRust #798/#970: sunder_backend classification helpers (is_deductive_vc_kind).
// SunderBackend struct is feature-gated behind `not(pipeline-v2)`.
pub mod sunder_backend;
// tRust #194: Termination dispatch — PDR/k-induction prove safety, not termination.
pub(crate) mod termination_dispatch;
// tRust #970: timeout removed — dead code cleanup
pub mod tla2_backend;
// tRust #970: trace removed — dead code cleanup
// tRust #798: zani_backend (subprocess BMC) superseded by trust-zani-lib in
// Pipeline v2. Feature-gated behind `not(pipeline-v2)`.
pub mod aggregation;
#[cfg(not(feature = "pipeline-v2"))]
pub mod zani_backend;
// tRust #792: axiom_provenance.rs removed — unused, no intra-crate callers.
// tRust #792: binary_pipeline.rs removed — unused, no intra-crate callers.
// tRust #950: benchmarking removed — dead code cleanup
// tRust #792: z4_backend/ removed — z4 integration now via z4-direct (trust-router)
// and trust-zani-lib (Pipeline v2).
// tRust #798: z4_direct.rs removed — z4 integration now via trust-zani-lib (Pipeline v2).
// tRust #798: sunder_native.rs removed — sunder integration now via trust-sunder-lib (Pipeline v2).
// tRust #792: lean5_backend removed — lean5 integration now via dedicated lean5 crate.
// tRust #970: load_balance removed — dead code cleanup
// tRust #792: solver_benchmark.rs, solver_portfolio.rs removed — unused, no intra-crate callers.
// tRust #970: portfolio_racer removed — dead code cleanup
// tRust #950: resource_governor removed — dead code cleanup
// tRust #882: Process memory monitoring for solver memory limit enforcement.
pub(crate) mod memory_guard;
// tRust #870: LLVM2 verified codegen backend (behind llvm2-backend feature).
#[cfg(feature = "llvm2-backend")]
pub mod llvm2_backend;
// tRust #970: solver_execution removed — ExecutionError inlined into error.rs
// tRust #520: VC-level solver result caching wired into verification dispatch.
pub mod solver_cache;
// tRust #676/#970: shared_pool removed — dead code cleanup
// tRust #798: sp_pipeline.rs removed — strongest-postcondition pipeline now via trust-sunder-lib (Pipeline v2).

#[cfg(test)]
mod router_tests;
