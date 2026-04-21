#![allow(dead_code)]
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
mod types;
mod backend_trait;
mod router;
pub(crate) mod routing;
// tRust #791: Pipeline v2 Phase 2 — MIR-level router for function classification
// and dispatch to zani-lib, sunder-lib, or v1 pipeline.
pub(crate) mod mir_router;
// tRust #791: Pipeline v2 Phase 2 — Obligation adapter that maps external tool
// results back to per-obligation identities (source span, VcKind, function name).
pub(crate) mod verification_obligation;

// --- Public re-exports preserving the crate's external API ---
pub use types::{BackendRole, BackendSelection, IndependenceResult, ArenaVc};
pub use backend_trait::VerificationBackend;
pub use router::Router;

// --- Internal re-exports so existing crate-internal callers still find these ---
pub(crate) use routing::select_backend;

// tRust #791: Pipeline v2 public re-exports — MIR-level router and obligation adapter.
#[cfg(feature = "pipeline-v2")]
pub use mir_router::{MirRouter, MirRouterConfig, MirStrategy};
#[cfg(feature = "pipeline-v2")]
pub use verification_obligation::VerificationObligation;

// tRust #703: Re-export the unified error type at the crate root.
pub(crate) mod error;
pub use error::RouterError;

// --- Existing submodules (unchanged) ---
pub(crate) mod adaptive;
pub(crate) mod batching;
pub(crate) mod cache_integration;
pub mod cegar_backend;
pub(crate) mod cegar_classifier;
pub(crate) mod certus_backend;
pub(crate) mod cex_reuse;
pub(crate) mod classifier;
pub mod enrichment;
pub mod fallback;
pub(crate) mod governor;
pub mod health;
pub(crate) mod health_monitor;
pub mod independence;
pub(crate) mod isolation;
// tRust #792: lean5_replay, lean5_tactics, lean5_templates removed — lean5 cluster deleted.
pub(crate) mod metrics;
pub mod mock_backend;
pub(crate) mod obligation_priority;
pub(crate) mod optimizer;
pub(crate) mod ownership_encoding;
pub(crate) mod parallel;
// tRust #456: Work-stealing parallel VC dispatch with independence-aware load balancing.
pub(crate) mod parallel_dispatch;
pub(crate) mod unified_memory;
pub(crate) mod portfolio;
pub mod query_cache;
pub mod replay;
pub(crate) mod result_cache;
pub(crate) mod routing_metrics;
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
pub mod strategies;
// tRust #798: sunder_backend classification functions (is_deductive_vc_kind,
// sunder_affinity, etc.) are always available. The SunderBackend subprocess
// struct is feature-gated inside the module behind `not(pipeline-v2)`.
pub mod sunder_backend;
// tRust #194: Termination dispatch — PDR/k-induction prove safety, not termination.
pub(crate) mod termination_dispatch;
pub(crate) mod timeout;
pub mod tla2_backend;
pub(crate) mod trace;
// tRust #798: zani_backend (subprocess BMC) superseded by trust-zani-lib in
// Pipeline v2. Feature-gated behind `not(pipeline-v2)`.
#[cfg(not(feature = "pipeline-v2"))]
pub mod zani_backend;
pub mod aggregation;
// tRust #792: axiom_provenance.rs removed — unused, no intra-crate callers.
// tRust #792: binary_pipeline.rs removed — unused, no intra-crate callers.
pub(crate) mod benchmarking;
// tRust #792: z4_backend/ removed — z4 integration now via z4-direct (trust-router)
// and trust-zani-lib (Pipeline v2).
// tRust #798: z4_direct.rs removed — z4 integration now via trust-zani-lib (Pipeline v2).
// tRust #798: sunder_native.rs removed — sunder integration now via trust-sunder-lib (Pipeline v2).
// tRust #792: lean5_backend removed — lean5 integration now via dedicated lean5 crate.
pub(crate) mod load_balance;
// tRust #792: solver_benchmark.rs, solver_portfolio.rs removed — unused, no intra-crate callers.
// tRust #363: Portfolio racer — dispatch same VC to multiple solvers in parallel.
pub(crate) mod portfolio_racer;
// tRust #196: Priority-aware resource governor with backpressure and statistics.
pub(crate) mod resource_governor;
// tRust #195: Hybrid native/worker-isolated solver execution architecture.
pub(crate) mod solver_execution;
// tRust #520: VC-level solver result caching wired into verification dispatch.
pub mod solver_cache;
// tRust #676: Shared rayon thread pool across verification pipeline.
pub(crate) mod shared_pool;
// tRust #798: sp_pipeline.rs removed — strongest-postcondition pipeline now via trust-sunder-lib (Pipeline v2).

#[cfg(test)]
mod router_tests;
