//! tRust: Verification MIR pass.
//!
//! Runs the tRust verification pipeline as a native MIR pass after optimization,
//! before codegen. This is the compiler-integrated equivalent of trust-driver's
//! after_analysis callback.
//!
//! Pipeline: MIR Body -> trust-mir-extract -> trust-vcgen -> trust-router -> report
//!
//! The pass delegates to the trust-* crates for extraction and VC generation:
//!
//!   let func = trust_mir_extract::extract_function(tcx, body);
//!   let vcs = trust_vcgen::generate_vcs(&func);
//!
//! Enable with `-Z trust-verify`. Disable explicitly with `-Z no-trust-verify`.
//!
//! Design: designs/2026-03-27-proof-carrying-mir.md
//! Master plan: designs/2026-03-27-trust-master-plan.md
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// tRust: Proof-carrying MIR types for building query results.
// tRust: deterministic — Use FxIndexMap for the verification results map to preserve
// insertion order, ensuring deterministic iteration for report generation.
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, LazyLock, Mutex, OnceLock};

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::{FxHashSet, FxIndexMap};
use rustc_hir::def::DefKind;
use rustc_hir::{LocalSource, Node};
use rustc_index::IndexVec;
use rustc_middle::mir::trust_proof::{
    ObligationId, TrustBinOp, TrustDisposition, TrustFunctionSummary, TrustObligationDetail,
    TrustObligationKind, TrustProofLevel, TrustProofResults, TrustProofStrength,
    TrustProofTelemetry, TrustRuntimeFallback, TrustRuntimeFallbackReason, TrustStatus,
};
use rustc_middle::mir::{Body, START_BLOCK, TerminatorKind};
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{self, TyCtxt};
use rustc_session::Session;
use rustc_span::Symbol;
use rustc_span::def_id::LOCAL_CRATE;
use tracing::{debug, trace};
// tRust: Iterative verification loop types for the native MIR pass.
use trust_loop::{LoopConfig, VerifyContext};
use trust_types::{
    BinOp, CounterexampleValue, FunctionTransportResult, ProofStrength, ReasoningKind,
    TRANSPORT_PREFIX, TransportMessage, TransportObligationResult, VcKind, VerificationCondition,
    VerificationResult,
};

/// tRust: Static flag to track whether we've already printed the report header
/// for this compilation session. Reset per-crate.
static TRUST_HEADER_PRINTED: AtomicBool = AtomicBool::new(false);

/// tRust: Cached router with real solver backends. Initialized once per
/// compilation session via OnceLock. Avoids repeated filesystem probing
/// for solver binaries on every function verification.
static ROUTER: OnceLock<trust_router::Router> = OnceLock::new();

/// tRust: Shared backend inventory reused by both the VC router and MIR router.
/// This keeps backend discovery one-time per compilation session.
type SharedRouterBackends = Vec<Arc<dyn trust_router::VerificationBackend>>;
static ROUTER_BACKENDS: OnceLock<SharedRouterBackends> = OnceLock::new();

fn get_router_backends() -> &'static SharedRouterBackends {
    ROUTER_BACKENDS.get_or_init(discover_router_backends)
}

/// tRust: Get or initialize the cached router with real solver backends.
fn get_router() -> &'static trust_router::Router {
    ROUTER.get_or_init(build_router)
}

/// tRust #796: Cached MIR-level router for Pipeline v2 dispatch. Wraps the
/// v1 Router and adds MIR-property classification (contracts, unsafe, loops,
/// FFI, atomics). Initialized once per compilation session via OnceLock.
#[cfg(feature = "pipeline-v2")]
static MIR_ROUTER: OnceLock<trust_router::MirRouter> = OnceLock::new();

/// tRust #796: Get or initialize the MIR router for Pipeline v2.
#[cfg(feature = "pipeline-v2")]
fn get_mir_router() -> &'static trust_router::MirRouter {
    MIR_ROUTER.get_or_init(|| {
        let v1_router = build_router();
        trust_router::MirRouter::new(v1_router, trust_router::MirRouterConfig::default())
    })
}

// tRust #538: Global verification results map.
//
// Stores per-function verification status keyed by the fully qualified
// def-path string (e.g. "mycrate::module::function"). Populated by the
// TrustVerify MIR pass after each function is verified, readable by any
// compiler pass or downstream consumer without requiring TyCtxt.
//
// Thread-safe: MIR passes may run in parallel, so all access goes through
// the Mutex. LazyLock initialises the map on first access.

/// tRust #538: Coarse verification status for a function.
///
/// Intentionally simpler than `TrustStatus` (which is per-obligation).
/// This is a per-function roll-up suitable for cross-pass queries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerificationStatus {
    /// All obligations proved (or no obligations).
    Proved,
    /// At least one obligation failed with a counterexample.
    Failed,
    /// No failures, but some obligations are unknown / timed out.
    Unknown,
    /// No failures, but some unproved obligations have runtime checks.
    RuntimeChecked,
}

/// tRust #538: Global map of function def-path -> verification status.
// tRust: deterministic — FxIndexMap preserves insertion order, so iteration
// during report generation produces deterministic output across compilations
// (functions appear in the order they were verified, which is determined by
// the MIR pass traversal order).
static VERIFICATION_RESULTS: LazyLock<Mutex<FxIndexMap<String, VerificationStatus>>> =
    LazyLock::new(|| Mutex::new(FxIndexMap::default()));

/// tRust #538: Query the verification status of a function by its def-path string.
///
/// Returns `None` if the function has not been verified yet (e.g. verification
/// is disabled, the function was filtered out, or the pass hasn't run yet).
///
/// # Example
/// ```ignore
/// if let Some(status) = trust_verification_status("mycrate::my_function") {
///     match status {
///         VerificationStatus::Proved => { /* elide checks */ }
///         VerificationStatus::Failed => { /* emit warning */ }
///         _ => {}
///     }
/// }
/// ```
pub fn trust_verification_status(fn_name: &str) -> Option<VerificationStatus> {
    VERIFICATION_RESULTS.lock().ok().and_then(|map| map.get(fn_name).cloned())
}

/// tRust #538: Store the verification status for a function in the global map.
fn store_verification_status(fn_name: &str, summary: &TrustFunctionSummary) {
    let status = if summary.failed > 0 {
        VerificationStatus::Failed
    } else if summary.unknown > 0 {
        VerificationStatus::Unknown
    } else if summary.runtime_checked > 0 {
        VerificationStatus::RuntimeChecked
    } else {
        VerificationStatus::Proved
    };

    if let Ok(mut map) = VERIFICATION_RESULTS.lock() {
        map.insert(fn_name.to_string(), status);
    }
}

// tRust: Bridge the MIR verification pass to trust-loop's host callbacks.
struct MirVerifyContext<'a> {
    router: &'a trust_router::Router,
}

// tRust: Delegate verification to the shared router and use trust-strengthen
// to analyze failures and produce strengthened VC replacements (#539).
impl<'a> VerifyContext for MirVerifyContext<'a> {
    fn verify_vcs(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        self.router.verify_all(vcs)
    }

    fn strengthen_specs(
        &self,
        failed: &[(VerificationCondition, VerificationResult)],
    ) -> Vec<VerificationCondition> {
        // tRust #539: Wire trust-strengthen into the iterative verification loop.
        // For each failed VC, analyze the failure pattern and generate proposals.
        // Convert proposals into strengthened VCs by conjoining the original formula
        // with a precondition guard derived from the proposal.
        strengthen_failed_vcs(failed)
    }
}

/// tRust #539: Analyze failed VCs via trust-strengthen and produce strengthened replacements.
///
/// Pipeline:
///   1. `analyzer::analyze_failure()` classifies each failure (overflow, div-zero, OOB, etc.)
///   2. `proposer::strengthen()` generates spec proposals (preconditions, postconditions)
///   3. Proposals are converted to VCs: `Implies(precondition, original_formula)`
///
/// The strengthened VCs have the same slot key (function + location + kind) as the originals
/// so that `merge_unproved_vcs` in trust-loop replaces them for the next iteration.
fn strengthen_failed_vcs(
    failed: &[(VerificationCondition, VerificationResult)],
) -> Vec<VerificationCondition> {
    use std::collections::BTreeMap;

    use trust_strengthen::{FailureAnalysis, Proposal, ProposalKind, analyze_failure, strengthen};
    use trust_types::{Formula, Sort};

    if failed.is_empty() {
        return Vec::new();
    }

    // tRust: Group failures by function for batch proposal generation.
    let mut by_function: BTreeMap<String, Vec<(&VerificationCondition, FailureAnalysis)>> =
        BTreeMap::new();
    for (vc, result) in failed {
        let analysis = analyze_failure(vc, result);
        by_function.entry(vc.function.to_string()).or_default().push((vc, analysis));
    }

    let mut strengthened = Vec::new();

    for (function, entries) in &by_function {
        let analyses: Vec<&FailureAnalysis> = entries.iter().map(|(_, a)| a).collect();
        // tRust: Determine function path -- use the VC's function field which is
        // typically the fully qualified path (e.g., "crate::module::function").
        let function_path = function.as_str();
        let function_name = function.rsplit("::").next().unwrap_or(function);

        let analyses_owned: Vec<FailureAnalysis> = analyses.into_iter().cloned().collect();
        let proposals = strengthen(function_path, function_name, &analyses_owned);

        // tRust: Convert proposals to strengthened VCs. For each proposal that targets
        // an existing failed VC, create a replacement VC with a strengthened formula.
        // We match proposals back to their originating VCs by index correspondence
        // (analyzer produces one FailureAnalysis per VC, proposer produces N proposals
        // per analysis). For each original VC, collect matching precondition proposals
        // and conjoin them as guards on the original formula.
        for (vc, _analysis) in entries {
            let preconditions: Vec<&Proposal> = proposals
                .iter()
                .filter(|p| p.function_path == function_path)
                .filter(|p| matches!(p.kind, ProposalKind::AddPrecondition { .. }))
                .collect();

            if preconditions.is_empty() {
                continue;
            }

            // tRust: Build the strengthened formula as:
            //   (precond_1 AND precond_2 AND ...) => original_formula
            // This gives the solver the additional assumptions to work with.
            let guard_formulas: Vec<Formula> = preconditions
                .iter()
                .map(|p| {
                    let spec_body = match &p.kind {
                        ProposalKind::AddPrecondition { spec_body } => spec_body.clone(),
                        _ => unreachable!(),
                    };
                    // tRust: Encode the textual spec as a named boolean variable.
                    // The solver treats it as an uninterpreted assumption. Future
                    // work (#540) will parse spec_body into a proper Formula AST.
                    Formula::Var(format!("__precond_{spec_body}"), Sort::Bool)
                })
                .collect();

            let guard = if guard_formulas.len() == 1 {
                guard_formulas.into_iter().next().unwrap()
            } else {
                Formula::And(guard_formulas)
            };

            let strengthened_formula =
                Formula::Implies(Box::new(guard), Box::new(vc.formula.clone()));

            let mut strengthened_vc = (*vc).clone();
            strengthened_vc.formula = strengthened_formula;
            strengthened.push(strengthened_vc);
        }
    }

    debug!(
        "tRust: strengthen_specs produced {} strengthened VCs from {} failures",
        strengthened.len(),
        failed.len(),
    );
    strengthened
}

/// tRust: Incremental verification cache (#67). Stores proof results keyed
/// by function body hash (SHA-256). Thread-safe via Mutex since MIR passes
/// may run in parallel. Initialized lazily on first access; persisted to
/// `.trust-cache/proof-cache.json` at the end of compilation.
static PROOF_CACHE: OnceLock<Mutex<trust_cache::VerificationCache>> = OnceLock::new();

/// tRust: Get or initialize the verification cache.
fn get_cache() -> &'static Mutex<trust_cache::VerificationCache> {
    PROOF_CACHE.get_or_init(|| {
        let cache_path = std::path::PathBuf::from(".trust-cache/proof-cache.json");
        let cache = trust_cache::VerificationCache::load(&cache_path).unwrap_or_else(|e| {
            debug!("tRust: failed to load proof cache: {e}, starting fresh");
            trust_cache::VerificationCache::in_memory()
        });
        Mutex::new(cache)
    })
}

fn compiler_cache_enabled() -> bool {
    std::env::var_os("TRUST_COMPILER_CACHE").is_some()
}

#[derive(Hash, PartialEq, Eq)]
struct ExactVcKey {
    function: String,
    file: String,
    line_start: u32,
    col_start: u32,
    line_end: u32,
    col_end: u32,
    fingerprint: u64,
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum VerificationOutcomeKey {
    Proved,
    Failed,
    Unknown,
    Timeout,
    Other,
}

fn exact_vc_key(vc: &VerificationCondition) -> ExactVcKey {
    ExactVcKey {
        function: vc.function.to_string(),
        file: vc.location.file.clone(),
        line_start: vc.location.line_start,
        col_start: vc.location.col_start,
        line_end: vc.location.line_end,
        col_end: vc.location.col_end,
        fingerprint: trust_vcgen::vc_fingerprint(vc),
    }
}

fn dedupe_exact_vcs(vcs: Vec<VerificationCondition>) -> Vec<VerificationCondition> {
    let mut seen = FxHashSet::default();
    let mut deduped = Vec::with_capacity(vcs.len());

    for vc in vcs {
        if seen.insert(exact_vc_key(&vc)) {
            deduped.push(vc);
        }
    }

    deduped
}

fn verification_outcome_key(result: &VerificationResult) -> VerificationOutcomeKey {
    match result {
        VerificationResult::Proved { .. } => VerificationOutcomeKey::Proved,
        VerificationResult::Failed { .. } => VerificationOutcomeKey::Failed,
        VerificationResult::Unknown { .. } => VerificationOutcomeKey::Unknown,
        VerificationResult::Timeout { .. } => VerificationOutcomeKey::Timeout,
        _ => VerificationOutcomeKey::Other,
    }
}

fn dedupe_exact_results(
    results: Vec<(VerificationCondition, VerificationResult)>,
) -> Vec<(VerificationCondition, VerificationResult)> {
    let mut seen = FxHashSet::default();
    let mut deduped = Vec::with_capacity(results.len());

    for (vc, result) in results {
        let key = (exact_vc_key(&vc), verification_outcome_key(&result));
        if seen.insert(key) {
            deduped.push((vc, result));
        }
    }

    deduped
}

pub(crate) struct VerificationArtifacts {
    pub(crate) proof_results: TrustProofResults,
    pub(crate) telemetry: TrustProofTelemetry,
    pub(crate) results: Vec<(VerificationCondition, VerificationResult)>,
    pub(crate) transport_results: Vec<TransportObligationResult>,
}

/// tRust #529: Build router with the shared backend inventory.
fn build_router() -> trust_router::Router {
    trust_router::Router::with_arc_backends(get_router_backends().clone())
}

/// tRust #529: Discover portfolio solver backends when available.
///
/// Probes for solver binaries on the system and registers all available
/// backends for portfolio dispatch. Each backend communicates via subprocess
/// (SMT-LIB2 over stdin/stdout), avoiding library linking conflicts.
///
/// Backend portfolio:
/// 1. IncrementalZ4Session with z4 (Z4_PATH env var, then PATH lookup) — primary SMT
/// 2. Tla2Backend — temporal obligations and protocol-style properties
/// 3. MockBackend (always present as fallback)
fn discover_router_backends() -> SharedRouterBackends {
    let mut backends: SharedRouterBackends = Vec::new();

    // tRust #529: Probe for z4 SMT solver (primary backend).
    let z4_path = std::env::var("Z4_PATH").ok().or_else(|| which_solver("z4"));

    if let Some(path) = z4_path {
        debug!("tRust: using z4 solver at {path}");
        backends.push(Arc::new(
            trust_router::IncrementalZ4Session::with_solver_path(path).with_timeout(30_000),
        ));
    } else {
        debug!("tRust: no z4 solver found");
    }

    // tRust: Register the temporal backend for temporal / protocol obligations.
    backends.push(Arc::new(trust_router::tla2_backend::Tla2Backend));

    // tRust: Log how many solver backends were discovered.
    let solver_count = backends.len();
    if solver_count == 0 {
        debug!("tRust: no solvers found, using mock backend only");
    } else {
        debug!("tRust: registered {solver_count} solver backend(s) for portfolio dispatch");
    }

    // tRust: Always include mock backend as fallback.
    backends.push(Arc::new(trust_router::mock_backend::MockBackend));

    backends
}

/// tRust: Search PATH for a solver binary by name.
fn which_solver(name: &str) -> Option<String> {
    std::process::Command::new("which")
        .arg(name)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
}

/// tRust: The trust_verify MIR pass.
///
/// Runs verification on each function's optimized MIR. This pass does NOT
/// modify the MIR -- it is a read-only analysis pass that produces verification
/// results (printed to stderr for now, will flow through query system later).
///
/// Follows the pattern of InstrumentCoverage: gated behind a flag, runs
/// per-function, does not modify MIR semantics.
pub(super) struct TrustVerify;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TrustOutputMode {
    Human,
    Json,
    Both,
}

impl TrustOutputMode {
    fn parse(sess: &Session) -> Self {
        match sess.opts.unstable_opts.trust_verify_output.as_str() {
            "json" => Self::Json,
            "both" => Self::Both,
            _ => Self::Human,
        }
    }

    fn emit_human(self) -> bool {
        matches!(self, Self::Human | Self::Both)
    }

    fn emit_json(self) -> bool {
        matches!(self, Self::Json | Self::Both)
    }
}

impl<'tcx> crate::MirPass<'tcx> for TrustVerify {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        let enabled = verification_enabled(sess);
        trace!("tRust: is_enabled = {enabled}");
        enabled
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let mir_source = body.source;
        trace!("tRust: run_pass entered for {:?}", mir_source.def_id());

        if !should_verify_body(tcx, body) {
            return;
        }

        let def_id = mir_source.def_id();

        // tRust: Use with_no_trimmed_paths to avoid trimmed_def_paths panic
        // when no diagnostics are emitted (our pass is read-only).
        let func_path = with_no_trimmed_paths!(tcx.def_path_str(def_id));
        debug!("tRust: verifying {func_path}");
        let Some(artifacts) = collect_verification_artifacts(tcx, body) else {
            return;
        };
        debug!(
            "tRust: proof results for {func_path}: {} obligations ({} trusted, {} runtime-checked, {} failed, {} unknown)",
            artifacts.proof_results.summary.total,
            artifacts.proof_results.summary.trusted,
            artifacts.proof_results.summary.runtime_checked,
            artifacts.proof_results.summary.failed,
            artifacts.proof_results.summary.unknown,
        );

        let output_mode = TrustOutputMode::parse(tcx.sess);

        // tRust: Report results via rustc diagnostics when human-readable output is enabled.
        if output_mode.emit_human() {
            if !artifacts.results.is_empty() {
                report_results(tcx, body, &artifacts.results);
            } else if !artifacts.transport_results.is_empty() {
                report_transport_results(tcx, body, &artifacts.transport_results);
            }
        }

        // tRust #542: Emit structured JSON transport line for this function.
        // cargo-trust and trust-driver parse these lines to get structured
        // verification results without fragile text parsing.
        emit_transport_json(
            &func_path,
            tcx.sess,
            &artifacts.results,
            &artifacts.proof_results.summary,
        );

        // tRust #538: Store function-level verification status in the global
        // map so other compiler passes can query it without TyCtxt.
        store_verification_status(&func_path, &artifacts.proof_results.summary);
    }

    fn is_required(&self) -> bool {
        // tRust: Verification is not required for correctness -- it is additive.
        // It can be disabled without affecting compilation semantics.
        false
    }

    fn is_mir_dump_enabled(&self) -> bool {
        // tRust: No MIR dump for the verification pass -- it doesn't modify MIR.
        false
    }
}

pub(crate) fn verification_enabled(sess: &Session) -> bool {
    sess.opts.unstable_opts.trust_verify && !sess.opts.unstable_opts.no_trust_verify
}

fn should_verify_body<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> bool {
    let mir_source = body.source;

    if mir_source.promoted.is_some() {
        return false;
    }

    if matches!(
        mir_source.instance,
        ty::InstanceKind::Intrinsic(..) | ty::InstanceKind::Virtual(..)
    ) {
        return false;
    }

    let def_id = mir_source.def_id();

    // tRust: Only verify local items (not cross-crate inlined MIR).
    if !def_id.is_local() {
        return false;
    }

    if !tcx.def_kind(def_id).is_fn_like() {
        trace!("tRust: skipping non-function {def_id:?}");
        return false;
    }

    if matches!(tcx.def_kind(def_id), DefKind::Closure) {
        if let Some(local_def_id) = def_id.as_local() {
            let closure_hir_id = tcx.local_def_id_to_hir_id(local_def_id);
            if tcx.hir_parent_iter(closure_hir_id).any(
                |(_, node)| matches!(node, Node::LetStmt(local) if matches!(local.source, LocalSource::Contract)),
            ) {
                trace!("tRust: skipping contract-generated closure {def_id:?}");
                return false;
            }
        }
    }

    // tRust: Skip compiler-generated shims and items without proper HIR backing.
    // These include drop glue, vtable shims, and other synthetic MIR bodies
    // where extracting HIR attributes would panic.
    if matches!(
        mir_source.instance,
        ty::InstanceKind::DropGlue(..)
            | ty::InstanceKind::CloneShim(..)
            | ty::InstanceKind::FnPtrShim(..)
            | ty::InstanceKind::ReifyShim(..)
            | ty::InstanceKind::VTableShim(..)
            | ty::InstanceKind::ClosureOnceShim { .. }
            | ty::InstanceKind::ThreadLocalShim(..)
            | ty::InstanceKind::ConstructCoroutineInClosureShim { .. }
            | ty::InstanceKind::FnPtrAddrShim(..)
            | ty::InstanceKind::AsyncDropGlueCtorShim(..)
    ) {
        trace!("tRust: skipping compiler-generated shim {def_id:?}");
        return false;
    }

    if let TerminatorKind::Unreachable = body.basic_blocks[START_BLOCK].terminator().kind {
        trace!("tRust: skipping unreachable function {def_id:?}");
        return false;
    }

    true
}

pub(crate) fn collect_verification_artifacts<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Option<VerificationArtifacts> {
    if !verification_enabled(tcx.sess) || !should_verify_body(tcx, body) {
        return None;
    }

    let func = trust_mir_extract::extract_function(tcx, body);
    debug!(
        "tRust: extracted {} with {} contract(s), {} precondition(s), {} postcondition(s)",
        func.def_path,
        func.contracts.len(),
        func.preconditions.len(),
        func.postconditions.len(),
    );

    // tRust #941: Dump extracted VerifiableFunction as JSON for test fixture generation.
    // When TRUST_DUMP_MIR=<dir> is set, serialize each function to <dir>/<sanitized_name>.json.
    // Used to produce real-MIR fixtures for integration tests without requiring rustc_private.
    if let Ok(dump_dir) = std::env::var("TRUST_DUMP_MIR") {
        let dump_path = std::path::Path::new(&dump_dir);
        if let Err(e) = std::fs::create_dir_all(dump_path) {
            debug!("tRust: failed to create TRUST_DUMP_MIR dir {dump_dir}: {e}");
        } else {
            // Sanitize def_path for use as filename (replace :: with __)
            let sanitized = func.def_path.replace("::", "__");
            let file_path = dump_path.join(format!("{sanitized}.json"));
            match serde_json::to_string_pretty(&func) {
                Ok(json) => {
                    if let Err(e) = std::fs::write(&file_path, &json) {
                        debug!("tRust: failed to write MIR dump to {}: {e}", file_path.display());
                    } else {
                        trace!(
                            "tRust: dumped MIR for {} to {}",
                            func.def_path,
                            file_path.display()
                        );
                    }
                }
                Err(e) => {
                    debug!("tRust: failed to serialize {} for MIR dump: {e}", func.def_path);
                }
            }
        }
    }

    // tRust #67: Check incremental verification cache before dispatching to solver.
    // If the function body + contracts hash matches a cached entry, we can skip
    // the expensive solver dispatch entirely.
    if compiler_cache_enabled() {
        if let Ok(mut cache) = get_cache().lock() {
            if let trust_cache::CacheLookup::Hit(entry) = cache.lookup_function(&func) {
                debug!(
                    "tRust: cache hit for {} ({} obligations, {:?})",
                    func.def_path, entry.total_obligations, entry.verdict
                );
                // tRust #393: Return cached artifacts instead of None.
                // Reconstruct summary from cached counts so the caller can
                // log and report the cached verdict.
                let summary = TrustFunctionSummary {
                    total: entry.total_obligations as u32,
                    trusted: entry.proved as u32,
                    certified: 0,
                    failed: entry.failed as u32,
                    unknown: entry.unknown as u32,
                    runtime_checked: entry.runtime_checked as u32,
                    max_level: TrustProofLevel::None,
                };
                let proof_results = TrustProofResults {
                    dispositions: IndexVec::new(),
                    fingerprints: IndexVec::new(),
                    summary,
                };
                let telemetry = TrustProofTelemetry { details: IndexVec::new() };
                // Individual results are not stored in the cache, so return
                // empty results. The caller skips per-VC diagnostics when
                // results is empty but still logs the summary.
                return Some(VerificationArtifacts { proof_results, telemetry, results: vec![] });
            }
        }
    }

    // tRust #796: Pipeline v2 — classify and dispatch via MirRouter.
    // When the pipeline-v2 feature is enabled, the MirRouter classifies
    // functions by MIR properties (contracts, unsafe, loops, FFI, atomics)
    // and dispatches to specialized backends (zani-lib, sunder-lib).
    // V1Fallback functions still use the iterative verification loop.
    #[cfg(feature = "pipeline-v2")]
    {
        let mir_router = get_mir_router();
        let strategy = mir_router.classify(&func);
        debug!("tRust: pipeline-v2 classified {} as {strategy}", func.def_path);

        let max_level = effective_max_level(tcx.sess, &func);

        // tRust #796: Generate VCs regardless of strategy — needed for proof results.
        let (solver_vcs, discharged) = trust_vcgen::generate_vcs_with_discharge(&func);
        let solver_vcs = dedupe_exact_vcs(trust_vcgen::filter_vcs_by_level(solver_vcs, max_level));
        debug!(
            "tRust: {} max_level={max_level:?}, solver_vcs={}, discharged={}",
            func.def_path,
            solver_vcs.len(),
            discharged.len(),
        );

        let results = match strategy {
            trust_router::MirStrategy::V1Fallback => {
                // tRust #796: V1Fallback — use existing iterative verification loop.
                let loop_config = LoopConfig::default();
                let mir_ctx = MirVerifyContext { router: get_router() };
                let loop_result =
                    trust_loop::run_iterative_verification(&loop_config, solver_vcs, &mir_ctx);

                if loop_result.iterations > 1 {
                    debug!(
                        "tRust: iterative verification for {}: {} iterations, reason={:?}",
                        func.def_path, loop_result.iterations, loop_result.reason,
                    );
                }

                let mut combined = discharged;
                combined.extend(loop_result.final_results);
                dedupe_exact_results(combined)
            }
            _ => {
                // tRust #796: MIR router dispatch — verify function as a whole,
                // then pair the single result with each generated VC.
                let mir_result = mir_router.verify_function(&func);
                debug!(
                    "tRust: pipeline-v2 MIR dispatch for {} returned {}",
                    func.def_path,
                    match &mir_result {
                        VerificationResult::Proved { .. } => "proved",
                        VerificationResult::Failed { .. } => "failed",
                        VerificationResult::Unknown { .. } => "unknown",
                        VerificationResult::Timeout { .. } => "timeout",
                        _ => "other",
                    },
                );

                // tRust #796: Map per-function result to per-VC results.
                // The MIR router dispatched the whole function; we spread
                // its verdict across all VCs so the proof results pipeline
                // has uniform per-obligation entries.
                let mut combined = discharged;
                for vc in solver_vcs {
                    combined.push((vc, mir_result.clone()));
                }
                dedupe_exact_results(combined)
            }
        };

        let proof_results = build_proof_results(tcx.sess, &results, &[]);
        let telemetry = build_proof_telemetry(tcx.sess, &results);

        // tRust #67: Store verification result in cache for future compilations.
        if compiler_cache_enabled() {
            if let Ok(mut cache) = get_cache().lock() {
                let summary = &proof_results.summary;
                if cache.store_function(
                    &func,
                    summarize_verdict(&proof_results.summary),
                    summary.total as usize,
                    summary.trusted as usize,
                    summary.failed as usize,
                    summary.unknown as usize,
                    summary.runtime_checked as usize,
                ) {
                    if let Err(e) = cache.save() {
                        debug!("tRust: failed to save proof cache: {e}");
                    }
                }
            }
        }

        return Some(VerificationArtifacts { proof_results, telemetry, results, transport_results });
    }

    // tRust: V1 pipeline — existing iterative verification loop.
    #[cfg(not(feature = "pipeline-v2"))]
    {
        let max_level = effective_max_level(tcx.sess, &func);
        // tRust #428: Abstract interp pre-pass discharges cheap numeric VCs before solver dispatch.
        let (solver_vcs, discharged) = trust_vcgen::generate_vcs_with_discharge(&func);
        let solver_vcs = dedupe_exact_vcs(trust_vcgen::filter_vcs_by_level(solver_vcs, max_level));
        debug!(
            "tRust: {} max_level={max_level:?}, solver_vcs={}, discharged={}",
            func.def_path,
            solver_vcs.len(),
            discharged.len(),
        );

        // tRust #169: Keep the compiler-side loop configuration self-contained for
        // now instead of adding a new rustc_session unstable option.
        let loop_config = LoopConfig::default();
        // tRust #169: Run the iterative verification loop through the shared router.
        let mir_ctx = MirVerifyContext { router: get_router() };
        let loop_result =
            trust_loop::run_iterative_verification(&loop_config, solver_vcs, &mir_ctx);

        // tRust #169: Log iteration summary when the loop needed more than one round.
        if loop_result.iterations > 1 {
            let reason = &loop_result.reason;
            debug!(
                "tRust: iterative verification for {}: {} iterations, reason={:?}, proved={}, failed={}, unknown={}",
                func.def_path,
                loop_result.iterations,
                reason,
                loop_result.final_proved,
                loop_result.final_failed,
                loop_result.final_unknown,
            );
        }

        // tRust #366: Use the loop's final results directly instead of re-dispatching
        // to the solver. The iterative loop already ran verification and may have
        // refined results through strengthening rounds.
        // tRust #428: Prepend abstract-interp discharged results so they appear in
        // proof results and telemetry alongside solver results.
        let mut results = discharged;
        results.extend(loop_result.final_results);
        let results = dedupe_exact_results(results);
        let proof_results = build_proof_results(tcx.sess, &results, &[]);
        let telemetry = build_proof_telemetry(tcx.sess, &results);

        // tRust #67: Store verification result in cache for future compilations.
        if compiler_cache_enabled() {
            if let Ok(mut cache) = get_cache().lock() {
                let summary = &proof_results.summary;
                if cache.store_function(
                    &func,
                    summarize_verdict(&proof_results.summary),
                    summary.total as usize,
                    summary.trusted as usize,
                    summary.failed as usize,
                    summary.unknown as usize,
                    summary.runtime_checked as usize,
                ) {
                    // tRust: Best-effort persist — errors are non-fatal since cache is advisory.
                    if let Err(e) = cache.save() {
                        debug!("tRust: failed to save proof cache: {e}");
                    }
                }
            }
        }

        Some(VerificationArtifacts { proof_results, telemetry, results, transport_results })
    }
}

fn effective_max_level(
    sess: &Session,
    func: &trust_types::VerifiableFunction,
) -> trust_types::ProofLevel {
    let configured = match sess.opts.unstable_opts.trust_verify_level {
        0 => trust_types::ProofLevel::L0Safety,
        1 => trust_types::ProofLevel::L1Functional,
        _ => trust_types::ProofLevel::L2Domain,
    };

    if !func.contracts.is_empty()
        || !func.preconditions.is_empty()
        || !func.postconditions.is_empty()
    {
        configured.max(trust_types::ProofLevel::L1Functional)
    } else {
        configured
    }
}

/// tRust #67: Derive a FunctionVerdict from the compiler-internal summary counts.
fn summarize_verdict(summary: &TrustFunctionSummary) -> trust_types::FunctionVerdict {
    if summary.total == 0 {
        trust_types::FunctionVerdict::NoObligations
    } else if summary.failed > 0 {
        trust_types::FunctionVerdict::HasViolations
    } else if summary.unknown > 0 {
        trust_types::FunctionVerdict::Inconclusive
    } else if summary.runtime_checked > 0 {
        trust_types::FunctionVerdict::RuntimeChecked
    } else {
        trust_types::FunctionVerdict::Verified
    }
}

/// tRust: Report verification results using rustc's diagnostic system.
///
/// Emits rich diagnostics with file/line numbers and code snippets via
/// `body.span`. All verification results are emitted as notes (informational)
/// so they never trigger -D warnings or break builds. Verification is additive.
///
/// Takes paired (VC, result) tuples from trust-router. In the future, results
/// will also flow through tcx.trust_proof_results() query and be consumed by
/// codegen (for check elision) and by trust-report (for JSON/HTML output).
fn report_results(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    results: &[(VerificationCondition, VerificationResult)],
) {
    // tRust: Print header once per compilation session.
    // tRust: Use SeqCst to ensure proper synchronization in parallel compilation.
    if !TRUST_HEADER_PRINTED.swap(true, Ordering::SeqCst) {
        let crate_name = tcx.crate_name(LOCAL_CRATE);
        eprintln!();
        eprintln!("=== tRust Verification Report ({crate_name}) ===");
        eprintln!();
    }

    // tRust: Use body.span for rich diagnostics — rustc will render file:line:col
    // and code snippets automatically.
    let func_span = body.span;

    for (vc, result) in results {
        let tag = format_vc_kind(&vc.kind);
        let desc = vc.kind.description();

        // tRust: All results emitted as notes — verification must NEVER break builds.
        // The verification pass is additive: it reports findings without blocking compilation.
        match result {
            VerificationResult::Proved { solver, strength, time_ms, .. } => {
                tcx.dcx()
                    .struct_span_note(
                        func_span,
                        format!(
                            "tRust [{tag}]: {desc} — PROVED ({solver}, {time_ms}ms, {strength:?})"
                        ),
                    )
                    .emit();
            }
            VerificationResult::Failed { solver, counterexample, time_ms } => {
                let mut diag = tcx.dcx().struct_span_note(
                    func_span,
                    format!("tRust [{tag}]: {desc} — FAILED ({solver}, {time_ms}ms)"),
                );
                if let Some(cex) = counterexample {
                    diag.note(format!("counterexample: {cex}"));
                }
                diag.emit();
            }
            VerificationResult::Unknown { solver, reason, time_ms } => {
                if has_runtime_check(tcx.sess, &vc.kind) {
                    tcx.dcx()
                        .struct_span_note(
                            func_span,
                            format!(
                                "tRust [{tag}]: {desc} — RUNTIME-CHECKED ({solver}, {time_ms}ms)"
                            ),
                        )
                        .with_note(format!("reason: {reason}"))
                        .with_note(runtime_check_note(&vc.kind))
                        .emit();
                } else {
                    tcx.dcx()
                        .struct_span_note(
                            func_span,
                            format!("tRust [{tag}]: {desc} — UNKNOWN ({solver}, {time_ms}ms)"),
                        )
                        .with_note(format!("reason: {reason}"))
                        .emit();
                }
            }
            VerificationResult::Timeout { solver, timeout_ms } => {
                if has_runtime_check(tcx.sess, &vc.kind) {
                    tcx.dcx()
                        .struct_span_note(
                            func_span,
                            format!(
                                "tRust [{tag}]: {desc} — RUNTIME-CHECKED ({solver}, {timeout_ms}ms)"
                            ),
                        )
                        .with_note("reason: solver timed out before proving the obligation")
                        .with_note(runtime_check_note(&vc.kind))
                        .emit();
                } else {
                    tcx.dcx()
                        .struct_span_note(
                            func_span,
                            format!("tRust [{tag}]: {desc} — TIMEOUT ({solver}, {timeout_ms}ms)"),
                        )
                        .emit();
                }
            }
            _ => {
                tcx.dcx()
                    .struct_span_note(
                        func_span,
                        format!(
                            "tRust [{tag}]: {desc} — UNKNOWN (unsupported verification result variant)"
                        ),
                    )
                    .emit();
            }
        }
    }
}

fn report_transport_results(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    results: &[TransportObligationResult],
) {
    let func_span = body.span;

    for result in results {
        let mut diag = tcx.dcx().struct_span_note(
            func_span,
            format!(
                "tRust [{}]: {} — {} ({}, {}ms)",
                result.kind,
                result.description,
                result.outcome.to_ascii_uppercase().replace('_', "-"),
                result.solver,
                result.time_ms,
            ),
        );
        if let Some(location) = &result.location {
            diag.note(format!(
                "location: {}:{}:{}",
                location.file, location.line_start, location.col_start
            ));
        }
        if let Some(counterexample) = &result.counterexample {
            diag.note(format!("counterexample: {counterexample}"));
        }
        if let Some(reason) = &result.reason {
            diag.note(format!("reason: {reason}"));
        }
        diag.emit();
    }
}

fn build_transport_results(
    sess: &Session,
    results: &[(VerificationCondition, VerificationResult)],
    summary: &TrustFunctionSummary,
) {
    let mut proved: usize = 0;
    let mut failed: usize = 0;
    let mut unknown: usize = 0;
    let mut runtime_checked: usize = 0;

    let obligation_results: Vec<TransportObligationResult> = results
        .iter()
        .map(|(vc, result)| {
            let tag = format_vc_kind(&vc.kind).to_string();
            let desc = vc.kind.description();
            let (outcome, solver, time_ms, counterexample, counterexample_model, reason) =
                match result {
                    VerificationResult::Proved { solver, time_ms, .. } => {
                        proved += 1;
                        ("proved".to_string(), solver.to_string(), *time_ms, None, None, None)
                    }
                    VerificationResult::Failed { solver, time_ms, counterexample } => {
                        failed += 1;
                        let cex_str = counterexample.as_ref().map(|c| c.to_string());
                        (
                            "failed".to_string(),
                            solver.to_string(),
                            *time_ms,
                            cex_str,
                            counterexample.clone(),
                            None,
                        )
                    }
                    VerificationResult::Unknown { solver, time_ms, reason } => {
                        if has_runtime_check(sess, &vc.kind) {
                            runtime_checked += 1;
                            (
                                "runtime_checked".to_string(),
                                solver.to_string(),
                                *time_ms,
                                None,
                                None,
                                Some(reason.clone()),
                            )
                        } else {
                            unknown += 1;
                            (
                                "unknown".to_string(),
                                solver.to_string(),
                                *time_ms,
                                None,
                                None,
                                Some(reason.clone()),
                            )
                        }
                    }
                    VerificationResult::Timeout { solver, timeout_ms } => {
                        if has_runtime_check(sess, &vc.kind) {
                            runtime_checked += 1;
                            (
                                "runtime_checked".to_string(),
                                solver.to_string(),
                                *timeout_ms,
                                None,
                                None,
                                Some("solver timed out".to_string()),
                            )
                        } else {
                            unknown += 1;
                            (
                                "timeout".to_string(),
                                solver.to_string(),
                                *timeout_ms,
                                None,
                                None,
                                Some("solver timed out".to_string()),
                            )
                        }
                    }
                    _ => {
                        unknown += 1;
                        (
                            "unknown".to_string(),
                            result.solver_name().to_string(),
                            result.time_ms(),
                            None,
                            None,
                            Some("unsupported verification result variant".to_string()),
                        )
                    }
                };
            TransportObligationResult {
                kind: tag,
                description: desc,
                location: Some(vc.location.clone()),
                outcome,
                solver,
                time_ms,
                counterexample,
                counterexample_model,
                reason,
            }
        })
        .collect()
}

/// tRust #542: Emit structured JSON transport line for a function's verification results.
///
/// Writes a single `TRUST_JSON:{"type":"function_result",...}` line to stderr.
/// This is consumed by cargo-trust and trust-driver for programmatic access
/// to verification results without fragile text parsing of compiler diagnostics.
fn emit_transport_json(func_path: &str, obligation_results: &[TransportObligationResult]) {
    let mut proved: usize = 0;
    let mut failed: usize = 0;
    let mut unknown: usize = 0;
    let mut runtime_checked: usize = 0;

    for result in obligation_results {
        match result.outcome.as_str() {
            "proved" => proved += 1,
            "failed" => failed += 1,
            "runtime_checked" => runtime_checked += 1,
            "unknown" | "timeout" => unknown += 1,
            _ => unknown += 1,
        }
    }

    let total = proved + failed + unknown + runtime_checked;
    let msg = TransportMessage::FunctionResult(FunctionTransportResult {
        function: func_path.to_string(),
        results: obligation_results.to_vec(),
        proved,
        failed,
        unknown,
        runtime_checked,
        total,
    });

    // tRust: Serialize and emit as a single line. Best-effort — serialization
    // failure is non-fatal since text diagnostics are still emitted.
    if let Ok(json) = serde_json::to_string(&msg) {
        eprintln!("{TRANSPORT_PREFIX}{json}");
    }
}

/// tRust: Returns true when the generated program retains a corresponding runtime check.
///
/// This is the incremental step toward #22: when static proof fails for an obligation
/// that Rust already guards dynamically, we classify it as `RUNTIME-CHECKED` instead
/// of leaving it as a bare UNKNOWN/TIMEOUT.
fn has_runtime_check(sess: &Session, kind: &VcKind) -> bool {
    runtime_check_available(kind, sess.overflow_checks())
}

/// tRust: Pure runtime-check classification helper for unit tests and diagnostics.
fn runtime_check_available(kind: &VcKind, overflow_checks: bool) -> bool {
    kind.has_runtime_fallback(overflow_checks)
}

/// tRust: Human-readable note explaining the runtime fallback.
fn runtime_check_note(kind: &VcKind) -> &'static str {
    match kind {
        VcKind::ArithmeticOverflow { .. }
        | VcKind::ShiftOverflow { .. }
        | VcKind::NegationOverflow { .. } => {
            "compiler retained the existing overflow check because the proof is not yet static"
        }
        VcKind::DivisionByZero | VcKind::RemainderByZero => {
            "compiler retained the existing division-by-zero check because the proof is not yet static"
        }
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
            "compiler retained the existing bounds check because the proof is not yet static"
        }
        VcKind::Assertion { .. } => {
            "compiler retained the existing assertion because the proof is not yet static"
        }
        VcKind::Unreachable => {
            "compiler retained the existing unreachable trap because the proof is not yet static"
        }
        VcKind::FloatDivisionByZero | VcKind::FloatOverflowToInfinity { .. } => {
            "floating-point operations do not trap at runtime; no dynamic fallback exists"
        }
        VcKind::CastOverflow { .. }
        | VcKind::Precondition { .. }
        | VcKind::Postcondition
        | VcKind::DeadState { .. }
        | VcKind::Deadlock
        | VcKind::Temporal { .. }
        | VcKind::Liveness { .. }
        | VcKind::Fairness { .. }
        | VcKind::TaintViolation { .. }
        | VcKind::RefinementViolation { .. }
        | VcKind::ResilienceViolation { .. }
        | VcKind::ProtocolViolation { .. }
        | VcKind::NonTermination { .. } => {
            "no runtime-check fallback is available for this obligation kind"
        }
        _ => "no runtime-check fallback is available for this obligation kind",
    }
}

/// tRust: Format a VcKind into a short tag for bracketed display.
fn format_vc_kind(kind: &VcKind) -> &'static str {
    match kind {
        VcKind::ArithmeticOverflow { op, .. } => match op {
            BinOp::Add => "overflow:add",
            BinOp::Sub => "overflow:sub",
            BinOp::Mul => "overflow:mul",
            _ => "overflow",
        },
        VcKind::ShiftOverflow { op, .. } => match op {
            BinOp::Shl => "shift:left",
            BinOp::Shr => "shift:right",
            _ => "shift",
        },
        VcKind::DivisionByZero => "divzero",
        VcKind::RemainderByZero => "remzero",
        VcKind::FloatDivisionByZero => "float_division_by_zero",
        VcKind::FloatOverflowToInfinity { .. } => "float_overflow_to_infinity",
        VcKind::IndexOutOfBounds => "bounds",
        VcKind::SliceBoundsCheck => "slice",
        VcKind::Assertion { .. } => "assert",
        VcKind::Precondition { .. } => "precond",
        VcKind::Postcondition => "postcond",
        VcKind::Unreachable => "unreach",
        VcKind::DeadState { .. } => "deadstate",
        VcKind::Deadlock => "deadlock",
        VcKind::Temporal { .. } => "temporal",
        VcKind::CastOverflow { .. } => "cast",
        VcKind::NegationOverflow { .. } => "negation",
        VcKind::Liveness { .. } => "liveness",
        VcKind::Fairness { .. } => "fairness",
        VcKind::TaintViolation { .. } => "taint",
        VcKind::RefinementViolation { .. } => "refinement",
        VcKind::ResilienceViolation { .. } => "resilience",
        VcKind::ProtocolViolation { .. } => "protocol",
        VcKind::NonTermination { .. } => "termination",
        _ => "unknown",
    }
}

// ---------------------------------------------------------------------------
// tRust: VC + VerificationResult -> TrustProofResults conversion (#35)
//
// Bridges the trust-types verification IR to the compiler-internal
// TrustProofResults type that will be stored in the query system.
// ---------------------------------------------------------------------------

/// tRust: Build compiler-internal TrustProofResults from verification pipeline output.
///
/// Creates one TrustDisposition per (VC, result) pair, computes a 128-bit
/// Fingerprint for each obligation (structural hash of VC kind + function + index),
/// and aggregates a TrustFunctionSummary with counts per status.
///
/// The returned TrustProofResults is ready for storage in the query system
/// (pending #32 query registration).
fn build_proof_results(
    sess: &Session,
    results: &[(VerificationCondition, VerificationResult)],
    fallback_vcs: &[VerificationCondition],
) -> TrustProofResults {
    // tRust: Build parallel IndexVec<ObligationId, _> for dispositions and fingerprints.
    let mut dispositions: IndexVec<ObligationId, TrustDisposition> = IndexVec::new();
    let mut fingerprints: IndexVec<ObligationId, Fingerprint> = IndexVec::new();

    // tRust: Summary counters.
    let mut trusted: u32 = 0;
    let mut certified: u32 = 0;
    let mut failed: u32 = 0;
    let mut unknown: u32 = 0;
    let mut runtime_checked: u32 = 0;
    let mut max_level = TrustProofLevel::None;

    // tRust: If results are available (trust-router ran), use paired (VC, result).
    // Otherwise fall back to VCs-only with Unknown status (no solver ran yet).
    if !results.is_empty() {
        for (idx, (vc, result)) in results.iter().enumerate() {
            let kind = convert_vc_kind(&vc.kind);
            let (status, strength) = convert_result(sess, &vc.kind, result);
            let is_certified = matches!(status, TrustStatus::Certified);

            let disposition = TrustDisposition { kind, status, strength, certified: is_certified };

            dispositions.push(disposition);
            fingerprints.push(compute_obligation_fingerprint(idx, &vc.kind, vc.function.as_str()));

            // tRust: Accumulate summary counts.
            match status {
                TrustStatus::Trusted => trusted += 1,
                TrustStatus::Certified => certified += 1,
                TrustStatus::Failed => failed += 1,
                TrustStatus::Unknown | TrustStatus::Timeout => unknown += 1,
                TrustStatus::RuntimeChecked => runtime_checked += 1,
            }

            // tRust: Track max proof level from VC kind.
            let level = convert_proof_level(&vc.kind);
            if level > max_level {
                max_level = level;
            }
        }
    } else {
        // tRust: No solver results — create Unknown dispositions for all VCs.
        for (idx, vc) in fallback_vcs.iter().enumerate() {
            let kind = convert_vc_kind(&vc.kind);
            let disposition = TrustDisposition {
                kind,
                status: TrustStatus::Unknown,
                strength: TrustProofStrength::None,
                certified: false,
            };

            dispositions.push(disposition);
            fingerprints.push(compute_obligation_fingerprint(idx, &vc.kind, vc.function.as_str()));
            unknown += 1;

            let level = convert_proof_level(&vc.kind);
            if level > max_level {
                max_level = level;
            }
        }
    }

    let total = dispositions.len() as u32;

    let summary = TrustFunctionSummary {
        total,
        trusted,
        certified,
        failed,
        unknown,
        runtime_checked,
        max_level,
    };

    TrustProofResults { dispositions, fingerprints, summary }
}

fn build_proof_telemetry(
    sess: &Session,
    results: &[(VerificationCondition, VerificationResult)],
) -> TrustProofTelemetry {
    let mut details: IndexVec<ObligationId, TrustObligationDetail> = IndexVec::new();

    for (vc, result) in results.iter() {
        let (solver, time_ms, counterexample, runtime_fallback) = match result {
            VerificationResult::Proved { solver, time_ms, .. } => {
                (solver.as_str(), *time_ms, None, None)
            }
            VerificationResult::Failed { solver, time_ms, counterexample } => {
                (solver.as_str(), *time_ms, counterexample.as_ref(), None)
            }
            VerificationResult::Unknown { solver, time_ms, reason } => {
                let fallback =
                    runtime_fallback_for(sess, &vc.kind, RuntimeFallbackOutcome::Unknown, reason);
                (solver.as_str(), *time_ms, None, fallback)
            }
            VerificationResult::Timeout { solver, timeout_ms } => {
                let fallback = runtime_fallback_for(
                    sess,
                    &vc.kind,
                    RuntimeFallbackOutcome::Timeout,
                    "solver timed out before proving the obligation",
                );
                (solver.as_str(), *timeout_ms, None, fallback)
            }
            _ => (
                result.solver_name(),
                result.time_ms(),
                None,
                runtime_fallback_for(
                    sess,
                    &vc.kind,
                    RuntimeFallbackOutcome::Unknown,
                    "unsupported verification result variant",
                ),
            ),
        };

        details.push(TrustObligationDetail {
            solver: Symbol::intern(solver.as_str()),
            time_us: time_ms.saturating_mul(1_000),
            counterexample: counterexample
                .map(|cex| {
                    cex.assignments
                        .iter()
                        .map(|(name, value)| {
                            (Symbol::intern(name), encode_counterexample_value(value))
                        })
                        .collect()
                })
                .unwrap_or_default(),
            runtime_fallback,
        });
    }

    TrustProofTelemetry { details }
}

enum RuntimeFallbackOutcome {
    Unknown,
    Timeout,
}

fn runtime_fallback_for(
    sess: &Session,
    kind: &VcKind,
    outcome: RuntimeFallbackOutcome,
    reason: &str,
) -> Option<TrustRuntimeFallback> {
    if !has_runtime_check(sess, kind) {
        return None;
    }

    Some(runtime_fallback_detail(outcome, reason))
}

fn runtime_fallback_detail(outcome: RuntimeFallbackOutcome, reason: &str) -> TrustRuntimeFallback {
    let (fallback_reason, note) = match outcome {
        RuntimeFallbackOutcome::Unknown => {
            (TrustRuntimeFallbackReason::Unknown, format!("solver returned unknown: {reason}"))
        }
        RuntimeFallbackOutcome::Timeout => {
            (TrustRuntimeFallbackReason::Timeout, reason.to_string())
        }
    };

    TrustRuntimeFallback { reason: fallback_reason, note }
}

/// tRust: Convert a trust-types VcKind to the compiler-internal TrustObligationKind.
///
/// Maps the serde-friendly VcKind variants to the Copy/HashStable/TyEncodable
/// TrustObligationKind used in the query system.
fn convert_vc_kind(kind: &VcKind) -> TrustObligationKind {
    match kind {
        VcKind::ArithmeticOverflow { op, .. } => {
            TrustObligationKind::ArithmeticOverflow(convert_binop(op))
        }
        VcKind::FloatOverflowToInfinity { op, .. } => {
            TrustObligationKind::ArithmeticOverflow(convert_binop(op))
        }
        VcKind::ShiftOverflow { .. } => TrustObligationKind::ShiftOverflow,
        VcKind::DivisionByZero => TrustObligationKind::DivisionByZero,
        VcKind::FloatDivisionByZero => TrustObligationKind::DivisionByZero,
        VcKind::RemainderByZero => TrustObligationKind::RemainderByZero,
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
            TrustObligationKind::IndexOutOfBounds
        }
        VcKind::Assertion { .. } => TrustObligationKind::Assertion,
        VcKind::Precondition { .. } => TrustObligationKind::Precondition,
        VcKind::Postcondition => TrustObligationKind::Postcondition,
        VcKind::CastOverflow { .. } => TrustObligationKind::CastOverflow,
        VcKind::NegationOverflow { .. } => TrustObligationKind::NegationOverflow,
        VcKind::Unreachable => TrustObligationKind::Unreachable,
        VcKind::DeadState { .. } | VcKind::Deadlock => TrustObligationKind::Deadlock,
        VcKind::Temporal { .. } => TrustObligationKind::Temporal,
        VcKind::Liveness { .. } | VcKind::Fairness { .. } => TrustObligationKind::Liveness,
        VcKind::TaintViolation { .. } => TrustObligationKind::TaintViolation,
        VcKind::RefinementViolation { .. } => TrustObligationKind::RefinementViolation,
        VcKind::ResilienceViolation { .. } => TrustObligationKind::ResilienceViolation,
        VcKind::ProtocolViolation { .. } => TrustObligationKind::ProtocolViolation,
        VcKind::NonTermination { .. } => TrustObligationKind::NonTermination,
        _ => TrustObligationKind::Assertion,
    }
}

/// tRust: Convert a trust-types BinOp to the compiler-internal TrustBinOp.
fn convert_binop(op: &BinOp) -> TrustBinOp {
    match op {
        BinOp::Add => TrustBinOp::Add,
        BinOp::Sub => TrustBinOp::Sub,
        BinOp::Mul => TrustBinOp::Mul,
        BinOp::Div => TrustBinOp::Div,
        BinOp::Rem => TrustBinOp::Rem,
        BinOp::Shl => TrustBinOp::Shl,
        BinOp::Shr => TrustBinOp::Shr,
        // tRust: Comparison and bitwise ops don't produce arithmetic overflow.
        // Map to Add as a conservative fallback — these shouldn't appear in
        // ArithmeticOverflow VCs, but we handle them defensively.
        BinOp::Eq
        | BinOp::Ne
        | BinOp::Lt
        | BinOp::Le
        | BinOp::Gt
        | BinOp::Ge
        | BinOp::BitAnd
        | BinOp::BitOr
        | BinOp::BitXor => TrustBinOp::Add,
        _ => TrustBinOp::Add,
    }
}

/// tRust: Convert a VerificationResult to (TrustStatus, TrustProofStrength).
///
/// Maps the solver-returned result to the two-level trust model:
/// - Proved + SmtUnsat -> (Trusted, SmtUnsat)
/// - Proved + Constructive -> (Trusted, Constructive) — NOT Certified until lean5 checks it
/// - Failed -> (Failed, None)
/// - Unknown/Timeout -> (Unknown/Timeout, None)
fn convert_result(
    sess: &Session,
    kind: &VcKind,
    result: &VerificationResult,
) -> (TrustStatus, TrustProofStrength) {
    match result {
        VerificationResult::Proved { strength, .. } => {
            let trust_strength = convert_proof_strength(strength);
            // tRust: All proved results start as Trusted. Only lean5 kernel
            // verification can promote to Certified (not implemented yet — #24).
            (TrustStatus::Trusted, trust_strength)
        }
        VerificationResult::Failed { .. } => (TrustStatus::Failed, TrustProofStrength::None),
        VerificationResult::Unknown { .. } => {
            if has_runtime_check(sess, kind) {
                (TrustStatus::RuntimeChecked, TrustProofStrength::None)
            } else {
                (TrustStatus::Unknown, TrustProofStrength::None)
            }
        }
        VerificationResult::Timeout { .. } => {
            if has_runtime_check(sess, kind) {
                (TrustStatus::RuntimeChecked, TrustProofStrength::None)
            } else {
                (TrustStatus::Timeout, TrustProofStrength::None)
            }
        }
        _ => (TrustStatus::Unknown, TrustProofStrength::None),
    }
}

/// tRust: Convert a trust-types ProofStrength to compiler-internal TrustProofStrength.
fn convert_proof_strength(strength: &ProofStrength) -> TrustProofStrength {
    match &strength.reasoning {
        ReasoningKind::Smt => TrustProofStrength::SmtUnsat,
        ReasoningKind::BoundedModelCheck { depth } => {
            TrustProofStrength::Bounded { depth: (*depth).min(u32::MAX as u64) as u32 }
        }
        ReasoningKind::Inductive => TrustProofStrength::Inductive,
        ReasoningKind::Deductive => TrustProofStrength::Deductive,
        ReasoningKind::Constructive => TrustProofStrength::Constructive,
        ReasoningKind::Pdr | ReasoningKind::ChcSpacer => TrustProofStrength::Inductive,
        ReasoningKind::AbstractInterpretation => TrustProofStrength::SmtUnsat,
        _ => TrustProofStrength::SmtUnsat,
    }
}

/// tRust: Convert a VcKind to TrustProofLevel (L0/L1/L2).
///
/// Mirrors VcKind::proof_level() but returns the compiler-internal enum.
fn convert_proof_level(kind: &VcKind) -> TrustProofLevel {
    match kind.proof_level() {
        trust_types::ProofLevel::L0Safety => TrustProofLevel::L0Safety,
        trust_types::ProofLevel::L1Functional => TrustProofLevel::L1Functional,
        trust_types::ProofLevel::L2Domain => TrustProofLevel::L2Domain,
        _ => TrustProofLevel::L2Domain,
    }
}

/// tRust: Compute a 128-bit Fingerprint for an obligation.
///
/// The fingerprint is a structural hash over the obligation's index, VC kind
/// (as a tag string), and function name. This provides a stable identity that
/// does NOT depend on MIR locations (which shift during optimization).
///
/// NOTE: This is a scaffold implementation using DefaultHasher. The production
/// version should use StableHasher for cross-compilation determinism.
/// For now, within a single compilation session, DefaultHasher is sufficient.
fn compute_obligation_fingerprint(index: usize, kind: &VcKind, function: &str) -> Fingerprint {
    // tRust: Hash the structural identity of this obligation.
    let mut hasher = DefaultHasher::new();
    index.hash(&mut hasher);
    format_vc_kind(kind).hash(&mut hasher);
    function.hash(&mut hasher);
    let h1 = hasher.finish();

    // tRust: Second independent hash for the 128-bit fingerprint.
    // Use a different seed by hashing in reverse order with a discriminant.
    let mut hasher2 = DefaultHasher::new();
    0xDEAD_BEEF_u64.hash(&mut hasher2);
    function.hash(&mut hasher2);
    format_vc_kind(kind).hash(&mut hasher2);
    index.hash(&mut hasher2);
    let h2 = hasher2.finish();

    Fingerprint::new(h1, h2)
}

fn encode_counterexample_value(value: &CounterexampleValue) -> i128 {
    match value {
        CounterexampleValue::Bool(value) => i128::from(*value),
        CounterexampleValue::Int(value) => *value,
        CounterexampleValue::Uint(value) => (*value).min(i128::MAX as u128) as i128,
        CounterexampleValue::Float(value) => i128::from(value.to_bits()),
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use rustc_index::IndexVec;
    use rustc_middle::mir::trust_proof::{TrustObligationDetail, TrustRuntimeFallbackReason};

    use super::*;

    fn test_vc(line_start: u32) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: Symbol::intern("test::f"),
            location: trust_types::SourceSpan {
                file: "test.rs".to_string(),
                line_start,
                col_start: 1,
                line_end: line_start,
                col_end: 5,
            },
            formula: trust_types::Formula::Bool(true),
            contract_metadata: None,
        }
    }

    #[test]
    fn unknown_overflow_is_runtime_checked_when_overflow_checks_are_on() {
        let kind = VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (trust_types::Ty::usize(), trust_types::Ty::usize()),
        };
        assert!(runtime_check_available(&kind, true));
    }

    #[test]
    fn unknown_overflow_stays_unknown_when_overflow_checks_are_off() {
        let kind = VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (trust_types::Ty::usize(), trust_types::Ty::usize()),
        };
        assert!(!runtime_check_available(&kind, false));
    }

    #[test]
    fn bounds_unknown_is_runtime_checked_even_without_overflow_checks() {
        assert!(runtime_check_available(&VcKind::IndexOutOfBounds, false));
    }

    #[test]
    fn precondition_unknown_has_no_runtime_fallback() {
        assert!(!runtime_check_available(
            &VcKind::Precondition { callee: "callee".to_string() },
            true,
        ));
    }

    #[test]
    fn float_unknown_has_no_runtime_fallback() {
        assert!(!runtime_check_available(&VcKind::FloatDivisionByZero, true));
        assert!(!runtime_check_available(
            &VcKind::FloatOverflowToInfinity {
                op: BinOp::Add,
                operand_ty: trust_types::Ty::Float { width: 64 },
            },
            true,
        ));
    }

    #[test]
    fn float_runtime_check_note_explains_no_dynamic_fallback() {
        assert_eq!(
            runtime_check_note(&VcKind::FloatDivisionByZero),
            "floating-point operations do not trap at runtime; no dynamic fallback exists",
        );
    }

    #[test]
    fn float_vc_tags_are_not_unknown() {
        assert_eq!(format_vc_kind(&VcKind::FloatDivisionByZero), "float_division_by_zero");
        assert_eq!(
            format_vc_kind(&VcKind::FloatOverflowToInfinity {
                op: BinOp::Add,
                operand_ty: trust_types::Ty::Float { width: 64 },
            }),
            "float_overflow_to_infinity",
        );
    }

    #[test]
    fn float_vc_kinds_map_to_existing_internal_obligation_buckets() {
        assert_eq!(
            convert_vc_kind(&VcKind::FloatDivisionByZero),
            TrustObligationKind::DivisionByZero,
        );
        assert_eq!(
            convert_vc_kind(&VcKind::FloatOverflowToInfinity {
                op: BinOp::Add,
                operand_ty: trust_types::Ty::Float { width: 64 },
            }),
            TrustObligationKind::ArithmeticOverflow(TrustBinOp::Add),
        );
    }

    #[test]
    fn telemetry_carries_runtime_fallback_metadata() {
        let mut details: IndexVec<ObligationId, TrustObligationDetail> = IndexVec::new();
        details.push(TrustObligationDetail {
            solver: Symbol::intern("mock"),
            time_us: 5_000,
            counterexample: vec![],
            runtime_fallback: Some(runtime_fallback_detail(
                RuntimeFallbackOutcome::Unknown,
                "solver could not decide",
            )),
        });
        details.push(TrustObligationDetail {
            solver: Symbol::intern("mock"),
            time_us: 7_000,
            counterexample: vec![],
            runtime_fallback: None,
        });
        let telemetry = TrustProofTelemetry { details };
        assert_eq!(telemetry.runtime_checked_count(), 1);

        let mut runtime_checked = telemetry.runtime_checked_details();
        let (obligation, detail) = runtime_checked.next().expect("runtime-checked detail");
        assert_eq!(obligation.index(), 0);
        assert!(detail.is_runtime_checked());

        let fallback = detail.runtime_fallback().expect("runtime fallback metadata");
        assert_eq!(fallback.reason, TrustRuntimeFallbackReason::Unknown);
        assert!(fallback.note.contains("solver returned unknown"));

        let second = telemetry.detail(obligation).expect("detail lookup");
        assert_eq!(second.solver, detail.solver);
        assert!(runtime_checked.next().is_none());
        assert!(telemetry.detail(obligation).unwrap().runtime_fallback().is_some());
    }

    #[test]
    fn runtime_fallback_detail_uses_timeout_reason() {
        let fallback = runtime_fallback_detail(RuntimeFallbackOutcome::Timeout, "solver timed out");
        assert_eq!(fallback.reason, TrustRuntimeFallbackReason::Timeout);
        assert_eq!(fallback.note, "solver timed out");
    }

    #[test]
    fn telemetry_ignores_non_runtime_checked_obligations() {
        let mut details: IndexVec<ObligationId, TrustObligationDetail> = IndexVec::new();
        details.push(TrustObligationDetail {
            solver: Symbol::intern("mock"),
            time_us: 12_000,
            counterexample: vec![],
            runtime_fallback: None,
        });
        let telemetry = TrustProofTelemetry { details };
        assert_eq!(telemetry.runtime_checked_count(), 0);
        assert!(telemetry.runtime_checked_details().next().is_none());
        assert!(telemetry.details[ObligationId::from_usize(0)].runtime_fallback().is_none());
    }

    #[test]
    fn dedupe_exact_vcs_drops_duplicate_slot() {
        let vc = test_vc(10);
        let deduped = dedupe_exact_vcs(vec![vc.clone(), vc]);
        assert_eq!(deduped.len(), 1);
    }

    #[test]
    fn dedupe_exact_vcs_preserves_distinct_spans() {
        let deduped = dedupe_exact_vcs(vec![test_vc(10), test_vc(11)]);
        assert_eq!(deduped.len(), 2);
    }

    #[test]
    fn dedupe_exact_results_drops_duplicate_outcome() {
        let vc = test_vc(10);
        let result = VerificationResult::Unknown {
            solver: Symbol::intern("mock"),
            time_ms: 3,
            reason: "duplicate".to_string(),
        };
        let deduped = dedupe_exact_results(vec![(vc.clone(), result.clone()), (vc, result)]);
        assert_eq!(deduped.len(), 1);
    }

    // tRust #538: Tests for global verification status map.

    #[test]
    fn store_and_query_proved_status() {
        let summary = TrustFunctionSummary {
            total: 3,
            trusted: 3,
            certified: 0,
            failed: 0,
            unknown: 0,
            runtime_checked: 0,
            max_level: TrustProofLevel::None,
        };
        store_verification_status("test::store_proved", &summary);
        let status = trust_verification_status("test::store_proved");
        assert_eq!(status, Some(VerificationStatus::Proved));
    }

    #[test]
    fn store_and_query_failed_status() {
        let summary = TrustFunctionSummary {
            total: 3,
            trusted: 1,
            certified: 0,
            failed: 2,
            unknown: 0,
            runtime_checked: 0,
            max_level: TrustProofLevel::None,
        };
        store_verification_status("test::store_failed", &summary);
        assert_eq!(
            trust_verification_status("test::store_failed"),
            Some(VerificationStatus::Failed),
        );
    }

    #[test]
    fn store_and_query_unknown_status() {
        let summary = TrustFunctionSummary {
            total: 3,
            trusted: 1,
            certified: 0,
            failed: 0,
            unknown: 2,
            runtime_checked: 0,
            max_level: TrustProofLevel::None,
        };
        store_verification_status("test::store_unknown", &summary);
        assert_eq!(
            trust_verification_status("test::store_unknown"),
            Some(VerificationStatus::Unknown),
        );
    }

    #[test]
    fn store_and_query_runtime_checked_status() {
        let summary = TrustFunctionSummary {
            total: 3,
            trusted: 1,
            certified: 0,
            failed: 0,
            unknown: 0,
            runtime_checked: 2,
            max_level: TrustProofLevel::None,
        };
        store_verification_status("test::store_runtime_checked", &summary);
        assert_eq!(
            trust_verification_status("test::store_runtime_checked"),
            Some(VerificationStatus::RuntimeChecked),
        );
    }

    #[test]
    fn query_unknown_function_returns_none() {
        assert_eq!(trust_verification_status("test::never_verified_function"), None);
    }
}
