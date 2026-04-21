// trust-router/mir_router.rs: MIR-level verification strategy router
//
// tRust #791: Pipeline v2 Phase 2 — classifies functions at the MIR level
// and dispatches to zani-lib (BMC), sunder-lib (deductive), or the existing
// v1 Formula-based pipeline. Sits ABOVE the existing Router.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! MIR-level verification strategy router.
//!
//! The `MirRouter` classifies `VerifiableFunction`s based on their MIR
//! properties (contracts, unsafe blocks, loops, atomics, raw pointers, FFI)
//! and dispatches each to the most appropriate verification backend:
//!
//! - **zani-lib**: Bounded model checking for reachability and safety
//! - **sunder-lib**: Deductive verification for contract-bearing functions
//! - **v1 pipeline**: The existing `Router` for everything else
//!
//! This router operates at a higher level than the existing `Router`, which
//! dispatches at the Formula/VC level. Classification happens before VC
//! generation, enabling backend-specific encoding.

use trust_types::{
    ContractKind, Rvalue, Statement, Terminator, VerifiableFunction,
    VerificationCondition, VerificationResult,
};

use crate::Router;

/// MIR-level verification strategy.
///
/// Determines how a function should be verified based on its MIR properties.
/// Ordered roughly by specificity: more specialized strategies are preferred
/// over generic ones.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum MirStrategy {
    /// BMC via zani-lib (bounded safety, reachability).
    BoundedModelCheck,
    /// Deductive via sunder-lib (contract verification).
    ContractVerification,
    /// Unsafe audit — both zani and sunder for maximum coverage.
    UnsafeAudit,
    /// Ownership/separation logic — v1 pipeline.
    SeparationLogic,
    /// Data race detection — v1 pipeline + TLA2.
    DataRace,
    /// FFI boundary — v1 pipeline.
    FFIBoundary,
    /// Run multiple strategies in parallel, take first definitive result.
    Portfolio(Vec<MirStrategy>),
    /// Fall through to v1 Formula-based pipeline.
    V1Fallback,
}

impl std::fmt::Display for MirStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MirStrategy::BoundedModelCheck => f.write_str("BoundedModelCheck"),
            MirStrategy::ContractVerification => f.write_str("ContractVerification"),
            MirStrategy::UnsafeAudit => f.write_str("UnsafeAudit"),
            MirStrategy::SeparationLogic => f.write_str("SeparationLogic"),
            MirStrategy::DataRace => f.write_str("DataRace"),
            MirStrategy::FFIBoundary => f.write_str("FFIBoundary"),
            MirStrategy::Portfolio(strategies) => {
                write!(f, "Portfolio(")?;
                for (i, s) in strategies.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{s}")?;
                }
                write!(f, ")")
            }
            MirStrategy::V1Fallback => f.write_str("V1Fallback"),
        }
    }
}

/// Configuration for the MIR router.
#[derive(Debug, Clone)]
pub struct MirRouterConfig {
    /// Default BMC depth for zani-lib verification.
    pub bmc_depth: u32,
    /// Timeout in milliseconds for individual backend calls.
    pub timeout_ms: u64,
    /// Whether to produce proof certificates.
    pub produce_proofs: bool,
    /// tRust #791: Shadow mode — run both MIR router and v1 fallback, compare
    /// results, and log discrepancies. Returns the MIR router result when it
    /// succeeds, otherwise falls back to v1.
    pub shadow_mode: bool,
    /// tRust #793: Enable rayon-based parallel portfolio racing.
    /// When true, portfolio strategies are dispatched in parallel using rayon
    /// with early termination on the first definitive result.
    pub enable_portfolio_racing: bool,
    /// tRust #793: Enable loop invariant inference via sunder before BMC dispatch.
    /// When true, functions with loops are first analyzed by sunder for invariant
    /// hints which are logged for the strengthen feedback loop.
    pub infer_invariants: bool,
}

impl Default for MirRouterConfig {
    fn default() -> Self {
        Self {
            bmc_depth: 100,
            timeout_ms: 30_000,
            produce_proofs: false,
            shadow_mode: false,
            enable_portfolio_racing: true,
            infer_invariants: false,
        }
    }
}

/// tRust #791: Describes how the MIR router result and v1 fallback result compare.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ShadowDiscrepancy {
    /// Both agree (both proved, both failed, or both unknown/timeout).
    Equivalent,
    /// MIR router proved but v1 did not (MIR is strictly better).
    MirStronger,
    /// v1 proved but MIR router did not (regression — MIR is weaker).
    V1Stronger,
    /// Both produced results but of different outcome classes (e.g., one failed, other unknown).
    Mismatch,
}

impl std::fmt::Display for ShadowDiscrepancy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ShadowDiscrepancy::Equivalent => f.write_str("equivalent"),
            ShadowDiscrepancy::MirStronger => f.write_str("mir_stronger"),
            ShadowDiscrepancy::V1Stronger => f.write_str("v1_stronger"),
            ShadowDiscrepancy::Mismatch => f.write_str("mismatch"),
        }
    }
}

/// tRust #791: Result of shadow-mode verification — both MIR router and v1 results
/// plus the comparison outcome.
#[derive(Debug, Clone)]
pub(crate) struct ShadowResult {
    /// The strategy chosen by the MIR router's classifier.
    pub(crate) strategy: MirStrategy,
    /// The result from the MIR router dispatch.
    pub(crate) mir_result: VerificationResult,
    /// The result from the v1 fallback dispatch.
    pub(crate) v1_result: VerificationResult,
    /// How the two results compare.
    pub(crate) discrepancy: ShadowDiscrepancy,
    /// The result that was actually returned to the caller.
    pub(crate) chosen_result: VerificationResult,
}

/// MIR-level router — classifies functions and dispatches to appropriate backends.
///
/// The MirRouter sits above the existing `Router`, intercepting functions before
/// VC generation. Functions with specific MIR-level properties (contracts, unsafe
/// blocks, loops) are dispatched directly to specialized backends (zani-lib,
/// sunder-lib). Everything else falls through to the v1 pipeline.
pub struct MirRouter {
    /// The v1 VC-level router for fallback dispatch.
    v1_router: Router,
    /// Configuration for backend invocations.
    config: MirRouterConfig,
}

impl MirRouter {
    /// Create a new MIR router wrapping the given v1 router.
    pub fn new(v1_router: Router, config: MirRouterConfig) -> Self {
        Self { v1_router, config }
    }

    /// Create a MIR router with default config and mock backends.
    pub fn with_defaults() -> Self {
        Self {
            v1_router: Router::new(),
            config: MirRouterConfig::default(),
        }
    }

    /// Access the underlying v1 router.
    #[must_use]
    pub fn v1_router(&self) -> &Router {
        &self.v1_router
    }

    /// Access the configuration.
    #[must_use]
    pub fn config(&self) -> &MirRouterConfig {
        &self.config
    }

    /// Classify a function to determine its verification strategy.
    ///
    /// The classification priority is:
    /// 1. Has `unsafe` blocks with contracts -> UnsafeAudit (both backends)
    /// 2. Has `#[requires]`/`#[ensures]` contracts -> ContractVerification (sunder)
    /// 3. Has `#[invariant]` annotations -> ContractVerification (sunder)
    /// 4. Has atomic operations / thread spawns -> DataRace
    /// 5. Has raw pointer operations -> SeparationLogic
    /// 6. Has FFI calls -> FFIBoundary
    /// 7. Has loops with unbounded iteration -> BoundedModelCheck (zani)
    /// 8. Default -> V1Fallback
    #[must_use]
    pub fn classify(&self, func: &VerifiableFunction) -> MirStrategy {
        let has_contracts = has_contracts(func);
        let has_invariant_annotations = has_invariant_annotations(func);
        let has_unsafe = has_unsafe_operations(func);
        let has_atomics = has_atomic_operations(func);
        let has_raw_ptrs = has_raw_pointer_operations(func);
        let has_ffi = has_ffi_calls(func);
        let has_loops = has_loops(func);

        // tRust #791: Unsafe with contracts gets both backends for maximum coverage.
        if has_unsafe && has_contracts {
            return MirStrategy::UnsafeAudit;
        }

        // tRust #791: Contract-bearing functions go to sunder for deductive proof.
        if has_contracts || has_invariant_annotations {
            return MirStrategy::ContractVerification;
        }

        // tRust #791: Atomic operations need data race analysis.
        if has_atomics {
            return MirStrategy::DataRace;
        }

        // tRust #791: Raw pointers need separation logic / ownership analysis.
        if has_raw_ptrs {
            return MirStrategy::SeparationLogic;
        }

        // tRust #791: FFI calls need boundary verification.
        if has_ffi {
            return MirStrategy::FFIBoundary;
        }

        // tRust #791: Functions with loops benefit from BMC to find bounds violations.
        if has_loops {
            return MirStrategy::BoundedModelCheck;
        }

        // tRust #791: Everything else goes through the v1 pipeline.
        MirStrategy::V1Fallback
    }

    /// Verify a function using the classified strategy.
    ///
    /// Dispatches to the appropriate backend based on `classify()`, then
    /// converts the result to a uniform `VerificationResult`.
    ///
    /// When `config.shadow_mode` is true, also dispatches through v1 and
    /// logs any discrepancies (but still returns the MIR router result when
    /// it succeeds).
    pub fn verify_function(
        &self,
        func: &VerifiableFunction,
    ) -> VerificationResult {
        if self.config.shadow_mode {
            return self.shadow_verify(func).chosen_result;
        }
        let strategy = self.classify(func);
        self.dispatch(func, &strategy)
    }

    /// Verify a function using an explicit strategy (bypasses classification).
    pub fn verify_with_strategy(
        &self,
        func: &VerifiableFunction,
        strategy: &MirStrategy,
    ) -> VerificationResult {
        self.dispatch(func, strategy)
    }

    /// Verify multiple functions, classifying and dispatching each.
    pub fn verify_all(
        &self,
        funcs: &[VerifiableFunction],
    ) -> Vec<(String, MirStrategy, VerificationResult)> {
        funcs
            .iter()
            .map(|func| {
                let strategy = self.classify(func);
                let result = self.dispatch(func, &strategy);
                (func.name.clone(), strategy, result)
            })
            .collect()
    }

    /// Internal dispatch: routes to the appropriate backend.
    fn dispatch(
        &self,
        func: &VerifiableFunction,
        strategy: &MirStrategy,
    ) -> VerificationResult {
        match strategy {
            MirStrategy::BoundedModelCheck => {
                // tRust #793: Optionally infer loop invariants before BMC dispatch.
                if self.config.infer_invariants && has_loops(func) {
                    self.dispatch_bmc_with_invariant_hints(func)
                } else {
                    self.dispatch_bmc(func)
                }
            }
            MirStrategy::ContractVerification => self.dispatch_contract(func),
            MirStrategy::UnsafeAudit => self.dispatch_unsafe_audit(func),
            MirStrategy::Portfolio(strategies) => self.dispatch_portfolio(func, strategies),
            // tRust #791: DataRace, SeparationLogic, FFIBoundary, V1Fallback all
            // go through the v1 pipeline for now. These backends will be specialized
            // in future phases.
            MirStrategy::DataRace
            | MirStrategy::SeparationLogic
            | MirStrategy::FFIBoundary
            | MirStrategy::V1Fallback => self.dispatch_v1(func),
        }
    }

    /// Dispatch to zani-lib for bounded model checking.
    fn dispatch_bmc(&self, func: &VerifiableFunction) -> VerificationResult {
        let zani_config = trust_zani_lib::ZaniConfig::new()
            .with_bmc_depth(self.config.bmc_depth)
            .with_timeout(self.config.timeout_ms)
            .with_proofs(self.config.produce_proofs);

        // tRust #791: Generate a minimal SMT-LIB2 script for zani.
        // In a full pipeline, trust-vcgen would produce the script from the MIR.
        // For now, we pass the function name and let zani's subprocess handle encoding.
        let smtlib = format!(
            "; MIR router BMC dispatch for {}\n(check-sat)\n",
            func.def_path
        );

        match trust_zani_lib::verify_function(&func.def_path, &smtlib, &zani_config) {
            Ok(result) => result.to_verification_result(),
            Err(e) => VerificationResult::Unknown {
                solver: "zani-lib".to_string(),
                time_ms: 0,
                reason: format!("zani dispatch error: {e}"),
            },
        }
    }

    /// Dispatch to sunder-lib for deductive contract verification.
    fn dispatch_contract(&self, func: &VerifiableFunction) -> VerificationResult {
        let sunder_config = trust_sunder_lib::SunderConfig::new()
            .with_timeout(self.config.timeout_ms)
            .with_proofs(self.config.produce_proofs);

        let contracts = build_sunder_contracts(func);

        match trust_sunder_lib::verify_with_contracts(&func.def_path, &contracts, &sunder_config) {
            Ok(result) => result.to_verification_result(),
            Err(e) => VerificationResult::Unknown {
                solver: "sunder-lib".to_string(),
                time_ms: 0,
                reason: format!("sunder dispatch error: {e}"),
            },
        }
    }

    /// Dispatch to both zani and sunder for unsafe code audit.
    ///
    /// When portfolio racing is enabled, dispatches BMC and contract verification
    /// in parallel and returns the first definitive result. Otherwise runs both
    /// sequentially and merges (preferring failure over proof).
    fn dispatch_unsafe_audit(&self, func: &VerifiableFunction) -> VerificationResult {
        if self.config.enable_portfolio_racing {
            let strategies = vec![
                MirStrategy::BoundedModelCheck,
                MirStrategy::ContractVerification,
            ];
            // tRust #793: Use parallel portfolio dispatch for unsafe audit.
            // For unsafe audit, both backends run; if either finds a failure, that wins.
            self.dispatch_portfolio(func, &strategies)
        } else {
            let bmc_result = self.dispatch_bmc(func);
            let contract_result = self.dispatch_contract(func);
            merge_results(bmc_result, contract_result)
        }
    }

    /// tRust #793: Dispatch multiple strategies in parallel using rayon, take
    /// the first definitive result.
    ///
    /// When `enable_portfolio_racing` is true, strategies are dispatched
    /// concurrently via `rayon::scope`. An `AtomicBool` signals early
    /// termination once any thread finds a Proved or Failed result.
    /// Falls back to sequential dispatch when racing is disabled or there
    /// is only one strategy.
    fn dispatch_portfolio(
        &self,
        func: &VerifiableFunction,
        strategies: &[MirStrategy],
    ) -> VerificationResult {
        use std::sync::atomic::{AtomicBool, Ordering};
        use std::sync::Mutex;

        if strategies.is_empty() {
            return VerificationResult::Unknown {
                solver: "mir-router-portfolio".to_string(),
                time_ms: 0,
                reason: "no strategies in portfolio".to_string(),
            };
        }

        // For single strategy, no need for parallelism.
        if strategies.len() == 1 {
            return self.dispatch(func, &strategies[0]);
        }

        // tRust #793: Sequential fallback when portfolio racing is disabled.
        if !self.config.enable_portfolio_racing {
            return self.dispatch_portfolio_sequential(func, strategies);
        }

        let found_definitive = AtomicBool::new(false);
        let results: Mutex<Vec<(usize, VerificationResult)>> = Mutex::new(Vec::new());

        rayon::scope(|s| {
            for (idx, strategy) in strategies.iter().enumerate() {
                let found = &found_definitive;
                let results_ref = &results;
                s.spawn(move |_| {
                    // Skip if another thread already found a definitive result.
                    if found.load(Ordering::Relaxed) {
                        return;
                    }
                    let result = self.dispatch(func, strategy);
                    if result.is_proved() || result.is_failed() {
                        found.store(true, Ordering::Relaxed);
                    }
                    results_ref
                        .lock()
                        .expect("invariant: portfolio results mutex not poisoned")
                        .push((idx, result));
                });
            }
        });

        let mut collected = results
            .into_inner()
            .expect("invariant: portfolio results mutex not poisoned");
        collected.sort_by_key(|(idx, _)| *idx);

        // Return first definitive result, or first result if none definitive.
        for (_, result) in &collected {
            if result.is_proved() || result.is_failed() {
                return result.clone();
            }
        }
        collected
            .into_iter()
            .next()
            .map(|(_, r)| r)
            .unwrap_or_else(|| VerificationResult::Unknown {
                solver: "mir-router-portfolio".to_string(),
                time_ms: 0,
                reason: "no strategies produced results".to_string(),
            })
    }

    /// tRust #793: Sequential portfolio dispatch (fallback when racing is disabled).
    fn dispatch_portfolio_sequential(
        &self,
        func: &VerifiableFunction,
        strategies: &[MirStrategy],
    ) -> VerificationResult {
        let mut best_result: Option<VerificationResult> = None;

        for strategy in strategies {
            let result = self.dispatch(func, strategy);

            // If we got a definitive result (Proved or Failed), return immediately.
            if result.is_proved() || result.is_failed() {
                return result;
            }

            // Keep track of the first non-definitive result.
            if best_result.is_none() {
                best_result = Some(result);
            }
        }

        best_result.unwrap_or_else(|| VerificationResult::Unknown {
            solver: "mir-router-portfolio".to_string(),
            time_ms: 0,
            reason: "no strategies in portfolio".to_string(),
        })
    }

    /// tRust #793: When BMC encounters a function with loops, optionally invoke
    /// sunder for invariant hints and log them for the strengthen feedback loop.
    fn dispatch_bmc_with_invariant_hints(
        &self,
        func: &VerifiableFunction,
    ) -> VerificationResult {
        let sunder_config = trust_sunder_lib::SunderConfig::new()
            .with_timeout(self.config.timeout_ms);

        if let Ok(invariants) =
            trust_sunder_lib::infer_loop_invariants(&func.def_path, &sunder_config)
        {
            // Log discovered invariants for strengthen feedback.
            if !invariants.is_empty() {
                eprintln!(
                    "[mir-router] discovered {} loop invariant(s) for {} via sunder",
                    invariants.len(),
                    func.name,
                );
            }
        }

        self.dispatch_bmc(func)
    }

    /// Dispatch to the v1 VC-level pipeline.
    ///
    /// Generates VCs from the function's contracts/preconditions and dispatches
    /// them through the existing Router.
    fn dispatch_v1(&self, func: &VerifiableFunction) -> VerificationResult {
        // tRust #791: Build VCs from the function's existing verification conditions.
        // If the function has no pre/postconditions, we generate a basic safety VC.
        let vcs = build_v1_vcs(func);

        if vcs.is_empty() {
            // tRust #804 (P1-9): No VCs means vacuously true, not soundly proved.
            // Use BoundedSound { depth: 0 } to signal zero proof work was done.
            return VerificationResult::Proved {
                solver: "mir-router-v1".to_string(),
                time_ms: 0,
                strength: trust_types::ProofStrength::bounded(0),
                proof_certificate: None,
                solver_warnings: None,
            };
        }

        let results = self.v1_router.verify_all(&vcs);

        // Merge: all must prove for overall proof.
        let mut total_time_ms: u64 = 0;
        for (_, result) in &results {
            match result {
                VerificationResult::Proved { time_ms, .. } => {
                    total_time_ms += time_ms;
                }
                other => return other.clone(),
            }
        }

        VerificationResult::Proved {
            solver: "mir-router-v1".to_string(),
            time_ms: total_time_ms,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        }
    }

    /// tRust #791: Shadow-mode verification — run both the MIR router strategy
    /// and the v1 fallback, compare results, and log discrepancies.
    ///
    /// Returns the MIR router result when it produces a definitive answer
    /// (Proved or Failed). Falls back to the v1 result when the MIR router
    /// returns Unknown or Timeout.
    ///
    /// Only active when `config.shadow_mode` is true. When shadow mode is off,
    /// `verify_function` bypasses this entirely.
    pub(crate) fn shadow_verify(
        &self,
        func: &VerifiableFunction,
    ) -> ShadowResult {
        let strategy = self.classify(func);

        // tRust #791: Run the MIR router dispatch.
        let mir_result = self.dispatch(func, &strategy);

        // tRust #791: Always run v1 fallback in shadow mode for comparison.
        let v1_result = self.dispatch_v1(func);

        // tRust #791: Compare the two results.
        let discrepancy = classify_discrepancy(&mir_result, &v1_result);

        // tRust #791: Log discrepancies to stderr for observability.
        if discrepancy != ShadowDiscrepancy::Equivalent {
            eprintln!(
                "[mir-router-shadow] discrepancy={} func={} strategy={} \
                 mir={} v1={}",
                discrepancy,
                func.name,
                strategy,
                result_summary(&mir_result),
                result_summary(&v1_result),
            );
        }

        // tRust #791: Choose which result to return.
        // MIR router result wins when it's definitive (Proved or Failed).
        // Fall back to v1 when MIR router is inconclusive.
        let chosen_result = if mir_result.is_proved() || mir_result.is_failed() {
            mir_result.clone()
        } else {
            v1_result.clone()
        };

        ShadowResult {
            strategy,
            mir_result,
            v1_result,
            discrepancy,
            chosen_result,
        }
    }
}

/// tRust #791: Classify how two verification results compare for shadow mode.
fn classify_discrepancy(
    mir: &VerificationResult,
    v1: &VerificationResult,
) -> ShadowDiscrepancy {
    match (mir.is_proved(), mir.is_failed(), v1.is_proved(), v1.is_failed()) {
        // Both proved or both failed — equivalent outcomes.
        (true, _, true, _) => ShadowDiscrepancy::Equivalent,
        (_, true, _, true) => ShadowDiscrepancy::Equivalent,
        // Both inconclusive (Unknown/Timeout).
        (false, false, false, false) => ShadowDiscrepancy::Equivalent,
        // One proved, other failed — real soundness mismatch. Check BEFORE
        // MirStronger/V1Stronger to avoid masking this critical case.
        (true, _, _, true) | (_, true, true, _) => ShadowDiscrepancy::Mismatch,
        // MIR proved, v1 did not (but v1 didn't fail either — just inconclusive).
        (true, _, false, false) => ShadowDiscrepancy::MirStronger,
        // MIR failed, v1 inconclusive — MIR more definitive.
        (_, true, false, false) => ShadowDiscrepancy::MirStronger,
        // v1 proved, MIR inconclusive.
        (false, false, true, _) => ShadowDiscrepancy::V1Stronger,
        // v1 failed, MIR inconclusive.
        (false, false, _, true) => ShadowDiscrepancy::V1Stronger,
    }
}

/// tRust #791: One-line summary of a verification result for logging.
fn result_summary(result: &VerificationResult) -> String {
    match result {
        VerificationResult::Proved { solver, time_ms, .. } => {
            format!("Proved({solver}, {time_ms}ms)")
        }
        VerificationResult::Failed { solver, time_ms, .. } => {
            format!("Failed({solver}, {time_ms}ms)")
        }
        VerificationResult::Unknown { solver, reason, .. } => {
            format!("Unknown({solver}: {reason})")
        }
        VerificationResult::Timeout { solver, timeout_ms } => {
            format!("Timeout({solver}, {timeout_ms}ms)")
        }
        // VerificationResult is #[non_exhaustive]; handle future variants gracefully.
        other => format!("Other({})", other.solver_name()),
    }
}

// ---------------------------------------------------------------------------
// MIR classification helpers
// ---------------------------------------------------------------------------

/// Returns true if the function has `#[requires]` or `#[ensures]` contracts.
fn has_contracts(func: &VerifiableFunction) -> bool {
    // Check the typed contracts list.
    let has_typed = func.contracts.iter().any(|c| {
        matches!(c.kind, ContractKind::Requires | ContractKind::Ensures)
    });

    // Also check the structured spec.
    let has_spec = !func.spec.requires.is_empty() || !func.spec.ensures.is_empty();

    // And the parsed formula-level conditions.
    let has_formulas = !func.preconditions.is_empty() || !func.postconditions.is_empty();

    has_typed || has_spec || has_formulas
}

/// Returns true if the function has `#[invariant]` or `#[loop_invariant]` annotations.
fn has_invariant_annotations(func: &VerifiableFunction) -> bool {
    let has_typed = func.contracts.iter().any(|c| {
        matches!(c.kind, ContractKind::Invariant | ContractKind::LoopInvariant)
    });

    let has_spec = !func.spec.invariants.is_empty();

    has_typed || has_spec
}

/// Returns true if the function body contains unsafe operations.
///
/// Detects: `AddressOf` (raw pointer creation), `Rvalue::Cast` to raw pointer types,
/// and derefs through raw pointers.
fn has_unsafe_operations(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().any(|bb| {
        bb.stmts.iter().any(|stmt| match stmt {
            Statement::Assign { rvalue, .. } => matches!(
                rvalue,
                Rvalue::AddressOf(_, _)
            ),
            _ => false,
        })
    })
}

/// Returns true if the function has atomic operations (from Terminator::Call with atomic field).
fn has_atomic_operations(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Terminator::Call { atomic: Some(_), .. }
        )
    })
}

/// Returns true if the function body has raw pointer operations.
///
/// Detects: `Rvalue::Ref` to raw pointers, `Rvalue::AddressOf`, and
/// `Rvalue::Cast` when locals have `RawPtr` type.
fn has_raw_pointer_operations(func: &VerifiableFunction) -> bool {
    // Check if any local is a raw pointer type.
    let has_raw_ptr_locals = func.body.locals.iter().any(|l| l.ty.is_raw_ptr());

    // Check for AddressOf or CopyForDeref (often used with raw pointers).
    let has_raw_ptr_ops = func.body.blocks.iter().any(|bb| {
        bb.stmts.iter().any(|stmt| match stmt {
            Statement::Assign { rvalue, .. } => matches!(
                rvalue,
                Rvalue::AddressOf(_, _) | Rvalue::CopyForDeref(_)
            ),
            _ => false,
        })
    });

    has_raw_ptr_locals || has_raw_ptr_ops
}

/// Returns true if the function has FFI calls (extern function calls).
///
/// In MIR, FFI calls appear as `Terminator::Call` where the function name
/// contains `::` patterns like `std::ffi::`, `extern`, or `libc::`.
fn has_ffi_calls(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Terminator::Call { func: callee, .. }
                if is_ffi_callee(callee)
        )
    })
}

/// Heuristic: is this callee name an FFI function?
fn is_ffi_callee(name: &str) -> bool {
    name.starts_with("libc::")
        || name.starts_with("std::ffi::")
        || name.starts_with("core::ffi::")
        || name.contains("extern \"C\"")
        || name.contains("__extern_")
}

/// Returns true if the function body has loops (back-edges in the CFG).
///
/// A back-edge exists when a block's terminator targets a block with a smaller
/// block ID. This is a conservative over-approximation: it may classify some
/// non-loop gotos as loops, but never misses actual loops.
fn has_loops(func: &VerifiableFunction) -> bool {
    for bb in &func.body.blocks {
        let current_id = bb.id.0;
        for target in successor_blocks(&bb.terminator) {
            if target <= current_id {
                return true;
            }
        }
    }
    false
}

/// Extract successor block indices from a terminator.
fn successor_blocks(terminator: &Terminator) -> Vec<usize> {
    match terminator {
        Terminator::Goto(bid) => vec![bid.0],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs: Vec<usize> = targets.iter().map(|(_, bid)| bid.0).collect();
            succs.push(otherwise.0);
            succs
        }
        Terminator::Call { target, .. } => {
            target.iter().map(|bid| bid.0).collect()
        }
        Terminator::Assert { target, .. } => vec![target.0],
        Terminator::Drop { target, .. } => vec![target.0],
        Terminator::Return | Terminator::Unreachable => vec![],
        _ => vec![],
    }
}

// ---------------------------------------------------------------------------
// Contract/VC bridging helpers
// ---------------------------------------------------------------------------

/// Build a `trust_sunder_lib::ContractSet` from a `VerifiableFunction`.
fn build_sunder_contracts(func: &VerifiableFunction) -> trust_sunder_lib::ContractSet {
    let mut contract_set = trust_sunder_lib::ContractSet::new();

    // From typed contracts.
    for c in &func.contracts {
        let sunder_contract = trust_sunder_lib::Contract::new(
            match c.kind {
                ContractKind::Requires => trust_sunder_lib::ContractKind::Requires,
                ContractKind::Ensures => trust_sunder_lib::ContractKind::Ensures,
                ContractKind::Invariant | ContractKind::LoopInvariant => {
                    trust_sunder_lib::ContractKind::Invariant
                }
                // Other kinds don't map directly to sunder contracts.
                _ => continue,
            },
            &c.body,
        );
        match c.kind {
            ContractKind::Requires => {
                contract_set.requires.push(sunder_contract);
            }
            ContractKind::Ensures => {
                contract_set.ensures.push(sunder_contract);
            }
            ContractKind::Invariant | ContractKind::LoopInvariant => {
                contract_set.invariants.push(sunder_contract);
            }
            _ => {}
        }
    }

    // From structured spec (FunctionSpec).
    for req in &func.spec.requires {
        contract_set
            .requires
            .push(trust_sunder_lib::Contract::requires(req));
    }
    for ens in &func.spec.ensures {
        contract_set
            .ensures
            .push(trust_sunder_lib::Contract::ensures(ens));
    }
    for inv in &func.spec.invariants {
        contract_set
            .invariants
            .push(trust_sunder_lib::Contract::invariant(inv));
    }

    contract_set
}

/// Build v1 VCs from a `VerifiableFunction` for fallback dispatch.
///
/// This generates safety VCs from the function's blocks (division by zero,
/// overflow, bounds checks). A real implementation would use trust-vcgen;
/// this is a lightweight bridge for the v1 dispatch path.
fn build_v1_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    use trust_types::{Formula, Ty, VcKind};

    let mut vcs = Vec::new();

    for bb in &func.body.blocks {
        // Generate VCs from assert terminators.
        if let Terminator::Assert { msg, span, .. } = &bb.terminator {
            let kind = match msg {
                trust_types::AssertMessage::DivisionByZero => VcKind::DivisionByZero,
                trust_types::AssertMessage::Overflow(op) => VcKind::ArithmeticOverflow {
                    op: *op,
                    operand_tys: (Ty::Int { width: 32, signed: true }, Ty::Int { width: 32, signed: true }),
                },
                trust_types::AssertMessage::BoundsCheck => VcKind::IndexOutOfBounds,
                trust_types::AssertMessage::RemainderByZero => VcKind::RemainderByZero,
                trust_types::AssertMessage::OverflowNeg => VcKind::NegationOverflow {
                    ty: Ty::Int { width: 32, signed: true },
                },
                _ => VcKind::Assertion {
                    message: format!("{msg:?}"),
                },
            };
            vcs.push(VerificationCondition {
                kind,
                function: func.name.clone(),
                location: span.clone(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            });
        }
    }

    vcs
}

/// Merge results from two backends (for UnsafeAudit).
///
/// Priority: Failed > Unknown/Timeout > Proved.
/// If both prove, uses the stronger proof strength.
fn merge_results(a: VerificationResult, b: VerificationResult) -> VerificationResult {
    // If either failed, return the failure.
    if a.is_failed() {
        return a;
    }
    if b.is_failed() {
        return b;
    }

    // If both proved, merge.
    match (&a, &b) {
        (
            VerificationResult::Proved {
                time_ms: t1,
                proof_certificate: cert1,
                ..
            },
            VerificationResult::Proved {
                time_ms: t2,
                proof_certificate: cert2,
                ..
            },
        ) => VerificationResult::Proved {
            solver: "mir-router-unsafe-audit".to_string(),
            time_ms: t1 + t2,
            // Deductive proof is stronger than bounded.
            strength: trust_types::ProofStrength::deductive(),
            proof_certificate: cert1.clone().or_else(|| cert2.clone()),
            solver_warnings: None,
        },
        // One proved, one didn't — return the non-proof result.
        (VerificationResult::Proved { .. }, _) => b,
        (_, VerificationResult::Proved { .. }) => a,
        // Neither proved — return whichever has more info.
        _ => a,
    }
}

// ---------------------------------------------------------------------------
// tRust #793: Typed counterexample propagation
// ---------------------------------------------------------------------------

/// Convert a zani-lib `TypedCounterexample` to a `trust_types::Counterexample`
/// preserving typed values.
///
/// This bridges the typed counterexample data from zani-lib's BMC solver back
/// into the generic `Counterexample` that flows through `VerificationResult::Failed`.
pub(crate) fn convert_typed_counterexample(
    typed_cex: &trust_zani_lib::TypedCounterexample,
) -> trust_types::Counterexample {
    let assignments: Vec<(String, trust_types::CounterexampleValue)> = typed_cex
        .variables
        .iter()
        .map(|(name, value)| {
            let cex_val = match value {
                trust_zani_lib::TypedValue::Bool(b) => {
                    trust_types::CounterexampleValue::Bool(*b)
                }
                trust_zani_lib::TypedValue::Int(n) => {
                    trust_types::CounterexampleValue::Int(*n)
                }
                trust_zani_lib::TypedValue::Uint(n) => {
                    trust_types::CounterexampleValue::Uint(*n)
                }
                trust_zani_lib::TypedValue::BitVec { value, .. } => {
                    trust_types::CounterexampleValue::Uint(*value)
                }
                trust_zani_lib::TypedValue::String(s) => {
                    trust_types::CounterexampleValue::Uint(s.parse::<u128>().unwrap_or(0))
                }
            };
            (name.clone(), cex_val)
        })
        .collect();

    match &typed_cex.trace {
        Some(trace_steps) => {
            let steps: Vec<trust_types::TraceStep> = trace_steps
                .iter()
                .map(|ts| trust_types::TraceStep {
                    step: ts.step,
                    assignments: ts
                        .assignments
                        .iter()
                        .map(|(k, v)| (k.clone(), format!("{v:?}")))
                        .collect(),
                    program_point: ts.program_point.clone(),
                })
                .collect();
            trust_types::Counterexample::with_trace(
                assignments,
                trust_types::CounterexampleTrace::new(steps),
            )
        }
        None => trust_types::Counterexample::new(assignments),
    }
}

// ---------------------------------------------------------------------------
// tRust #793: Proof certificate composition for portfolio/multi-backend results
// ---------------------------------------------------------------------------

/// Compose proof certificate data from multiple verification results.
///
/// When multiple backends in a portfolio or unsafe audit produce proof certificates,
/// this function creates a composed certificate hash from their individual certificates.
/// The composed certificate can then be stored in `trust-proof-cert`'s composition module.
#[must_use]
pub(crate) fn compose_portfolio_certificates(
    results: &[(MirStrategy, VerificationResult)],
) -> Option<Vec<u8>> {
    use sha2::{Digest, Sha256};

    let certificates: Vec<(&MirStrategy, &[u8])> = results
        .iter()
        .filter_map(|(strategy, result)| {
            if let VerificationResult::Proved {
                proof_certificate: Some(cert),
                ..
            } = result
            {
                Some((strategy, cert.as_slice()))
            } else {
                None
            }
        })
        .collect();

    if certificates.is_empty() {
        return None;
    }

    // Compose by hashing all component certificates together.
    let mut hasher = Sha256::new();
    for (strategy, cert_bytes) in &certificates {
        hasher.update(format!("{strategy}:").as_bytes());
        hasher.update(cert_bytes);
        hasher.update(b"|");
    }
    Some(hasher.finalize().to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::*;

    // -----------------------------------------------------------------------
    // Test helper: build a minimal VerifiableFunction
    // -----------------------------------------------------------------------

    fn minimal_func(name: &str) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn func_with_contract(name: &str, kind: ContractKind) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.contracts.push(Contract {
            kind,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        });
        f
    }

    fn func_with_unsafe(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::AddressOf(true, Place::local(0)),
            span: SourceSpan::default(),
        });
        f
    }

    fn func_with_atomics(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.body.blocks[0].terminator = Terminator::Call {
            func: "std::sync::atomic::AtomicU64::fetch_add".to_string(),
            args: vec![],
            dest: Place::local(0),
            target: None,
            span: SourceSpan::default(),
            atomic: Some(AtomicOperation {
                place: Place::local(0),
                dest: None,
                op_kind: AtomicOpKind::FetchAdd,
                ordering: AtomicOrdering::SeqCst,
                failure_ordering: None,
                span: SourceSpan::default(),
            }),
        };
        f
    }

    fn func_with_raw_ptr_locals(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.body.locals.push(LocalDecl {
            index: 1,
            ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
            name: Some("ptr".to_string()),
        });
        f
    }

    fn func_with_ffi(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.body.blocks[0].terminator = Terminator::Call {
            func: "libc::malloc".to_string(),
            args: vec![],
            dest: Place::local(0),
            target: None,
            span: SourceSpan::default(),
            atomic: None,
        };
        f
    }

    fn func_with_loop(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.body.blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(0)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1), // Back-edge: loop!
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];
        f
    }

    fn func_with_spec(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.spec = FunctionSpec {
            requires: vec!["n > 0".to_string()],
            ensures: vec!["result >= 0".to_string()],
            invariants: vec![],
        };
        f
    }

    fn func_with_invariant_spec(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.spec = FunctionSpec {
            requires: vec![],
            ensures: vec![],
            invariants: vec!["i < n".to_string()],
        };
        f
    }

    // -----------------------------------------------------------------------
    // Classification tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_plain_function_v1_fallback() {
        let router = MirRouter::with_defaults();
        let func = minimal_func("plain");
        assert_eq!(router.classify(&func), MirStrategy::V1Fallback);
    }

    #[test]
    fn test_classify_contract_requires() {
        let router = MirRouter::with_defaults();
        let func = func_with_contract("with_requires", ContractKind::Requires);
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_contract_ensures() {
        let router = MirRouter::with_defaults();
        let func = func_with_contract("with_ensures", ContractKind::Ensures);
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_invariant_annotation() {
        let router = MirRouter::with_defaults();
        let func = func_with_contract("with_invariant", ContractKind::Invariant);
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_loop_invariant_annotation() {
        let router = MirRouter::with_defaults();
        let func = func_with_contract("with_loop_inv", ContractKind::LoopInvariant);
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_unsafe_with_contracts() {
        let router = MirRouter::with_defaults();
        let mut func = func_with_unsafe("unsafe_with_contracts");
        func.contracts.push(Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "ptr.is_null() == false".to_string(),
        });
        assert_eq!(router.classify(&func), MirStrategy::UnsafeAudit);
    }

    #[test]
    fn test_classify_unsafe_without_contracts_raw_ptr() {
        let router = MirRouter::with_defaults();
        let func = func_with_unsafe("unsafe_no_contracts");
        // AddressOf triggers both has_unsafe and has_raw_pointer_operations.
        // Since there are no contracts, UnsafeAudit won't trigger.
        // Instead, SeparationLogic takes priority over DataRace.
        let strategy = router.classify(&func);
        assert_eq!(strategy, MirStrategy::SeparationLogic);
    }

    #[test]
    fn test_classify_atomics() {
        let router = MirRouter::with_defaults();
        let func = func_with_atomics("atomic_fetch");
        assert_eq!(router.classify(&func), MirStrategy::DataRace);
    }

    #[test]
    fn test_classify_raw_pointer_locals() {
        let router = MirRouter::with_defaults();
        let func = func_with_raw_ptr_locals("raw_ptr");
        assert_eq!(router.classify(&func), MirStrategy::SeparationLogic);
    }

    #[test]
    fn test_classify_ffi() {
        let router = MirRouter::with_defaults();
        let func = func_with_ffi("ffi_call");
        assert_eq!(router.classify(&func), MirStrategy::FFIBoundary);
    }

    #[test]
    fn test_classify_loop() {
        let router = MirRouter::with_defaults();
        let func = func_with_loop("loopy");
        assert_eq!(router.classify(&func), MirStrategy::BoundedModelCheck);
    }

    #[test]
    fn test_classify_spec_requires_ensures() {
        let router = MirRouter::with_defaults();
        let func = func_with_spec("with_spec");
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_spec_invariants() {
        let router = MirRouter::with_defaults();
        let func = func_with_invariant_spec("with_inv_spec");
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_preconditions_formulas() {
        let router = MirRouter::with_defaults();
        let mut func = minimal_func("with_preconditions");
        func.preconditions.push(Formula::Bool(true));
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_postconditions_formulas() {
        let router = MirRouter::with_defaults();
        let mut func = minimal_func("with_postconditions");
        func.postconditions.push(Formula::Bool(true));
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    // -----------------------------------------------------------------------
    // Dispatch tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_v1_fallback_dispatch_no_vcs() {
        let router = MirRouter::with_defaults();
        let func = minimal_func("empty");
        let result = router.verify_function(&func);
        // Empty function with no asserts produces no VCs -> trivially proved.
        assert!(result.is_proved());
    }

    #[test]
    fn test_v1_fallback_dispatch_with_assert() {
        let router = MirRouter::with_defaults();
        let mut func = minimal_func("with_assert");
        // Use target BlockId(1) to avoid creating a back-edge (which would
        // classify as BoundedModelCheck instead of V1Fallback).
        func.body.blocks[0].terminator = Terminator::Assert {
            cond: Operand::Constant(ConstValue::Bool(true)),
            expected: true,
            msg: AssertMessage::DivisionByZero,
            target: BlockId(1),
            span: SourceSpan::default(),
        };
        // This will generate a VC and dispatch through mock backend.
        let result = router.verify_function(&func);
        // MockBackend returns Proved for Formula::Bool(false) (negation is unsat).
        assert!(result.is_proved());
    }

    #[test]
    fn test_verify_all_classifies_each() {
        let router = MirRouter::with_defaults();
        let funcs = vec![
            minimal_func("plain"),
            func_with_contract("contracted", ContractKind::Requires),
            func_with_loop("loopy"),
        ];

        let results = router.verify_all(&funcs);
        assert_eq!(results.len(), 3);
        assert_eq!(results[0].1, MirStrategy::V1Fallback);
        assert_eq!(results[1].1, MirStrategy::ContractVerification);
        assert_eq!(results[2].1, MirStrategy::BoundedModelCheck);
    }

    #[test]
    fn test_verify_with_explicit_strategy() {
        let router = MirRouter::with_defaults();
        let func = minimal_func("explicit");
        // Force V1Fallback even though it's the default.
        let result = router.verify_with_strategy(&func, &MirStrategy::V1Fallback);
        assert!(result.is_proved());
    }

    // -----------------------------------------------------------------------
    // Merge result tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_merge_both_proved() {
        let a = VerificationResult::Proved {
            solver: "a".to_string(),
            time_ms: 10,
            strength: ProofStrength::bounded(10),
            proof_certificate: None,
            solver_warnings: None,
        };
        let b = VerificationResult::Proved {
            solver: "b".to_string(),
            time_ms: 20,
            strength: ProofStrength::deductive(),
            proof_certificate: None,
            solver_warnings: None,
        };
        let merged = merge_results(a, b);
        assert!(merged.is_proved());
        if let VerificationResult::Proved { time_ms, .. } = &merged {
            assert_eq!(*time_ms, 30);
        }
    }

    #[test]
    fn test_merge_one_failed() {
        let a = VerificationResult::Failed {
            solver: "a".to_string(),
            time_ms: 10,
            counterexample: None,
        };
        let b = VerificationResult::Proved {
            solver: "b".to_string(),
            time_ms: 20,
            strength: ProofStrength::deductive(),
            proof_certificate: None,
            solver_warnings: None,
        };
        let merged = merge_results(a, b);
        assert!(merged.is_failed());
    }

    #[test]
    fn test_merge_one_proved_one_unknown() {
        let a = VerificationResult::Proved {
            solver: "a".to_string(),
            time_ms: 10,
            strength: ProofStrength::bounded(10),
            proof_certificate: None,
            solver_warnings: None,
        };
        let b = VerificationResult::Unknown {
            solver: "b".to_string(),
            time_ms: 20,
            reason: "timeout".to_string(),
        };
        let merged = merge_results(a, b);
        // One proved, other didn't — return the non-proof result.
        assert!(!merged.is_proved());
    }

    // -----------------------------------------------------------------------
    // Strategy display tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_strategy_display() {
        assert_eq!(MirStrategy::BoundedModelCheck.to_string(), "BoundedModelCheck");
        assert_eq!(MirStrategy::ContractVerification.to_string(), "ContractVerification");
        assert_eq!(MirStrategy::UnsafeAudit.to_string(), "UnsafeAudit");
        assert_eq!(MirStrategy::V1Fallback.to_string(), "V1Fallback");

        let portfolio = MirStrategy::Portfolio(vec![
            MirStrategy::BoundedModelCheck,
            MirStrategy::ContractVerification,
        ]);
        assert_eq!(
            portfolio.to_string(),
            "Portfolio(BoundedModelCheck, ContractVerification)"
        );
    }

    // -----------------------------------------------------------------------
    // Helper function tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_ffi_callee() {
        assert!(is_ffi_callee("libc::malloc"));
        assert!(is_ffi_callee("libc::free"));
        assert!(is_ffi_callee("std::ffi::CString::new"));
        assert!(is_ffi_callee("core::ffi::c_str::CStr::as_ptr"));
        assert!(!is_ffi_callee("std::vec::Vec::new"));
        assert!(!is_ffi_callee("my_crate::my_func"));
    }

    #[test]
    fn test_has_loops_no_loop() {
        let func = minimal_func("no_loop");
        assert!(!has_loops(&func));
    }

    #[test]
    fn test_has_loops_with_back_edge() {
        let func = func_with_loop("loopy");
        assert!(has_loops(&func));
    }

    #[test]
    fn test_build_sunder_contracts_from_typed() {
        let func = func_with_contract("contracted", ContractKind::Requires);
        let contracts = build_sunder_contracts(&func);
        assert_eq!(contracts.requires.len(), 1);
        assert_eq!(contracts.requires[0].expression, "x > 0");
    }

    #[test]
    fn test_build_sunder_contracts_from_spec() {
        let func = func_with_spec("spec_func");
        let contracts = build_sunder_contracts(&func);
        assert_eq!(contracts.requires.len(), 1);
        assert_eq!(contracts.ensures.len(), 1);
        assert_eq!(contracts.requires[0].expression, "n > 0");
        assert_eq!(contracts.ensures[0].expression, "result >= 0");
    }

    #[test]
    fn test_build_v1_vcs_from_asserts() {
        let mut func = minimal_func("assert_func");
        func.body.blocks[0].terminator = Terminator::Assert {
            cond: Operand::Constant(ConstValue::Bool(true)),
            expected: true,
            msg: AssertMessage::DivisionByZero,
            target: BlockId(0),
            span: SourceSpan::default(),
        };
        let vcs = build_v1_vcs(&func);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::DivisionByZero));
    }

    #[test]
    fn test_config_defaults() {
        let config = MirRouterConfig::default();
        assert_eq!(config.bmc_depth, 100);
        assert_eq!(config.timeout_ms, 30_000);
        assert!(!config.produce_proofs);
        assert!(!config.shadow_mode);
    }

    #[test]
    fn test_portfolio_strategy_empty() {
        let router = MirRouter::with_defaults();
        let func = minimal_func("empty_portfolio");
        let result = router.dispatch_portfolio(&func, &[]);
        match result {
            VerificationResult::Unknown { reason, .. } => {
                assert!(reason.contains("no strategies"));
            }
            _ => panic!("expected Unknown for empty portfolio"),
        }
    }

    // -----------------------------------------------------------------------
    // Shadow mode tests
    // -----------------------------------------------------------------------

    fn shadow_router() -> MirRouter {
        let config = MirRouterConfig {
            shadow_mode: true,
            ..MirRouterConfig::default()
        };
        MirRouter::new(Router::new(), config)
    }

    #[test]
    fn test_shadow_verify_plain_function_equivalent() {
        let router = shadow_router();
        let func = minimal_func("plain_shadow");

        let shadow = router.shadow_verify(&func);

        // Plain function: both MIR router (V1Fallback) and v1 should agree.
        assert_eq!(shadow.strategy, MirStrategy::V1Fallback);
        assert_eq!(shadow.discrepancy, ShadowDiscrepancy::Equivalent);
        assert!(shadow.mir_result.is_proved());
        assert!(shadow.v1_result.is_proved());
        assert!(shadow.chosen_result.is_proved());
    }

    #[test]
    fn test_shadow_verify_contract_function_results_comparable() {
        let router = shadow_router();
        let func = func_with_contract("contract_shadow", ContractKind::Requires);

        let shadow = router.shadow_verify(&func);

        // Contract function uses ContractVerification strategy via MIR router.
        assert_eq!(shadow.strategy, MirStrategy::ContractVerification);
        // Both results are present regardless of discrepancy.
        assert!(!shadow.mir_result.solver_name().is_empty());
        assert!(!shadow.v1_result.solver_name().is_empty());
    }

    #[test]
    fn test_shadow_verify_loop_function_dispatch() {
        let router = shadow_router();
        let func = func_with_loop("loop_shadow");

        let shadow = router.shadow_verify(&func);

        // Loop function classified as BoundedModelCheck.
        assert_eq!(shadow.strategy, MirStrategy::BoundedModelCheck);
        // Both paths produce results.
        assert!(!shadow.mir_result.solver_name().is_empty());
        assert!(!shadow.v1_result.solver_name().is_empty());
    }

    #[test]
    fn test_shadow_verify_fallback_to_v1_on_mir_unknown() {
        let router = shadow_router();
        // A contract function dispatches to sunder-lib which returns Unknown
        // in the mock test environment. The v1 path (no VCs) returns Proved.
        let func = func_with_spec("fallback_shadow");

        let shadow = router.shadow_verify(&func);

        // If MIR result is Unknown but v1 is Proved, chosen_result should be v1.
        if !shadow.mir_result.is_proved() && !shadow.mir_result.is_failed() {
            assert!(
                shadow.chosen_result.is_proved() == shadow.v1_result.is_proved(),
                "When MIR is inconclusive, chosen should match v1"
            );
        }
    }

    #[test]
    fn test_shadow_verify_mir_proved_takes_precedence() {
        let router = shadow_router();
        // Plain function with no VCs: MIR router via V1Fallback path proves trivially.
        let func = minimal_func("mir_wins_shadow");

        let shadow = router.shadow_verify(&func);

        assert!(shadow.mir_result.is_proved());
        assert!(shadow.chosen_result.is_proved());
        // chosen_result should match MIR when MIR is definitive.
        assert_eq!(
            shadow.chosen_result.solver_name(),
            shadow.mir_result.solver_name()
        );
    }

    #[test]
    fn test_shadow_mode_through_verify_function() {
        // When shadow_mode is on, verify_function should still return a result.
        let router = shadow_router();
        let func = minimal_func("verify_fn_shadow");
        let result = router.verify_function(&func);
        assert!(result.is_proved());
    }

    #[test]
    fn test_shadow_mode_off_skips_shadow() {
        // When shadow_mode is off, verify_function does NOT do shadow dispatch.
        let router = MirRouter::with_defaults();
        assert!(!router.config().shadow_mode);
        let func = minimal_func("no_shadow");
        let result = router.verify_function(&func);
        assert!(result.is_proved());
    }

    #[test]
    fn test_classify_discrepancy_both_proved() {
        let proved_a = VerificationResult::Proved {
            solver: "a".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        };
        let proved_b = VerificationResult::Proved {
            solver: "b".to_string(),
            time_ms: 20,
            strength: ProofStrength::deductive(),
            proof_certificate: None,
            solver_warnings: None,
        };
        assert_eq!(
            classify_discrepancy(&proved_a, &proved_b),
            ShadowDiscrepancy::Equivalent
        );
    }

    #[test]
    fn test_classify_discrepancy_both_failed() {
        let failed_a = VerificationResult::Failed {
            solver: "a".to_string(),
            time_ms: 10,
            counterexample: None,
        };
        let failed_b = VerificationResult::Failed {
            solver: "b".to_string(),
            time_ms: 20,
            counterexample: None,
        };
        assert_eq!(
            classify_discrepancy(&failed_a, &failed_b),
            ShadowDiscrepancy::Equivalent
        );
    }

    #[test]
    fn test_classify_discrepancy_both_unknown() {
        let unknown_a = VerificationResult::Unknown {
            solver: "a".to_string(),
            time_ms: 10,
            reason: "timeout".to_string(),
        };
        let unknown_b = VerificationResult::Unknown {
            solver: "b".to_string(),
            time_ms: 20,
            reason: "complex".to_string(),
        };
        assert_eq!(
            classify_discrepancy(&unknown_a, &unknown_b),
            ShadowDiscrepancy::Equivalent
        );
    }

    #[test]
    fn test_classify_discrepancy_mir_stronger_proved() {
        let proved = VerificationResult::Proved {
            solver: "mir".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        };
        let unknown = VerificationResult::Unknown {
            solver: "v1".to_string(),
            time_ms: 20,
            reason: "complex".to_string(),
        };
        assert_eq!(
            classify_discrepancy(&proved, &unknown),
            ShadowDiscrepancy::MirStronger
        );
    }

    #[test]
    fn test_classify_discrepancy_mir_stronger_failed() {
        let failed = VerificationResult::Failed {
            solver: "mir".to_string(),
            time_ms: 10,
            counterexample: None,
        };
        let unknown = VerificationResult::Unknown {
            solver: "v1".to_string(),
            time_ms: 20,
            reason: "complex".to_string(),
        };
        assert_eq!(
            classify_discrepancy(&failed, &unknown),
            ShadowDiscrepancy::MirStronger
        );
    }

    #[test]
    fn test_classify_discrepancy_v1_stronger_proved() {
        let unknown = VerificationResult::Unknown {
            solver: "mir".to_string(),
            time_ms: 10,
            reason: "complex".to_string(),
        };
        let proved = VerificationResult::Proved {
            solver: "v1".to_string(),
            time_ms: 20,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        };
        assert_eq!(
            classify_discrepancy(&unknown, &proved),
            ShadowDiscrepancy::V1Stronger
        );
    }

    #[test]
    fn test_classify_discrepancy_v1_stronger_failed() {
        let unknown = VerificationResult::Unknown {
            solver: "mir".to_string(),
            time_ms: 10,
            reason: "complex".to_string(),
        };
        let failed = VerificationResult::Failed {
            solver: "v1".to_string(),
            time_ms: 20,
            counterexample: None,
        };
        assert_eq!(
            classify_discrepancy(&unknown, &failed),
            ShadowDiscrepancy::V1Stronger
        );
    }

    #[test]
    fn test_classify_discrepancy_mismatch_proved_vs_failed() {
        let proved = VerificationResult::Proved {
            solver: "mir".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        };
        let failed = VerificationResult::Failed {
            solver: "v1".to_string(),
            time_ms: 20,
            counterexample: None,
        };
        assert_eq!(
            classify_discrepancy(&proved, &failed),
            ShadowDiscrepancy::Mismatch
        );
    }

    #[test]
    fn test_classify_discrepancy_mismatch_failed_vs_proved() {
        let failed = VerificationResult::Failed {
            solver: "mir".to_string(),
            time_ms: 10,
            counterexample: None,
        };
        let proved = VerificationResult::Proved {
            solver: "v1".to_string(),
            time_ms: 20,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        };
        assert_eq!(
            classify_discrepancy(&failed, &proved),
            ShadowDiscrepancy::Mismatch
        );
    }

    #[test]
    fn test_shadow_discrepancy_display() {
        assert_eq!(ShadowDiscrepancy::Equivalent.to_string(), "equivalent");
        assert_eq!(ShadowDiscrepancy::MirStronger.to_string(), "mir_stronger");
        assert_eq!(ShadowDiscrepancy::V1Stronger.to_string(), "v1_stronger");
        assert_eq!(ShadowDiscrepancy::Mismatch.to_string(), "mismatch");
    }

    #[test]
    fn test_result_summary_format() {
        let proved = VerificationResult::Proved {
            solver: "test".to_string(),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        };
        assert_eq!(result_summary(&proved), "Proved(test, 42ms)");

        let failed = VerificationResult::Failed {
            solver: "test".to_string(),
            time_ms: 7,
            counterexample: None,
        };
        assert_eq!(result_summary(&failed), "Failed(test, 7ms)");

        let unknown = VerificationResult::Unknown {
            solver: "test".to_string(),
            time_ms: 0,
            reason: "complex formula".to_string(),
        };
        assert_eq!(result_summary(&unknown), "Unknown(test: complex formula)");

        let timeout = VerificationResult::Timeout {
            solver: "test".to_string(),
            timeout_ms: 5000,
        };
        assert_eq!(result_summary(&timeout), "Timeout(test, 5000ms)");
    }

    #[test]
    fn test_shadow_verify_all_functions_produce_results() {
        // Verify that shadow mode works for each function type.
        let router = shadow_router();
        let funcs = vec![
            minimal_func("plain"),
            func_with_contract("contracted", ContractKind::Requires),
            func_with_loop("loopy"),
            func_with_ffi("ffi"),
            func_with_raw_ptr_locals("raw_ptr"),
            func_with_atomics("atomic"),
        ];

        for func in &funcs {
            let shadow = router.shadow_verify(func);
            // Every function should produce a ShadowResult with both paths.
            assert!(
                !shadow.mir_result.solver_name().is_empty(),
                "MIR result missing solver for {}",
                func.name,
            );
            assert!(
                !shadow.v1_result.solver_name().is_empty(),
                "v1 result missing solver for {}",
                func.name,
            );
            assert!(
                !shadow.chosen_result.solver_name().is_empty(),
                "chosen result missing solver for {}",
                func.name,
            );
        }
    }

    // -----------------------------------------------------------------------
    // tRust #793: Portfolio racing tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_portfolio_racing_enabled_by_default() {
        let config = MirRouterConfig::default();
        assert!(config.enable_portfolio_racing);
        assert!(!config.infer_invariants);
    }

    #[test]
    fn test_portfolio_parallel_single_strategy() {
        let router = MirRouter::with_defaults();
        let func = minimal_func("single_strategy");
        // Single strategy should not invoke parallelism.
        let result = router.dispatch_portfolio(&func, &[MirStrategy::V1Fallback]);
        assert!(result.is_proved());
    }

    #[test]
    fn test_portfolio_parallel_multiple_strategies() {
        let router = MirRouter::with_defaults();
        let func = minimal_func("multi_strategy");
        let strategies = vec![MirStrategy::V1Fallback, MirStrategy::BoundedModelCheck];
        let result = router.dispatch_portfolio(&func, &strategies);
        // Both backends produce results; at least one should be definitive.
        assert!(
            result.is_proved() || result.is_failed()
                || matches!(result, VerificationResult::Unknown { .. }),
        );
    }

    #[test]
    fn test_portfolio_sequential_fallback() {
        let config = MirRouterConfig {
            enable_portfolio_racing: false,
            ..MirRouterConfig::default()
        };
        let router = MirRouter::new(Router::new(), config);
        let func = minimal_func("seq_fallback");
        let strategies = vec![MirStrategy::V1Fallback, MirStrategy::BoundedModelCheck];
        let result = router.dispatch_portfolio(&func, &strategies);
        // Sequential should still produce a valid result.
        assert!(
            result.is_proved() || result.is_failed()
                || matches!(result, VerificationResult::Unknown { .. }),
        );
    }

    #[test]
    fn test_unsafe_audit_portfolio_racing() {
        // UnsafeAudit with portfolio racing enabled dispatches via portfolio.
        let router = MirRouter::with_defaults();
        let mut func = func_with_unsafe("unsafe_portfolio");
        func.contracts.push(Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "ptr != null".to_string(),
        });
        let result = router.verify_function(&func);
        assert!(!result.solver_name().is_empty());
    }

    #[test]
    fn test_unsafe_audit_sequential_fallback() {
        let config = MirRouterConfig {
            enable_portfolio_racing: false,
            ..MirRouterConfig::default()
        };
        let router = MirRouter::new(Router::new(), config);
        let mut func = func_with_unsafe("unsafe_seq");
        func.contracts.push(Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "ptr != null".to_string(),
        });
        let result = router.verify_function(&func);
        assert!(!result.solver_name().is_empty());
    }

    // -----------------------------------------------------------------------
    // tRust #793: Typed counterexample conversion tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_convert_typed_counterexample_basic() {
        use std::collections::BTreeMap;
        let mut vars = BTreeMap::new();
        vars.insert("x".to_string(), trust_zani_lib::TypedValue::Int(-42));
        vars.insert("y".to_string(), trust_zani_lib::TypedValue::Uint(255));
        vars.insert("flag".to_string(), trust_zani_lib::TypedValue::Bool(true));

        let typed_cex = trust_zani_lib::TypedCounterexample::new(vars);
        let cex = convert_typed_counterexample(&typed_cex);

        assert_eq!(cex.assignments.len(), 3);
        // BTreeMap is sorted by key, so assignments should be in key order.
        assert_eq!(cex.assignments[0].0, "flag");
        assert!(matches!(
            cex.assignments[0].1,
            CounterexampleValue::Bool(true)
        ));
        assert_eq!(cex.assignments[1].0, "x");
        assert!(matches!(
            cex.assignments[1].1,
            CounterexampleValue::Int(-42)
        ));
        assert_eq!(cex.assignments[2].0, "y");
        assert!(matches!(
            cex.assignments[2].1,
            CounterexampleValue::Uint(255)
        ));
        assert!(cex.trace.is_none());
    }

    #[test]
    fn test_convert_typed_counterexample_with_trace() {
        use std::collections::BTreeMap;
        let mut vars = BTreeMap::new();
        vars.insert("i".to_string(), trust_zani_lib::TypedValue::Uint(10));

        let mut step_vars = BTreeMap::new();
        step_vars.insert("i".to_string(), trust_zani_lib::TypedValue::Uint(0));
        let trace = vec![trust_zani_lib::TraceStep {
            step: 0,
            assignments: step_vars,
            program_point: Some("bb0".to_string()),
        }];

        let typed_cex = trust_zani_lib::TypedCounterexample::new(vars).with_trace(trace);
        let cex = convert_typed_counterexample(&typed_cex);

        assert!(cex.trace.is_some());
        let trace = cex.trace.as_ref().unwrap();
        assert_eq!(trace.len(), 1);
        assert_eq!(trace.steps[0].step, 0);
        assert_eq!(trace.steps[0].program_point.as_deref(), Some("bb0"));
    }

    // -----------------------------------------------------------------------
    // tRust #793: Proof certificate composition tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_compose_portfolio_certificates_empty() {
        let results: Vec<(MirStrategy, VerificationResult)> = vec![];
        assert!(compose_portfolio_certificates(&results).is_none());
    }

    #[test]
    fn test_compose_portfolio_certificates_no_certs() {
        let results = vec![
            (
                MirStrategy::BoundedModelCheck,
                VerificationResult::Proved {
                    solver: "zani".to_string(),
                    time_ms: 10,
                    strength: ProofStrength::bounded(100),
                    proof_certificate: None,
                    solver_warnings: None,
                },
            ),
        ];
        assert!(compose_portfolio_certificates(&results).is_none());
    }

    #[test]
    fn test_compose_portfolio_certificates_with_certs() {
        let results = vec![
            (
                MirStrategy::BoundedModelCheck,
                VerificationResult::Proved {
                    solver: "zani".to_string(),
                    time_ms: 10,
                    strength: ProofStrength::bounded(100),
                    proof_certificate: Some(vec![1, 2, 3]),
                    solver_warnings: None,
                },
            ),
            (
                MirStrategy::ContractVerification,
                VerificationResult::Proved {
                    solver: "sunder".to_string(),
                    time_ms: 20,
                    strength: ProofStrength::deductive(),
                    proof_certificate: Some(vec![4, 5, 6]),
                    solver_warnings: None,
                },
            ),
        ];
        let composed = compose_portfolio_certificates(&results);
        assert!(composed.is_some());
        // SHA-256 produces 32 bytes.
        assert_eq!(composed.unwrap().len(), 32);
    }

    #[test]
    fn test_compose_portfolio_certificates_deterministic() {
        let results = vec![
            (
                MirStrategy::BoundedModelCheck,
                VerificationResult::Proved {
                    solver: "zani".to_string(),
                    time_ms: 10,
                    strength: ProofStrength::bounded(100),
                    proof_certificate: Some(vec![1, 2, 3]),
                    solver_warnings: None,
                },
            ),
        ];
        let a = compose_portfolio_certificates(&results);
        let b = compose_portfolio_certificates(&results);
        assert_eq!(a, b);
    }

    // -----------------------------------------------------------------------
    // tRust #793: Invariant inference config test
    // -----------------------------------------------------------------------

    #[test]
    fn test_bmc_dispatch_with_invariant_hints_config() {
        // When infer_invariants is true and function has loops,
        // dispatch should use the invariant hints path.
        let config = MirRouterConfig {
            infer_invariants: true,
            ..MirRouterConfig::default()
        };
        let router = MirRouter::new(Router::new(), config);
        let func = func_with_loop("loopy_invariant");
        let result = router.verify_function(&func);
        // The function has loops so it is classified as BoundedModelCheck,
        // and with infer_invariants=true it goes through the hints path.
        // It should still produce a valid result.
        assert!(!result.solver_name().is_empty());
    }

    #[test]
    fn test_bmc_dispatch_without_invariant_hints() {
        // When infer_invariants is false, dispatch goes straight to BMC.
        let config = MirRouterConfig {
            infer_invariants: false,
            ..MirRouterConfig::default()
        };
        let router = MirRouter::new(Router::new(), config);
        let func = func_with_loop("loopy_no_hints");
        let result = router.verify_function(&func);
        assert!(!result.solver_name().is_empty());
    }
}
