//! trust-vcgen: Verification condition generation for tRust
//!
//! Takes a VerifiableFunction (extracted from MIR) and produces
//! VerificationConditions that can be dispatched to solvers.
//!
//! For M2, focuses on L0 safety VCs:
//! - Arithmetic overflow (add, sub, mul on integer types)
//! - Division by zero
//! - Remainder by zero
//! - Index out-of-bounds (array/slice access)
//! - Assert terminator conditions (rustc's own safety checks)
//! - Cast overflow (narrowing, signed-to-unsigned, unsigned-to-signed)
//! - Negation overflow (-x when x == INT_MIN)
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// tRust: Allow std HashMap/HashSet — FxHash lint only applies to compiler internals
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]
#![allow(dead_code)]

pub(crate) mod error;
// tRust #477: VC deduplication to avoid redundant solver calls.
pub(crate) mod dedup;
pub(crate) mod abstract_domains;
pub(crate) mod abstract_interp;
// tRust #148: Binary analysis pipeline — pattern detection and type recovery.
pub(crate) mod binary_analysis;
// tRust #148: Unified binary analysis pipeline (lift → type-recover → detect → generate VCs).
pub(crate) mod binary_pipeline;
pub(crate) mod cpa;
// tRust #513: Adapter bridging trust-lift LiftedFunction to VC generation for binary verification.
pub mod lift_adapter;
// tRust #227: CPA-integrated abstract interpretation domains.
pub(crate) mod interval_domain;
pub(crate) mod octagon_domain;
pub(crate) mod pointer_domain;
// tRust #192: Cross-checking for MIR→Formula VC generation.
pub(crate) mod cross_check;
pub(crate) mod boundary_vcgen;
// tRust #797: bounds.rs deleted — functionality migrated to trust-zani-lib.
pub(crate) mod cex_refine;
// tRust #147: CHC encoding for z4 Spacer loop invariant inference.
pub mod chc;
// tRust #588: Made pub for Sunder contract IR builder access.
pub(crate) mod contracts;
// tRust #119: Spec-based VC generation from FunctionSpec (#[requires], #[ensures]).
pub(crate) mod spec_parser;
// tRust #204: Extern/FFI function summary framework (angr/Ghidra-inspired).
pub(crate) mod ffi_summary;
// tRust #460: FFI boundary verification with summary-based VCs.
pub(crate) mod ffi_vcgen;
mod guards;
pub(crate) mod invariants;
pub(crate) mod invariant_inference;
pub(crate) mod liveness;
// tRust #792: memory_bytes.rs removed — byte-level encoding now in trust-zani-lib/sunder-lib.
// tRust #797: memory_model.rs deleted — functionality migrated to trust-zani-lib.
// tRust #150: Provenance-based VC generation (Layer 2).
pub mod memory_provenance;
// tRust #797: region_encoding.rs deleted — functionality migrated to trust-zani-lib.
// tRust #797: safe_rust_model.rs deleted — functionality migrated to trust-zani-lib.
pub(crate) mod loop_analysis;
mod negation;
pub(crate) mod panic_free;
pub(crate) mod range;
pub(crate) mod pointer_analysis;
mod resilience;
pub(crate) mod resilience_analysis;
// tRust #148: Security-focused VC generation from binary patterns.
pub(crate) mod security_vcs;
// tRust #792: spacer_bridge.rs removed — Spacer CHC solving now via z4/zani directly.
pub(crate) mod instantiation;
pub(crate) mod interprocedural;
pub(crate) mod modular;
// tRust #230: Interprocedural analysis modules — call graph construction and summaries.
pub(crate) mod call_graph;
pub(crate) mod summaries;
pub(crate) mod persistent_specdb;
pub(crate) mod quantifier_tiers;
pub(crate) mod spec_inference;
pub(crate) mod specdb;
pub(crate) mod termination;
// tRust #797: recursive_verify.rs deleted — functionality migrated to trust-sunder-lib.
pub(crate) mod trait_verify;
// tRust #149: Translation validation — prove compiled output refines MIR semantics.
pub(crate) mod translation_validation;
// tRust #191: Separation logic primitives for unsafe Rust verification.
pub(crate) mod separation_logic;
// tRust #436: Minimal separation logic provenance engine for unsafe Rust verification.
pub(crate) mod sep_engine;
pub(crate) mod unsafe_audit;
pub(crate) mod unsafe_patterns;
// tRust #191: Dedicated unsafe operation VC generation (UnsafeOpKind classifier).
pub(crate) mod unsafe_vc;
pub(crate) mod unsafe_verify;
mod rvalue_safety;
mod unreachable;
// tRust #736: Core VC generation logic (generate_vcs, generate_vcs_with_discharge).
mod generate;
pub(crate) mod value_analysis;
// tRust #203: Data race detection and memory ordering verification.
pub mod data_race;
// tRust #617: TLA+ spec generation for data race verification conditions.
pub(crate) mod data_race_tla;
// tRust #203: Memory ordering verification — HappensBefore, DataRaceDetector, AtomicAccessLog.
pub mod memory_ordering;
// tRust #162: Call graph reachability moved from trust-types.
pub mod reachability;
// tRust #238: Ownership and borrow checking for MIR bodies.
pub mod ownership;
// tRust #241: Verification condition simplification passes.
pub mod simplify;
// tRust #659: Semantic equivalence checking for formula simplifications via z4.
pub(crate) mod simplify_equivalence;
// tRust #792: smtlib2.rs removed — SMT-LIB2 printing now in trust-types::smt_logic.
// tRust #243: Trait object verification with vtable modeling.
pub(crate) mod vtable_model;
// tRust #265: Proof obligation splitter for parallel solving.
pub(crate) mod vc_splitter;
// tRust #248: Modular verification with function contracts.
pub(crate) mod contract_check;
// tRust #250: Send/Sync concurrency verification.
pub mod send_sync;
// tRust #280: Alias analysis for VC precision.
pub(crate) mod alias_analysis;
// tRust #286: Quantifier elimination for VC simplification.
pub(crate) mod quantifier_elim;
// tRust #298: Predicate abstraction for CEGAR-based verification.
pub(crate) mod predicate_abstraction;
// tRust #797: wp_transformer/ deleted — functionality migrated to trust-sunder-lib.
// tRust #304: Frame condition generation for modifies clauses.
pub(crate) mod frame_condition;
// tRust #310: Loop invariant VC generation (initiation, consecution, sufficiency, termination).
pub(crate) mod loop_invariant_gen;
// tRust #317: SSA form transformation for VC generation.
pub(crate) mod ssa_transform;
// tRust #329: Multi-pass VC simplification pipeline for solver dispatch.
pub(crate) mod vc_simplifier;
// tRust #323: Craig interpolant generation from VCs for CEGAR predicate discovery.
pub(crate) mod interpolant_gen;
// tRust #331: Proof term generation for verified VCs.
pub(crate) mod proof_term;
// tRust #338: Type state verification — valid state transitions, deadlock, reachability.
pub(crate) mod typestate;
// tRust #344: VC splitting strategies for breaking large VCs into fragments.
pub(crate) mod vc_splitting;
// tRust #337: Witness generation for verified properties.
pub(crate) mod witness_gen;
// tRust #478: Solver-agnostic proof witness extraction and validation.
pub(crate) mod witness_validate;
// tRust #792: horn_clause.rs removed — CHC generation now via chc.rs and z4/zani directly.
// tRust #792: sp.rs + sp_engine.rs removed — SP now handled by trust-sunder-lib.
// tRust #468: MIR-to-Formula coverage matrix for systematic gap analysis.
pub(crate) mod coverage;
// tRust #445: Certified translation validation with lean5-backed proof certificates.
pub(crate) mod certified_transval;
// tRust #480: Loop invariant inference via abstract interpretation widening.
pub(crate) mod loop_invariant;
// tRust #797: function_summary.rs deleted — functionality migrated to trust-sunder-lib.
// tRust #484: Proof obligation slicing to remove irrelevant conjuncts before solving.
pub(crate) mod vc_slicing;
// tRust #486: VC strength comparison and subsumption ordering for discharge optimization.
pub(crate) mod vc_ordering;
// tRust #589: RustHorn borrow encoding for Sunder CHC-based verification.
pub(crate) mod rusthorn_encoding;
// tRust #590: Standard library function specifications for Sunder Proof Level 1.
pub(crate) mod stdlib_specs;
// tRust #792: bmc_gen.rs + chc_gen.rs removed — BMC/CHC now handled by trust-zani-lib.

use trust_types::{
    ConstValue, DiscoveredClause, Formula, Operand,
    PathMapEntry, Place, Projection, ProofLevel, Sort,
    Ty, VerifiableFunction, VerificationCondition,
};

#[cfg(test)]
use trust_types::{
    AssertMessage, AtomicOpKind, AtomicOperation, AtomicOrdering, BasicBlock,
    BinOp, BlockId, ClauseTarget, GuardCondition, LocalDecl, Rvalue,
    Statement, Terminator, VerifiableBody,
};

pub use error::VcgenError;
// tRust #703: Re-export the unified Result alias for crate consumers.
pub use error::Result as VcgenResult;

// tRust: Re-export cross-check API (#192).
pub use cross_check::{
    CrossCheckResult, CrossCheckVerdict, CrossCheckWarning, SortClass,
    cross_check_all_vcs, cross_check_vc, full_cross_check,
    formula_free_var_count, weakening_preserves_safety, strengthen_by_dropping_assumption,
};

// tRust: Re-export quantifier tiers API (#145).
pub use quantifier_tiers::{
    ArithmeticFragment, EliminationStats, QuantifierConfig, QuantifierEliminator,
    QuantifierError, QuantifierStats, QuantifierTier, SolverStrategy, TierClassification,
    analyze_quantifiers, apply_tier_strategy, classify_fragment, classify_quantifiers,
    has_quantifiers, instantiate_universal, is_decidable_arithmetic, simplify_quantified,
    skolemize,
};

// tRust: Re-export quantifier instantiation API (#145).
pub use instantiation::{
    InstantiationConfig, InstantiationEngine, InstantiationError, InstantiationStats,
    Trigger, TriggerPattern,
};

// tRust: Re-export cross-function spec composition API (#20).
pub use specdb::{AnnotatedVc, DispositionSummary, SpecDatabase, generate_vcs_with_specs, solver_vcs};

// tRust: Re-export persistent spec database and inference engine (#140).
pub use persistent_specdb::{
    InferenceConfidence, PersistentSpecDatabase, SpecDbError, SpecDiff, SpecEntry, SpecSource,
};
pub use spec_inference::{
    InferenceResult, InferenceStrategy, InferredSpec, InferredSpecKind, SpecInferenceEngine,
};

// tRust #204: Re-export FFI summary framework API.
pub use ffi_summary::{
    FfiSummary, FfiSummaryDb, ParamContract, SafetyLevel, SideEffect,
    apply_summary, generate_ffi_vcs,
};

// tRust: Re-export interprocedural analysis API (#140, #230).
pub use interprocedural::{
    AnalysisResult, InterproceduralAnalyzer, InterproceduralSummary, SideEffects,
    analyze_functions, apply_callee_summary, compute_summary, compute_verification_order,
};

// tRust #230: Re-export call graph construction and summary store API.
pub use call_graph::{
    Scc, build_call_graph, detect_cycles, is_self_recursive, recursive_functions,
};
pub use summaries::{
    SummaryStore, substitute_callee_summary,
};

// tRust #797: recursive_verify re-exports removed — functionality migrated to trust-sunder-lib.

// tRust: Re-export modular verification API (#76, #140).
pub use modular::{
    ContractCheck, FunctionSummary, ModularVcResult, ModularVerifier, SummaryDatabase,
    generate_modular_vcs, modular_vcgen,
};

// tRust: Re-export trait contract inheritance verification API (#80).
pub use trait_verify::{ImplContract, TraitContract, verify_liskov};

// tRust #243: Re-export trait object verification with vtable modeling API.
pub use vtable_model::{
    BoundCheckResult, DynDispatchVc, MethodContract, ObjectSafetyChecker,
    ObjectSafetyMethod, ObjectSafetyViolation, TraitBoundPropagation, VtableModel,
    WitnessType,
};

// tRust #797: bounds re-exports removed — functionality migrated to trust-zani-lib.

// tRust #458: Re-export translation validation types from trust-types.
// The authoritative implementation (generate_refinement_vcs) is in trust-transval::vc_core.
pub use translation_validation::{
    CheckKind, RefinementVc, SimulationRelation, TranslationCheck,
    TranslationValidationError, infer_identity_relation,
};

// tRust: Re-export abstract interpretation API (#125, #206, #357, #452).
pub use abstract_interp::{
    AbstractDomain, AbstractInterpResult, DischargeReport, FixpointResult,
    FixpointConfig, Interval, IntervalDomain, ThresholdSet, WidenPoint,
    abstract_eval_formula, detect_widen_points, extract_invariants,
    extract_thresholds, fixpoint, fixpoint_configured, fixpoint_with_narrowing,
    type_aware_initial_state, type_to_interval,
    interval_add, interval_div, interval_mul, interval_rem, interval_shl,
    interval_shr, interval_sub, interval_bitand, interval_bitor,
    transfer_function as abstract_transfer,
    try_discharge_batch, try_discharge_vc,
    augment_batch, augment_vc_with_abstract_state, interval_domain_to_formula,
};

// tRust: Re-export value set analysis API (#125, #132).
pub use value_analysis::{
    ArrayAccess, ValueSet, ValueSetState, analyze_function, generate_vc_from_value_sets,
    is_definite_error, is_definite_safe, join_value_sets, transfer_assign,
    transfer_condition,
};

// tRust #797: memory_model, region_encoding, safe_rust_model re-exports removed —
// functionality migrated to trust-zani-lib.

// tRust #150: Re-export memory provenance API.
pub use memory_provenance::{BorrowStack, ProvenanceTracker, check_provenance};

// tRust #792: memory_bytes re-exports removed.

// tRust #191: Re-export separation logic API for unsafe code verification.
pub use separation_logic::{
    HeapCell, PointerPermission, ProvenanceId, SepFormula, SymbolicHeap, SymbolicPointer,
    address_of_sep_vc, apply_frame_rule, deref_vc, encode_framed_unsafe_block,
    encode_heap_disjointness, encode_unsafe_block, ffi_call_sep_vc,
    raw_write_vc, sep_to_formula, transmute_vc, unsafe_fn_call_sep_vc,
};

// tRust #203: Re-export data race and memory ordering verification API.
pub use data_race::{
    AccessKind, DataRacePair, MemoryOrdering, SharedAccess,
    check_ordering_sufficient, detect_potential_races, generate_ordering_vcs,
    generate_race_vcs,
};

// tRust #203: Re-export memory ordering verification API.
// tRust #619: Added HappensBeforeGraph for typed program-point HB analysis.
pub use memory_ordering::{
    AtomicAccessEntry, AtomicAccessLog, DataRaceDetector, HappensBefore,
    HappensBeforeGraph, MemoryModelCheckResult, MemoryModelChecker,
    OrderingRequirement, OrderingViolation, RaceCondition,
};

// tRust #238: Re-export ownership and borrow checking API.
pub use ownership::{
    BorrowKind, BorrowRecord, BorrowState, BorrowViolation, scan_body,
};

// tRust #792: smtlib2 re-exports removed — printers now in trust-types::smt_logic.

// tRust #241: Re-export VC simplification API.
pub use simplify::{
    SimplificationPass, SimplificationPipeline,
    BooleanSimplifyPass, ConstantFoldPass, DeadVarEliminationPass,
    boolean_simplify, constant_fold, dead_var_elimination, measure_size,
};

// tRust #227: Re-export CPA-integrated abstract domains.
pub use interval_domain::{CpaIntervalState, IntervalCpaTransfer};
pub use octagon_domain::{CpaOctagonState, OctagonTransfer};
pub use pointer_domain::{CpaPointerState, PointerTransfer};

// tRust #148: Re-export binary analysis pipeline API.
// Note: deprecated analyze_binary_default and analyze_binary_security_only
// are not re-exported — use analyze_lifted_binary_default() instead.
pub use binary_pipeline::{
    BinaryAnalysisResult, BinaryPipelineConfig, BinaryPipelineError,
    analyze_binary,
};

// tRust #816: Re-export binary lifter types for integration testing.
pub use binary_analysis::lifter::{
    AbstractInsn, AbstractOp, AbstractRegister, AbstractValue, LiftError, LiftedProgram,
    MemoryAccess, lift_to_mir,
};

// tRust #280: Re-export alias analysis API.
pub use alias_analysis::{
    AliasAnalyzer, AliasResult, AliasSet, MemoryLocation, ProjectionKind,
    refine_vc_with_alias,
};

// tRust #119: Re-export spec-based VC generation API.
pub use spec_parser::has_spec_vcs;

// tRust #329: Re-export VC simplification pipeline API.
pub use vc_simplifier::{
    SimplificationConfig, SimplificationStats, SimplifiedVc,
    VcSimplificationPass, VcSimplifier,
    expression_size, is_contradiction, is_tautology,
};

// tRust #323: Re-export interpolant generation API.
pub use interpolant_gen::{
    Interpolant, InterpolantError, InterpolantGenerator, InterpolantRequest,
    InterpolantStrength, conjoin_interpolants, extract_shared_symbols, weaken_interpolant,
};

// tRust #338: Re-export type state verification API.
pub use typestate::{
    StateProperty, StateTransition, TransitionError, TypeState, TypeStateMachine,
    TypeStateVerifier,
};

// tRust #331: Re-export proof term generation API.
pub use proof_term::{
    ProofBuilder, ProofContext, ProofError, ProofTerm,
    proof_depth, proof_size, proof_to_string, simplify_proof, validate_proof_term,
};

// tRust #337: Re-export witness generation API.
pub use witness_gen::{
    Witness, WitnessAssignment, WitnessConfig, WitnessError, WitnessGenerator, WitnessValue,
};

// tRust #478: Re-export witness validation API.
pub use witness_validate::{WitnessValidation, WitnessValidator};

// tRust #468: Re-export coverage analysis API.
pub use coverage::{
    CoverageReport, CoverageStatus, VariantCoverage, coverage_report,
};

// tRust #792: sp_engine re-exports removed — SP now in trust-sunder-lib.

// tRust #445: Re-export certified translation validation API.
pub use certified_transval::{
    BlockCertificate, CertificationError, CertificationLevel, CertifiedTranslation,
    Lean5ProofTerm, ProofJudgment, ProofJustification, TranslationCertificate,
    cross_checked_translation, proof_certified_translation, uncertified_translation,
    verify_certificate,
};

// tRust #477: Re-export VC deduplication API.
pub use dedup::{VcDeduplicator, formula_fingerprint, vc_fingerprint};

// tRust #513: Re-export binary verification adapter API.
pub use lift_adapter::{generate_binary_vcs, generate_memory_model_vcs, lift_to_verifiable};

// tRust #480: Re-export loop invariant inference API.
pub use loop_invariant::{
    InvariantInferer, LoopInvariant, LoopPattern,
    classify_loop_pattern, infer_invariant_interval,
};

// tRust #797: function_summary re-exports removed — functionality migrated to trust-sunder-lib.

// tRust #484: Re-export VC slicing API.
pub use vc_slicing::{
    SlicingStats, collect_vars, compute_slicing_stats, dependency_cone, slice_vc,
};

// tRust #486: Re-export VC strength comparison and subsumption ordering API.
pub use vc_ordering::{
    SubsumptionGraph, VcStrength, build_subsumption_graph, compare_formulas,
    discharge_subsumed,
};

// tRust #589: Re-export RustHorn borrow encoding API.
pub use rusthorn_encoding::{
    augment_chc_with_borrows, encode_borrows, encode_function_with_borrows,
};

// tRust #590: Re-export standard library specs API for Sunder verification.
pub use stdlib_specs::{FnContract, StdlibSpecs};

// tRust #792: bmc_gen re-exports removed — BMC now in trust-zani-lib.

/// Validate a function before VC generation.
///
/// tRust #163: typed error for invalid input (replaces string-based errors).
pub fn validate_function(func: &VerifiableFunction) -> Result<(), VcgenError> {
    if func.body.blocks.is_empty() {
        return Err(VcgenError::MissingBody(func.name.clone()));
    }
    Ok(())
}

/// Try to generate VCs, returning a typed error on invalid input.
///
/// tRust #163: typed error wrapper around `generate_vcs`.
pub fn try_generate_vcs(
    func: &VerifiableFunction,
) -> Result<Vec<VerificationCondition>, VcgenError> {
    validate_function(func)?;
    Ok(generate_vcs(func))
}

/// tRust: Filter VCs by verification level.
///
/// Only keeps VCs at or below the specified maximum level.
/// L0 = safety only, L1 = safety + functional, L2 = all.
#[must_use]
pub fn filter_vcs_by_level(
    vcs: Vec<VerificationCondition>,
    max_level: ProofLevel,
) -> Vec<VerificationCondition> {
    vcs.into_iter().filter(|vc| vc.kind.proof_level() <= max_level).collect()
}

// tRust #736: Core VC generation logic extracted to generate.rs.
#[cfg(not(feature = "pipeline-v2"))]
pub(crate) use generate::build_semantic_guard_map;
pub use generate::{generate_vcs, generate_vcs_with_discharge};

/// Extract discovered guard clauses from a function's MIR control flow.
///
/// Returns all guard conditions discovered from SwitchInt and Assert
/// terminators. This is the raw clause output before path accumulation.
///
/// tRust #21: Public API for guard clause discovery and JSON report output.
#[must_use]
pub fn discover_clauses(func: &VerifiableFunction) -> Vec<DiscoveredClause> {
    func.body.discovered_clauses()
}

/// Build the path map for a function, showing accumulated guards per block.
///
/// Each entry gives the conjunction of guard conditions required to reach
/// that block from the entry point.
///
/// tRust #21: Public API for path condition queries and JSON report output.
#[must_use]
pub fn build_path_map(func: &VerifiableFunction) -> Vec<PathMapEntry> {
    func.body.path_map()
}

/// Resolve the type of an operand from the function's local declarations.
///
/// tRust #458: Promoted to `pub` for use by trust-transval translation validation.
pub fn operand_ty(func: &VerifiableFunction, op: &Operand) -> Option<Ty> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            let decl = func.body.locals.get(place.local)?;
            let mut ty = decl.ty.clone();

            for proj in &place.projections {
                ty = match (proj, &ty) {
                    (Projection::Field(idx), Ty::Tuple(fields)) => fields.get(*idx)?.clone(),
                    (Projection::Field(idx), Ty::Adt { fields, .. }) => {
                        fields.get(*idx).map(|(_, t)| t.clone())?
                    }
                    (Projection::Deref, Ty::Ref { inner, .. }) => *inner.clone(),
                    // tRust #432: Deref through RawPtr yields the pointee type.
                    (Projection::Deref, Ty::RawPtr { pointee, .. }) => *pointee.clone(),
                    (Projection::Index(_), Ty::Array { elem, .. })
                    | (Projection::Index(_), Ty::Slice { elem }) => *elem.clone(),
                    _ => return None,
                };
            }
            Some(ty)
        }
        Operand::Constant(cv) => Some(match cv {
            ConstValue::Bool(_) => Ty::Bool,
            ConstValue::Int(_) => Ty::Int { width: 64, signed: true },
            // tRust #377: ConstValue::Uint now carries bit width from MIR extraction.
            ConstValue::Uint(_, w) => Ty::Int { width: *w, signed: false },
            ConstValue::Float(_) => Ty::Float { width: 64 },
            ConstValue::Unit => Ty::Unit,
            // tRust #361: Sound fallback for unknown ConstValue variants.
            // ConstValue is #[non_exhaustive], so new variants may appear.
            // Returning None (unknown type) is conservative — the caller will
            // use a default type, and VCs will be over-approximate.
            _ => return None,
        }),
        // tRust #361: Sound fallback for unknown Operand variants.
        // Operand is #[non_exhaustive], so new variants may appear.
        // Return None rather than panicking — this causes callers to skip
        // VC generation for the unknown operand, which is sound (no missed bugs,
        // just potentially missed VCs).
        _ => None,
    }
}

/// Convert a u128 discriminant/switch value into a Formula without truncation.
///
/// Values that fit in i128 become `Formula::Int` for compatibility with the
/// mathematical-integer encoding used elsewhere. Values above `i128::MAX`
/// use `Formula::UInt` to avoid silent high-bit truncation.
pub(crate) fn u128_to_formula(value: u128) -> Formula {
    match i128::try_from(value) {
        Ok(n) => Formula::Int(n),
        Err(_) => Formula::UInt(value),
    }
}

/// Convert an operand to an SMT formula variable.
/// Uses Sort::Int for integer types (mathematical integers) to enable
/// range-based overflow checking.
///
/// tRust #458: Promoted to `pub` for use by trust-transval translation validation.
pub fn operand_to_formula(func: &VerifiableFunction, op: &Operand) -> Formula {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            let name = place_to_var_name(func, place);
            let ty = operand_ty(func, op).unwrap_or(Ty::Int { width: 64, signed: false });
            let sort = match &ty {
                Ty::Bool => Sort::Bool,
                Ty::Int { .. } => Sort::Int,
                _ => Sort::from_ty(&ty),
            };
            Formula::Var(name, sort)
        }
        Operand::Constant(cv) => match cv {
            ConstValue::Bool(b) => Formula::Bool(*b),
            ConstValue::Int(n) => Formula::Int(*n),
            ConstValue::Uint(n, _) => match i128::try_from(*n) {
                Ok(n) => Formula::Int(n),
                Err(_) => Formula::UInt(*n),
            },
            ConstValue::Float(f) => Formula::Var(
                format!("float_{f}"),
                Sort::BitVec(64),
            ),
            ConstValue::Unit => Formula::Int(0),
            // tRust #361: Sound fallback for unknown ConstValue variants.
            // Produce an unconstrained symbolic variable rather than panicking.
            // This is sound: an unconstrained variable can take any value, so
            // no real bug is missed.
            _ => Formula::Var("__unknown_const".to_string(), Sort::Int),
        },
        // tRust #361: Sound fallback for unknown Operand variants.
        // Produce an unconstrained symbolic variable rather than panicking.
        _ => Formula::Var("__unknown_operand".to_string(), Sort::Int),
    }
}

/// Build a human-readable variable name from a Place.
pub(crate) fn place_to_var_name(func: &VerifiableFunction, place: &Place) -> String {
    let fallback = format!("_{}", place.local);
    let base =
        func.body.locals.get(place.local).and_then(|d| d.name.as_deref()).unwrap_or(&fallback);

    if place.projections.is_empty() {
        base.to_string()
    } else {
        let projs: Vec<String> = place
            .projections
            .iter()
            .map(|p| match p {
                Projection::Field(i) => format!(".{i}"),
                Projection::Index(i) => format!("[_{i}]"),
                Projection::Deref => "*".to_string(),
                Projection::Downcast(i) => format!("@{i}"),
                Projection::ConstantIndex { offset, from_end } => {
                    if *from_end { format!("[-{offset}]") } else { format!("[{offset}]") }
                }
                Projection::Subslice { from, to, from_end } => {
                    if *from_end { format!("[{from}..-{to}]") } else { format!("[{from}..{to}]") }
                }
                _ => "unknown".to_string(),
            })
            .collect();
        format!("{base}{}", projs.join(""))
    }
}

// tRust #475: Property-based tests for Formula simplification correctness.
#[cfg(test)]
mod formula_proptest;

#[cfg(test)]
pub(crate) mod tests;
