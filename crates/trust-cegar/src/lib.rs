// dead_code audit: crate-level suppression removed (#939)
//! trust-cegar: Counterexample-guided abstraction refinement for tRust
//!
//! Ports CPAchecker's CEGAR approach into the tRust verification pipeline.
//! Key technique from SV-COMP winners: start with coarse abstraction,
//! refine predicates when spurious counterexamples are found.
//!
//! Architecture:
//!   predicate.rs           — Predicate types, AbstractState, abstract transfer function
//!   predicate_discovery.rs — PredicateSet, automatic predicate discovery + ranking
//!   abstraction.rs         — AbstractDomain trait, Boolean/Cartesian abstractions
//!   strategy.rs            — RefinementStrategy selection based on VC complexity
//!   refinement.rs          — CegarLoop: check → refine → iterate
//!   lazy.rs                — LazyRefiner: refine only along counterexample paths
//!   interpolation.rs       — Craig interpolation from unsat cores
//!   z4_bridge.rs           — SMT-LIB2 generation + unsat core parsing
//!   chc.rs                 — Constrained Horn Clause encoding for loops
//!   spacer.rs              — z4 Spacer bridge for CHC solving
//!   invariant_extract.rs   — Loop invariant extraction from Spacer solutions
//!   chc_cegar.rs           — CHC/Spacer integration with CEGAR loop
//!   rust_abstraction.rs    — Rust-specific abstraction domains (ownership, lifetime, type)
//!   cegar_loop.rs          — Full CEGAR loop driver: abstract → check → refine → repeat
//!   cpa.rs                 — CPA framework for composable analysis
//!   portfolio.rs           — Adaptive verification portfolio
//!   spurious_refine/       — Spurious counterexample refinement inner loop (#362)
//!   error.rs               — CegarError with thiserror
//!
//! Reference: refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod abstract_lattice; // tRust: Abstract domain lattice operations (#330)
pub(crate) mod abstraction;
pub(crate) mod cegar_loop; // tRust: Full CEGAR lazy refinement loop driver (#228)
pub(crate) mod chc; // tRust: CHC encoding for loop invariant inference (#147)
pub(crate) mod chc_cegar; // tRust: CHC/Spacer integration with CEGAR loop (#147)
pub(crate) mod cpa; // tRust: CPA framework for composable analysis (#103)
pub(crate) mod error;
pub(crate) mod ic3;
pub(crate) mod interpolation;
pub(crate) mod invariant_extract; // tRust: loop invariant extraction from Spacer (#147)
pub(crate) mod lazy;
pub(crate) mod lazy_abstraction; // tRust: Lazy abstraction refinement with ART (#311)
pub(crate) mod pdr_certificates;
pub(crate) mod portfolio; // tRust: Adaptive verification portfolio (#179)
pub(crate) mod predicate;
pub(crate) mod predicate_abstraction; // tRust: Bitvector-based predicate abstraction domain (#240)
pub(crate) mod predicate_discovery;
pub(crate) mod predicate_refinement; // tRust: Predicate abstraction refinement (#335)
pub(crate) mod refinement;
pub(crate) mod rust_abstraction; // tRust: Rust-specific abstraction domains (#200)
pub(crate) mod sat_oracle; // tRust: SAT oracle for IC3/PDR
pub(crate) mod spacer; // tRust: z4 Spacer bridge for CHC solving (#147)
pub(crate) mod spurious_refine; // tRust: Spurious counterexample refinement inner loop (#362)
pub(crate) mod strategy;
pub(crate) mod z4_bridge;

// tRust: Abstract domain lattice operations (#330)
pub use abstract_lattice::{
    LatticeElement, SignValue, includes as lattice_includes, interval_add, interval_join,
    interval_mul, interval_widen, is_bottom as lattice_is_bottom, is_top as lattice_is_top,
    join as lattice_join, meet as lattice_meet, narrow as lattice_narrow, sign_from_interval,
    sign_join, sign_meet, widen as lattice_widen,
};
pub use abstraction::{
    AbstractDomain, BooleanAbstraction, CartesianAbstraction, CartesianValue, PredicateAbstraction,
    abstract_state, bottom_sentinel, concretize, is_bottom,
};
pub use cpa::{
    CompositeCpa, CompositeState, Cpa, CpaConfig, CpaResult, MergeStrategy, ReachedSet, cpa_analyze,
};
pub use error::CegarError;
pub use interpolation::{UnsatCore, craig_interpolant, formula_variables};
pub use lazy::LazyRefiner;
pub use predicate::{AbstractState, CmpOp, Predicate, abstract_block};
pub use predicate_abstraction::{
    BitVecState, BlockTransfer, PredicateDiscovery, abstract_state_from_concrete,
    abstract_transfer, common_variables,
};
pub use predicate_discovery::{
    AnnotatedPredicate, PredicateSet, PredicateSource, discover_predicates, rank_predicates,
};
pub use refinement::{CegarConfig, CegarLoop, CegarOutcome};
// tRust: Full CEGAR loop driver (#228)
pub use cegar_loop::{
    AbstractChecker, FeasibilityChecker, FeasibilityResult, InterpolatingRefiner, LoopConfig,
    LoopOutcome, PredicateRefiner,
};
pub use ic3::{Cube, Frame, Ic3Config, Ic3Engine, Ic3Result, TransitionSystem, ic3_check};
pub use pdr_certificates::{
    CertificateVerification, InvariantStrength, PdrCertificate, PdrJustification, PdrProofStep,
    certificate_to_proof_steps, interpolants_from_pdr, minimize_invariant,
    pretty_print_certificate, verify_certificate,
};
pub use strategy::{
    RefinementStrategy, StrategyConfig, formula_nesting_depth, select_strategy,
    select_strategy_with_config,
};
pub use z4_bridge::{UnsatCoreRequest, parse_unsat_core_response};
// tRust: CHC/Spacer re-exports (#147)
pub use chc::{
    ChcPredicate, ChcSystem, ClauseKind, HornClause, LoopEncoding, PredicateApp, encode_loop,
};
pub use chc_cegar::{
    ChcCegarConfig, ChcRefinementResult, LoopStrategy, bounded_unroll, generate_chc_script,
    get_chc_system, refine_with_chc,
};
pub use invariant_extract::{LoopInvariant, extract_invariants, parse_smtlib_expr};
pub use spacer::{
    PredicateInterpretation, SpacerConfig, SpacerResult, chc_to_smtlib2, parse_spacer_response,
};
// tRust: Rust-specific abstraction domains (#200)
pub use rust_abstraction::{
    BorrowCheckPredicate, IntervalAbstraction, LifetimeAbstraction, OwnershipAbstraction,
    OwnershipPredicate, OwnershipState, RustAbstractionDomain, TypeAbstraction,
    combined_abstraction, refine_with_rust_semantics,
};
// tRust: Adaptive verification portfolio (#179)
pub use portfolio::{
    AdaptivePortfolio, AttemptOutcome, EngineAttempt, EngineId, PortfolioConfig, PortfolioOutcome,
};
// tRust: Lazy abstraction refinement with ART (#311)
pub use lazy_abstraction::{
    AbstractReachTree, ExpansionStrategy, LazyAbstractionConfig, LazyAbstractionRefiner, TreeNode,
};
// tRust: Predicate abstraction refinement (#335)
pub use predicate_refinement::{
    AbstractionState as RefinementAbstractionState, Predicate as RefinementPredicate,
    PredicateDiscovery as RefinementDiscovery, PredicateSet as RefinementPredicateSet,
    RefinementResult, SpuriousCex,
};
// tRust: Spurious counterexample refinement inner loop (#362)
pub use spurious_refine::{
    CexCheckResult, CounterexampleChecker, InnerLoopConfig, InnerLoopOutcome, InnerLoopStats,
    InnerRefinementStrategy, SpuriousRefinementLoop,
};
