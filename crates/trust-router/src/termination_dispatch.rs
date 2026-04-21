// tRust #194: Termination dispatch — separate termination from safety routing.
//
// PDR, k-induction, and BMC prove safety properties (AG !bad), NOT termination.
// Termination requires ranking functions, well-founded orderings, or decreases
// clauses. This module classifies properties and validates dispatch decisions.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, VcKind, VerificationCondition};

// ---------------------------------------------------------------------------
// Property classification
// ---------------------------------------------------------------------------

/// tRust #194: Semantic property kind for dispatch validation.
///
/// Safety and termination require fundamentally different proof techniques.
/// Conflating them (e.g., routing termination to PDR) produces unsound results.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum PropertyKind {
    /// Invariant holds on all reachable states (AG !bad).
    /// Provable by PDR, IC3, k-induction, BMC, SMT.
    Safety,
    /// Something good eventually happens (AF good, GF good).
    /// Requires fairness assumptions + ranking or Buchi automata.
    Liveness,
    /// All executions terminate (well-founded ordering exists).
    /// Requires ranking function synthesis, NOT safety checkers.
    Termination,
    /// If it terminates, the postcondition holds ({P} S {Q}).
    /// Provable by WP/SP calculus, deductive verification.
    PartialCorrectness,
    /// Terminates AND postcondition holds ([P] S [Q]).
    /// Requires both termination proof + partial correctness proof.
    TotalCorrectness,
}

impl PropertyKind {
    /// Returns true if this property kind requires a termination argument.
    #[must_use]
    pub fn requires_termination_proof(&self) -> bool {
        matches!(self, PropertyKind::Termination | PropertyKind::TotalCorrectness)
    }

    /// Returns true if this property can be handled by safety-only solvers.
    #[must_use]
    pub fn is_safety_compatible(&self) -> bool {
        matches!(
            self,
            PropertyKind::Safety | PropertyKind::PartialCorrectness
        )
    }
}

// ---------------------------------------------------------------------------
// Termination strategies
// ---------------------------------------------------------------------------

/// tRust #194: Strategy for proving termination.
///
/// Each strategy maps to different solver capabilities:
/// - Ranking functions: lean5 (inductive proofs), z4 (synthesis via SMT)
/// - Well-founded orderings: lean5 (ordinal arithmetic)
/// - Decreases clauses: z4 (bounded arithmetic), sunder (deductive)
/// - Bounded unrolling: zani (BMC up to bound, incomplete)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TerminationStrategy {
    /// Synthesize f: State -> Ordinal that strictly decreases on every transition.
    /// Sound and complete for single-path loops.
    RankingFunction,
    /// Prove that the transition relation is well-founded via ordinal embedding.
    /// Required for nested/mutually recursive functions.
    WellFoundedOrdering,
    /// Check user-supplied `#[decreases(...)]` clause against loop body.
    /// Most efficient when the user provides the measure.
    DecreasesClause,
    /// Unroll the loop up to `bound` iterations looking for non-termination.
    /// Incomplete: can find bugs but cannot prove termination.
    BoundedUnrolling { bound: u32 },
}

// ---------------------------------------------------------------------------
// Termination obligation
// ---------------------------------------------------------------------------

/// tRust #194: A termination proof obligation extracted from a VC.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TerminationObligation {
    /// Function containing the potentially non-terminating construct.
    pub function_name: String,
    /// Loop ID within the function (None for recursive calls).
    pub loop_id: Option<usize>,
    /// Strategy to use for the termination proof.
    pub strategy: TerminationStrategy,
    /// The formula encoding the termination condition.
    pub formula: Formula,
}

// ---------------------------------------------------------------------------
// Safety strategies — what PDR/k-induction/BMC actually prove
// ---------------------------------------------------------------------------

/// tRust #194: Strategy for proving safety properties (AG !bad).
///
/// These are the techniques that PDR, k-induction, and BMC implement.
/// They prove that bad states are unreachable — NOT that execution terminates.
///
/// Contrast with `TerminationStrategy` which handles termination proofs
/// using ranking functions and well-founded orderings.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SafetyStrategy {
    /// PDR/IC3: iteratively compute inductive invariants that block bad states.
    /// Sound and complete for finite-state safety. Proves AG !bad.
    Pdr,
    /// k-induction: base case (BMC to depth k) + inductive step (k-step invariant).
    /// Sound for safety. Proves AG !bad when an inductive invariant exists at depth k.
    KInduction { depth: u32 },
    /// Bounded model checking: explore all paths up to a depth bound.
    /// Incomplete for safety (only checks up to bound). Finds counterexamples quickly.
    Bmc { depth: u32 },
    /// Direct SMT query: encode the safety property as an SMT formula.
    /// Sound and complete for quantifier-free theories.
    DirectSmt,
    /// CEGAR predicate abstraction: refine abstract domain until the property
    /// is proved or a real counterexample is found. Proves safety via invariant.
    Cegar { max_refinements: u32 },
}

/// tRust #194: Returns true if the solver can prove safety properties (AG !bad).
///
/// All solvers listed here prove that bad states are unreachable. This is the
/// complement of `can_prove_termination` — safety-only solvers (PDR, IC3,
/// k-induction, BMC) appear here but NOT in `can_prove_termination`.
#[must_use]
pub fn can_prove_safety(solver: &str) -> bool {
    matches!(
        solver.to_lowercase().as_str(),
        "pdr" | "ic3" | "k-induction" | "k_induction" | "bmc" | "z4-chc"
            | "z4" | "lean5" | "sunder" | "zani" | "certus" | "cegar"
    )
}

/// tRust #194: Route a safety obligation to appropriate solvers.
///
/// Returns solver names in priority order. Unlike termination routing,
/// safety routing includes PDR, IC3, k-induction, and BMC — these are
/// precisely the tools that prove safety (AG !bad).
#[must_use]
pub fn route_safety(strategy: &SafetyStrategy) -> Vec<String> {
    match strategy {
        SafetyStrategy::Pdr => {
            vec!["z4-chc".to_string(), "z4".to_string()]
        }
        SafetyStrategy::KInduction { .. } => {
            vec!["z4".to_string(), "z4-chc".to_string()]
        }
        SafetyStrategy::Bmc { .. } => {
            vec!["zani".to_string(), "z4".to_string()]
        }
        SafetyStrategy::DirectSmt => {
            vec!["z4".to_string(), "sunder".to_string()]
        }
        SafetyStrategy::Cegar { .. } => {
            vec!["z4".to_string(), "z4-chc".to_string()]
        }
    }
}

// ---------------------------------------------------------------------------
// Classification
// ---------------------------------------------------------------------------

/// tRust #194: Classify a VC into its semantic property kind.
///
/// Inspects `VcKind` to determine whether the obligation is safety,
/// liveness, termination, or correctness. This classification drives
/// dispatch validation.
#[must_use]
pub fn classify_property(vc: &VerificationCondition) -> PropertyKind {
    match &vc.kind {
        // Termination
        VcKind::NonTermination { .. } => PropertyKind::Termination,

        // Liveness / temporal
        VcKind::Liveness { .. } | VcKind::Fairness { .. } => PropertyKind::Liveness,
        VcKind::Temporal { .. } => PropertyKind::Liveness,

        // Safety: all runtime-checkable panic conditions
        VcKind::ArithmeticOverflow { .. }
        | VcKind::ShiftOverflow { .. }
        | VcKind::DivisionByZero
        | VcKind::RemainderByZero
        | VcKind::IndexOutOfBounds
        | VcKind::SliceBoundsCheck
        | VcKind::CastOverflow { .. }
        | VcKind::NegationOverflow { .. }
        | VcKind::Unreachable
        | VcKind::DataRace { .. } => PropertyKind::Safety,

        // Safety: state machine deadlock / dead state
        VcKind::DeadState { .. } | VcKind::Deadlock => PropertyKind::Safety,

        // Partial correctness: contract-based
        VcKind::Precondition { .. }
        | VcKind::Postcondition
        | VcKind::TranslationValidation { .. } => PropertyKind::PartialCorrectness,

        // Safety: assertions are runtime-checkable invariants
        VcKind::Assertion { .. } => PropertyKind::Safety,

        // Safety/correctness: domain-specific
        VcKind::TaintViolation { .. }
        | VcKind::RefinementViolation { .. }
        | VcKind::ResilienceViolation { .. }
        | VcKind::ProtocolViolation { .. } => PropertyKind::Safety,

        // Safety: neural network properties are bounded safety checks
        VcKind::NeuralRobustness { .. }
        | VcKind::NeuralOutputRange { .. }
        | VcKind::NeuralLipschitz { .. }
        | VcKind::NeuralMonotonicity { .. } => PropertyKind::Safety,

        // Safety: concurrency ordering
        VcKind::InsufficientOrdering { .. } => PropertyKind::Safety,

        // tRust #433: Floating-point safety checks
        VcKind::FloatDivisionByZero | VcKind::FloatOverflowToInfinity { .. } => {
            PropertyKind::Safety
        }
        // tRust #438: Rvalue safety VCs — type-level safety checks
        VcKind::InvalidDiscriminant { .. }
        | VcKind::AggregateArrayLengthMismatch { .. } => PropertyKind::Safety,
// tRust #463: Unsafe operations are safety properties.
        VcKind::UnsafeOperation { .. } => PropertyKind::Safety,
        // tRust #546: Ownership/memory safety VcKinds
        VcKind::UseAfterFree
        | VcKind::DoubleFree
        | VcKind::AliasingViolation { .. }
        | VcKind::LifetimeViolation
        | VcKind::SendViolation
        | VcKind::SyncViolation => PropertyKind::Safety,
        // tRust #546: FFI boundary violations are safety properties.
        VcKind::FfiBoundaryViolation { .. } => PropertyKind::Safety,
        // tRust #597: Functional correctness is partial correctness.
        VcKind::FunctionalCorrectness { .. } => PropertyKind::PartialCorrectness,
        // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
        _ => PropertyKind::Safety,
    }
}

// ---------------------------------------------------------------------------
// Solver capability checks
// ---------------------------------------------------------------------------

/// tRust #194: Returns true if the solver can ONLY prove safety properties.
///
/// PDR, IC3, k-induction, and BMC prove that bad states are unreachable
/// (AG !bad). They do NOT prove termination or liveness.
#[must_use]
pub fn is_safety_only(solver: &str) -> bool {
    matches!(
        solver.to_lowercase().as_str(),
        "pdr" | "ic3" | "k-induction" | "k_induction" | "bmc" | "z4-chc"
    )
}

/// tRust #194: Returns true if the solver can handle termination proofs.
#[must_use]
pub fn can_prove_termination(solver: &str) -> bool {
    matches!(
        solver.to_lowercase().as_str(),
        "lean5" | "z4" | "sunder" | "zani"
    )
}

// ---------------------------------------------------------------------------
// Termination routing
// ---------------------------------------------------------------------------

/// tRust #194: Route a termination obligation to appropriate solvers.
///
/// Returns solver names in priority order. PDR, IC3, k-induction, and BMC
/// are explicitly excluded — they prove safety, not termination.
///
/// Routing by strategy:
/// - `RankingFunction` -> lean5 (inductive proof), z4 (synthesis)
/// - `WellFoundedOrdering` -> lean5 (ordinal arithmetic)
/// - `DecreasesClause` -> z4 (bounded check), sunder (deductive)
/// - `BoundedUnrolling` -> zani (counterexample search), z4 (bounded BMC)
#[must_use]
pub fn route_termination(obligation: &TerminationObligation) -> Vec<String> {
    match &obligation.strategy {
        TerminationStrategy::RankingFunction => {
            vec!["lean5".to_string(), "z4".to_string()]
        }
        TerminationStrategy::WellFoundedOrdering => {
            vec!["lean5".to_string()]
        }
        TerminationStrategy::DecreasesClause => {
            vec!["z4".to_string(), "sunder".to_string()]
        }
        TerminationStrategy::BoundedUnrolling { .. } => {
            vec!["zani".to_string(), "z4".to_string()]
        }
    }
}

// ---------------------------------------------------------------------------
// Dispatch validation
// ---------------------------------------------------------------------------

/// tRust #194: Result of validating a solver dispatch decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DispatchValidity {
    /// The solver can handle this property kind correctly.
    Valid,
    /// The solver fundamentally cannot handle this property kind.
    /// Dispatching to it would produce unsound or meaningless results.
    Invalid { reason: String },
    /// The solver can partially handle this but results may be incomplete.
    /// E.g., bounded unrolling for termination finds bugs but cannot prove it.
    Degraded { reason: String },
}

impl DispatchValidity {
    #[must_use]
    pub fn is_valid(&self) -> bool {
        matches!(self, DispatchValidity::Valid)
    }

    #[must_use]
    pub fn is_invalid(&self) -> bool {
        matches!(self, DispatchValidity::Invalid { .. })
    }

    #[must_use]
    pub fn is_degraded(&self) -> bool {
        matches!(self, DispatchValidity::Degraded { .. })
    }
}

/// tRust #194: Validate that a solver can handle the given property kind.
///
/// This is the core guard that prevents the bug described in issue #194:
/// routing termination obligations to PDR/k-induction/BMC, which only
/// prove safety.
#[must_use]
pub fn validate_dispatch(property: PropertyKind, solver: &str) -> DispatchValidity {
    let solver_lower = solver.to_lowercase();
    let solver_str = solver_lower.as_str();

    match property {
        PropertyKind::Safety => {
            // All solvers can handle safety to some degree.
            DispatchValidity::Valid
        }

        PropertyKind::Termination => {
            if is_safety_only(solver_str) {
                DispatchValidity::Invalid {
                    reason: format!(
                        "{solver} proves safety (AG !bad), not termination. \
                         Use ranking function synthesis (lean5, z4) instead."
                    ),
                }
            } else if solver_str == "zani" {
                // zani can find non-termination bugs via bounded unrolling
                // but cannot prove termination.
                DispatchValidity::Degraded {
                    reason: format!(
                        "{solver} can detect non-termination via lasso witnesses \
                         but cannot prove termination. Use lean5 or z4 for proofs."
                    ),
                }
            } else if solver_str == "lean5" || solver_str == "z4" || solver_str == "sunder" {
                DispatchValidity::Valid
            } else {
                DispatchValidity::Degraded {
                    reason: format!(
                        "{solver} has unknown termination proving capability."
                    ),
                }
            }
        }

        PropertyKind::Liveness => {
            if is_safety_only(solver_str) {
                DispatchValidity::Invalid {
                    reason: format!(
                        "{solver} proves safety only. Liveness requires \
                         fairness assumptions + ranking or Buchi automata. Use tla2."
                    ),
                }
            } else if solver_str == "tla2" || solver_str == "lean5" {
                DispatchValidity::Valid
            } else {
                DispatchValidity::Degraded {
                    reason: format!(
                        "{solver} may not fully support liveness checking."
                    ),
                }
            }
        }

        PropertyKind::PartialCorrectness => {
            // Most solvers can handle partial correctness (WP/SP).
            DispatchValidity::Valid
        }

        PropertyKind::TotalCorrectness => {
            if is_safety_only(solver_str) {
                DispatchValidity::Invalid {
                    reason: format!(
                        "{solver} proves safety only. Total correctness requires \
                         termination proof + partial correctness. Use lean5."
                    ),
                }
            } else if solver_str == "lean5" {
                DispatchValidity::Valid
            } else if solver_str == "z4" || solver_str == "sunder" {
                DispatchValidity::Degraded {
                    reason: format!(
                        "{solver} can handle the partial correctness component \
                         but may need lean5 for the termination component."
                    ),
                }
            } else {
                DispatchValidity::Degraded {
                    reason: format!(
                        "{solver} has unknown total correctness capability."
                    ),
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::*;

    /// Helper: build a VC with the given kind.
    fn make_vc(kind: VcKind) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "test_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    // -------------------------------------------------------------------
    // classify_property tests
    // -------------------------------------------------------------------

    #[test]
    fn test_classify_safety_division_by_zero() {
        let vc = make_vc(VcKind::DivisionByZero);
        assert_eq!(classify_property(&vc), PropertyKind::Safety);
    }

    #[test]
    fn test_classify_safety_arithmetic_overflow() {
        let vc = make_vc(VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        });
        assert_eq!(classify_property(&vc), PropertyKind::Safety);
    }

    #[test]
    fn test_classify_safety_index_out_of_bounds() {
        let vc = make_vc(VcKind::IndexOutOfBounds);
        assert_eq!(classify_property(&vc), PropertyKind::Safety);
    }

    #[test]
    fn test_classify_safety_assertion() {
        let vc = make_vc(VcKind::Assertion {
            message: "loop invariant".to_string(),
        });
        assert_eq!(classify_property(&vc), PropertyKind::Safety);
    }

    #[test]
    fn test_classify_termination_non_termination() {
        let vc = make_vc(VcKind::NonTermination {
            context: "loop".to_string(),
            measure: "n".to_string(),
        });
        assert_eq!(classify_property(&vc), PropertyKind::Termination);
    }

    #[test]
    fn test_classify_liveness_temporal() {
        let vc = make_vc(VcKind::Temporal {
            property: "eventually done".to_string(),
        });
        assert_eq!(classify_property(&vc), PropertyKind::Liveness);
    }

    #[test]
    fn test_classify_liveness_fairness() {
        let vc = make_vc(VcKind::Fairness {
            constraint: FairnessConstraint::Strong {
                action: "sched".to_string(), vars: vec!["x".to_string()],
            },
        });
        assert_eq!(classify_property(&vc), PropertyKind::Liveness);
    }

    #[test]
    fn test_classify_partial_correctness_postcondition() {
        let vc = make_vc(VcKind::Postcondition);
        assert_eq!(classify_property(&vc), PropertyKind::PartialCorrectness);
    }

    #[test]
    fn test_classify_partial_correctness_precondition() {
        let vc = make_vc(VcKind::Precondition {
            callee: "foo".to_string(),
        });
        assert_eq!(classify_property(&vc), PropertyKind::PartialCorrectness);
    }

    #[test]
    fn test_classify_safety_data_race() {
        let vc = make_vc(VcKind::DataRace {
            variable: "x".to_string(),
            thread_a: "t1".to_string(),
            thread_b: "t2".to_string(),
        });
        assert_eq!(classify_property(&vc), PropertyKind::Safety);
    }

    // -------------------------------------------------------------------
    // is_safety_only tests
    // -------------------------------------------------------------------

    #[test]
    fn test_pdr_is_safety_only() {
        assert!(is_safety_only("pdr"));
        assert!(is_safety_only("PDR"));
    }

    #[test]
    fn test_ic3_is_safety_only() {
        assert!(is_safety_only("ic3"));
        assert!(is_safety_only("IC3"));
    }

    #[test]
    fn test_k_induction_is_safety_only() {
        assert!(is_safety_only("k-induction"));
        assert!(is_safety_only("k_induction"));
        assert!(is_safety_only("K-Induction"));
    }

    #[test]
    fn test_bmc_is_safety_only() {
        assert!(is_safety_only("bmc"));
        assert!(is_safety_only("BMC"));
    }

    #[test]
    fn test_z4_chc_is_safety_only() {
        assert!(is_safety_only("z4-chc"));
    }

    #[test]
    fn test_lean5_is_not_safety_only() {
        assert!(!is_safety_only("lean5"));
    }

    #[test]
    fn test_z4_is_not_safety_only() {
        assert!(!is_safety_only("z4"));
    }

    // -------------------------------------------------------------------
    // route_termination tests
    // -------------------------------------------------------------------

    #[test]
    fn test_route_ranking_function_prefers_lean5() {
        let obligation = TerminationObligation {
            function_name: "loop_fn".to_string(),
            loop_id: Some(0),
            strategy: TerminationStrategy::RankingFunction,
            formula: Formula::Bool(true),
        };
        let solvers = route_termination(&obligation);
        assert_eq!(solvers, vec!["lean5", "z4"]);
        // PDR/k-induction/BMC must never appear
        for s in &solvers {
            assert!(!is_safety_only(s), "{s} is safety-only but was routed for termination");
        }
    }

    #[test]
    fn test_route_well_founded_ordering_lean5_only() {
        let obligation = TerminationObligation {
            function_name: "mutual_rec".to_string(),
            loop_id: None,
            strategy: TerminationStrategy::WellFoundedOrdering,
            formula: Formula::Bool(true),
        };
        let solvers = route_termination(&obligation);
        assert_eq!(solvers, vec!["lean5"]);
    }

    #[test]
    fn test_route_decreases_clause_z4_sunder() {
        let obligation = TerminationObligation {
            function_name: "countdown".to_string(),
            loop_id: Some(1),
            strategy: TerminationStrategy::DecreasesClause,
            formula: Formula::Bool(true),
        };
        let solvers = route_termination(&obligation);
        assert_eq!(solvers, vec!["z4", "sunder"]);
        for s in &solvers {
            assert!(!is_safety_only(s));
        }
    }

    #[test]
    fn test_route_bounded_unrolling_zani_z4() {
        let obligation = TerminationObligation {
            function_name: "maybe_loops".to_string(),
            loop_id: Some(0),
            strategy: TerminationStrategy::BoundedUnrolling { bound: 100 },
            formula: Formula::Bool(true),
        };
        let solvers = route_termination(&obligation);
        assert_eq!(solvers, vec!["zani", "z4"]);
    }

    #[test]
    fn test_route_termination_never_returns_safety_only_solver() {
        let strategies = [
            TerminationStrategy::RankingFunction,
            TerminationStrategy::WellFoundedOrdering,
            TerminationStrategy::DecreasesClause,
            TerminationStrategy::BoundedUnrolling { bound: 50 },
        ];
        for strategy in strategies {
            let obligation = TerminationObligation {
                function_name: "fn".to_string(),
                loop_id: None,
                strategy,
                formula: Formula::Bool(true),
            };
            for solver in route_termination(&obligation) {
                assert!(
                    !is_safety_only(&solver),
                    "route_termination returned safety-only solver: {solver}"
                );
            }
        }
    }

    // -------------------------------------------------------------------
    // validate_dispatch tests
    // -------------------------------------------------------------------

    #[test]
    fn test_validate_pdr_for_safety_is_valid() {
        let result = validate_dispatch(PropertyKind::Safety, "pdr");
        assert!(result.is_valid());
    }

    #[test]
    fn test_validate_pdr_for_termination_is_invalid() {
        let result = validate_dispatch(PropertyKind::Termination, "pdr");
        assert!(result.is_invalid(), "PDR must not handle termination: {result:?}");
    }

    #[test]
    fn test_validate_k_induction_for_termination_is_invalid() {
        let result = validate_dispatch(PropertyKind::Termination, "k-induction");
        assert!(result.is_invalid());
    }

    #[test]
    fn test_validate_bmc_for_termination_is_invalid() {
        let result = validate_dispatch(PropertyKind::Termination, "BMC");
        assert!(result.is_invalid());
    }

    #[test]
    fn test_validate_ic3_for_liveness_is_invalid() {
        let result = validate_dispatch(PropertyKind::Liveness, "ic3");
        assert!(result.is_invalid());
    }

    #[test]
    fn test_validate_lean5_for_termination_is_valid() {
        let result = validate_dispatch(PropertyKind::Termination, "lean5");
        assert!(result.is_valid());
    }

    #[test]
    fn test_validate_z4_for_termination_is_valid() {
        let result = validate_dispatch(PropertyKind::Termination, "z4");
        assert!(result.is_valid());
    }

    #[test]
    fn test_validate_zani_for_termination_is_degraded() {
        let result = validate_dispatch(PropertyKind::Termination, "zani");
        assert!(result.is_degraded(), "zani can find bugs but not prove termination: {result:?}");
    }

    #[test]
    fn test_validate_tla2_for_liveness_is_valid() {
        let result = validate_dispatch(PropertyKind::Liveness, "tla2");
        assert!(result.is_valid());
    }

    #[test]
    fn test_validate_pdr_for_total_correctness_is_invalid() {
        let result = validate_dispatch(PropertyKind::TotalCorrectness, "pdr");
        assert!(result.is_invalid());
    }

    #[test]
    fn test_validate_lean5_for_total_correctness_is_valid() {
        let result = validate_dispatch(PropertyKind::TotalCorrectness, "lean5");
        assert!(result.is_valid());
    }

    // -------------------------------------------------------------------
    // PropertyKind helper tests
    // -------------------------------------------------------------------

    #[test]
    fn test_property_kind_requires_termination_proof() {
        assert!(PropertyKind::Termination.requires_termination_proof());
        assert!(PropertyKind::TotalCorrectness.requires_termination_proof());
        assert!(!PropertyKind::Safety.requires_termination_proof());
        assert!(!PropertyKind::Liveness.requires_termination_proof());
        assert!(!PropertyKind::PartialCorrectness.requires_termination_proof());
    }

    #[test]
    fn test_property_kind_is_safety_compatible() {
        assert!(PropertyKind::Safety.is_safety_compatible());
        assert!(PropertyKind::PartialCorrectness.is_safety_compatible());
        assert!(!PropertyKind::Termination.is_safety_compatible());
        assert!(!PropertyKind::Liveness.is_safety_compatible());
        assert!(!PropertyKind::TotalCorrectness.is_safety_compatible());
    }

    // -------------------------------------------------------------------
    // Integration: classify + validate roundtrip
    // -------------------------------------------------------------------

    #[test]
    fn test_non_termination_vc_rejected_by_all_safety_solvers() {
        let vc = make_vc(VcKind::NonTermination {
            context: "while loop".to_string(),
            measure: "n".to_string(),
        });
        let property = classify_property(&vc);
        assert_eq!(property, PropertyKind::Termination);

        let safety_solvers = ["pdr", "ic3", "k-induction", "bmc", "z4-chc"];
        for solver in safety_solvers {
            let validity = validate_dispatch(property, solver);
            assert!(
                validity.is_invalid(),
                "{solver} should be invalid for termination but got: {validity:?}"
            );
        }
    }

    #[test]
    fn test_safety_vc_accepted_by_all_solvers() {
        let vc = make_vc(VcKind::DivisionByZero);
        let property = classify_property(&vc);
        assert_eq!(property, PropertyKind::Safety);

        let all_solvers = ["pdr", "ic3", "k-induction", "bmc", "z4", "lean5", "zani", "sunder", "tla2"];
        for solver in all_solvers {
            let validity = validate_dispatch(property, solver);
            assert!(
                validity.is_valid(),
                "{solver} should be valid for safety but got: {validity:?}"
            );
        }
    }

    // -------------------------------------------------------------------
    // can_prove_safety tests (#194)
    // -------------------------------------------------------------------

    #[test]
    fn test_all_safety_only_solvers_can_prove_safety() {
        let safety_only = ["pdr", "ic3", "k-induction", "k_induction", "bmc", "z4-chc"];
        for solver in safety_only {
            assert!(
                can_prove_safety(solver),
                "{solver} is safety-only but can_prove_safety returned false"
            );
        }
    }

    #[test]
    fn test_termination_capable_solvers_can_also_prove_safety() {
        let termination_solvers = ["z4", "lean5", "sunder", "zani"];
        for solver in termination_solvers {
            assert!(
                can_prove_safety(solver),
                "{solver} can prove termination but not safety?"
            );
        }
    }

    #[test]
    fn test_safety_only_solvers_cannot_prove_termination() {
        let safety_only = ["pdr", "ic3", "k-induction", "bmc", "z4-chc"];
        for solver in safety_only {
            assert!(
                !can_prove_termination(solver),
                "{solver} is safety-only but can_prove_termination returned true"
            );
            assert!(
                is_safety_only(solver),
                "{solver} should be classified as safety-only"
            );
        }
    }

    // -------------------------------------------------------------------
    // SafetyStrategy tests (#194)
    // -------------------------------------------------------------------

    #[test]
    fn test_safety_strategy_pdr_routes_to_z4_chc() {
        let solvers = route_safety(&SafetyStrategy::Pdr);
        assert_eq!(solvers[0], "z4-chc");
        assert!(solvers.contains(&"z4".to_string()));
    }

    #[test]
    fn test_safety_strategy_k_induction_routes_to_z4() {
        let solvers = route_safety(&SafetyStrategy::KInduction { depth: 10 });
        assert_eq!(solvers[0], "z4");
    }

    #[test]
    fn test_safety_strategy_bmc_routes_to_zani() {
        let solvers = route_safety(&SafetyStrategy::Bmc { depth: 100 });
        assert_eq!(solvers[0], "zani");
    }

    #[test]
    fn test_safety_strategy_direct_smt_routes_to_z4() {
        let solvers = route_safety(&SafetyStrategy::DirectSmt);
        assert_eq!(solvers[0], "z4");
    }

    #[test]
    fn test_safety_strategy_cegar_routes_to_z4() {
        let solvers = route_safety(&SafetyStrategy::Cegar { max_refinements: 50 });
        assert_eq!(solvers[0], "z4");
    }

    #[test]
    fn test_safety_routes_never_return_termination_only_solvers() {
        let strategies = [
            SafetyStrategy::Pdr,
            SafetyStrategy::KInduction { depth: 10 },
            SafetyStrategy::Bmc { depth: 100 },
            SafetyStrategy::DirectSmt,
            SafetyStrategy::Cegar { max_refinements: 50 },
        ];
        for strategy in &strategies {
            for solver in route_safety(strategy) {
                assert!(
                    can_prove_safety(&solver),
                    "route_safety returned solver that cannot prove safety: {solver}"
                );
            }
        }
    }

    // -------------------------------------------------------------------
    // Cross-concern: termination routing never includes safety-only solvers
    // -------------------------------------------------------------------

    #[test]
    fn test_termination_and_safety_routing_are_disjoint_for_safety_only() {
        let strategies = [
            TerminationStrategy::RankingFunction,
            TerminationStrategy::WellFoundedOrdering,
            TerminationStrategy::DecreasesClause,
            TerminationStrategy::BoundedUnrolling { bound: 50 },
        ];
        let safety_only_solvers = ["pdr", "ic3", "k-induction", "bmc", "z4-chc"];

        for strategy in &strategies {
            let obligation = TerminationObligation {
                function_name: "fn".to_string(),
                loop_id: None,
                strategy: strategy.clone(),
                formula: Formula::Bool(true),
            };
            let termination_solvers = route_termination(&obligation);
            for safety_solver in &safety_only_solvers {
                assert!(
                    !termination_solvers.contains(&safety_solver.to_string()),
                    "safety-only solver {safety_solver} appeared in termination routing for {strategy:?}"
                );
            }
        }
    }

    // -------------------------------------------------------------------
    // DispatchValidity helper method tests
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_validity_methods_are_mutually_exclusive() {
        let valid = DispatchValidity::Valid;
        assert!(valid.is_valid());
        assert!(!valid.is_invalid());
        assert!(!valid.is_degraded());

        let invalid = DispatchValidity::Invalid {
            reason: "test".to_string(),
        };
        assert!(!invalid.is_valid());
        assert!(invalid.is_invalid());
        assert!(!invalid.is_degraded());

        let degraded = DispatchValidity::Degraded {
            reason: "test".to_string(),
        };
        assert!(!degraded.is_valid());
        assert!(!degraded.is_invalid());
        assert!(degraded.is_degraded());
    }
}
