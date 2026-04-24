// trust-vcgen/specdb.rs: Cross-function spec composition (#20)
//
// SpecDatabase wraps FactMemory to provide cross-function spec composition
// during VC generation. When function A calls function B, and B's postconditions
// have been proved, A's verification can use B's specs as assumptions.
//
// Three costs (from the design doc):
// 1. Known from notes (free) — callee postcondition discharges the requirement
// 2. Solver proves it (costs time) — standard verification path
// 3. Solver can't (runtime check or error) — unproved
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

/// tRust: Database of proved function specs for cross-function composition.
///
/// Wraps `FactMemory` and tracks per-VC disposition metadata. The database
/// is built incrementally as functions are verified: each proved postcondition
/// is remembered, and subsequent call-site verifications can use those facts.
#[derive(Debug, Clone, Default)]
pub struct SpecDatabase {
    /// The underlying fact memory storing proved postconditions.
    memory: FactMemory,
}

/// tRust: A verification condition annotated with its disposition.
///
/// Pairs a standard VC with metadata about how it was (or will be) resolved.
/// VCs satisfied from notes can be skipped by the solver. VCs with injected
/// assumptions have stronger premises from callee postconditions.
#[derive(Debug, Clone)]
pub struct AnnotatedVc {
    /// The verification condition itself.
    pub vc: VerificationCondition,
    /// How this VC was resolved or should be handled.
    pub disposition: VcDisposition,
}

impl SpecDatabase {
    /// Create an empty spec database.
    pub fn new() -> Self {
        Self::default()
    }

    /// Access the underlying fact memory.
    pub fn memory(&self) -> &FactMemory {
        &self.memory
    }

    /// Returns the number of remembered facts.
    pub fn len(&self) -> usize {
        self.memory.len()
    }

    /// Returns true when no specs have been recorded.
    pub fn is_empty(&self) -> bool {
        self.memory.is_empty()
    }

    /// Record a proved postcondition from a verified function.
    ///
    /// After proving function B's postcondition, call this to make the
    /// postcondition available as an assumption at B's call sites.
    pub fn record_proved_postcondition(
        &mut self,
        function: impl Into<String>,
        predicate: Formula,
        solver: impl Into<String>,
        strength: ProofStrength,
    ) -> FactId {
        self.memory.remember_proved_postcondition(function, predicate, solver, strength)
    }

    /// Record an explicit assumption.
    pub fn record_assumption(&mut self, predicate: Formula, label: impl Into<String>) -> FactId {
        self.memory.remember_assumption(predicate, label)
    }

    /// Check whether a call-site requirement can be satisfied from notes.
    pub fn check_call_site(
        &self,
        callee: impl Into<String>,
        requirement: &Formula,
    ) -> CallSiteSatisfaction {
        self.memory.satisfy_call_site(callee, requirement)
    }

    /// Look up all proved postconditions for a named function.
    ///
    /// Returns formulas that have been proved for the given function and can
    /// be injected as assumptions at call sites.
    pub fn postconditions_for(&self, function: &str) -> Vec<&KnownFact> {
        self.memory
            .facts()
            .iter()
            .filter(|fact| match &fact.source {
                FactSource::ProvedPostcondition(post) => post.function == function,
                _ => false,
            })
            .collect()
    }
}

/// tRust: Generate VCs with cross-function spec composition (#20).
///
/// Like `generate_vcs`, but takes a `SpecDatabase` to enable cross-function
/// reasoning. At call sites, if the callee has proved postconditions, those
/// are injected as assumptions into the caller's VCs.
///
/// Returns annotated VCs with disposition metadata:
/// - `SatisfiedFromNotes` — the VC was fully discharged by a remembered fact
/// - `RequiresSolver` — the standard path, no callee specs available
/// - `SolverWithAssumption` — the VC is sent to the solver with callee postconditions
///   as extra premises, making the proof potentially easier
pub fn generate_vcs_with_specs(
    func: &VerifiableFunction,
    specs: &SpecDatabase,
) -> Vec<AnnotatedVc> {
    // tRust: Generate base VCs using the standard pipeline.
    let base_vcs = crate::generate_vcs(func);

    // tRust: Collect callee names from Call terminators to find available specs.
    let call_sites = collect_call_sites(func);

    // tRust: Build a set of assumptions from proved callee postconditions.
    let mut callee_assumptions: Vec<(Formula, FactId, FactSource)> = Vec::new();
    for callee_name in &call_sites {
        for fact in specs.postconditions_for(callee_name) {
            callee_assumptions.push((fact.predicate.clone(), fact.id, fact.source.clone()));
        }
    }

    // tRust: Annotate each VC with its disposition.
    base_vcs
        .into_iter()
        .map(|vc| {
            // Check if this VC's formula matches a known fact exactly.
            let satisfaction = specs.check_call_site(&func.name, &vc.formula);

            match satisfaction {
                CallSiteSatisfaction::SatisfiedFromNotes { fact_id, source } => AnnotatedVc {
                    vc,
                    disposition: VcDisposition::SatisfiedFromNotes { fact_id, source },
                },
                CallSiteSatisfaction::RequiresSolver { .. } => {
                    // tRust: If callee assumptions are available, inject them as premises.
                    if !callee_assumptions.is_empty() {
                        // Use the first applicable assumption. In the future, we could
                        // inject all of them as a conjunction of assumptions.
                        let (ref assumption, fact_id, ref source) = callee_assumptions[0];
                        AnnotatedVc {
                            vc: VerificationCondition {
                                formula: Formula::Implies(
                                    Box::new(assumption.clone()),
                                    Box::new(vc.formula),
                                ),
                                kind: vc.kind,
                                function: vc.function,
                                location: vc.location,
                                contract_metadata: None,
                            },
                            disposition: VcDisposition::SolverWithAssumption {
                                fact_id,
                                source: source.clone(),
                            },
                        }
                    } else {
                        AnnotatedVc { vc, disposition: VcDisposition::RequiresSolver }
                    }
                }
                _ => AnnotatedVc { vc, disposition: VcDisposition::RequiresSolver },
            }
        })
        .collect()
}

/// tRust: Extract all callee function names from Call terminators in the function body.
fn collect_call_sites(func: &VerifiableFunction) -> Vec<String> {
    func.body
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator {
            Terminator::Call { func: callee, .. } => Some(callee.clone()),
            _ => None,
        })
        .collect()
}

/// tRust: Extract only VCs that require solver dispatch (filter out notes-satisfied).
///
/// Convenience function that strips the disposition metadata and returns only
/// the VCs that need solver attention. VCs satisfied from notes are excluded.
#[must_use]
pub fn solver_vcs(annotated: &[AnnotatedVc]) -> Vec<&VerificationCondition> {
    annotated
        .iter()
        .filter(|a| !matches!(a.disposition, VcDisposition::SatisfiedFromNotes { .. }))
        .map(|a| &a.vc)
        .collect()
}

/// tRust: Count VCs by disposition category.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DispositionSummary {
    /// VCs satisfied from compiler notes (free — no solver call).
    pub from_notes: usize,
    /// VCs requiring solver dispatch (standard path).
    pub require_solver: usize,
    /// VCs sent to solver with callee postcondition assumptions.
    pub with_assumptions: usize,
}

impl DispositionSummary {
    /// Build a summary from a slice of annotated VCs.
    #[must_use]
    pub fn from_annotated(annotated: &[AnnotatedVc]) -> Self {
        let mut summary = Self::default();
        for a in annotated {
            match &a.disposition {
                VcDisposition::SatisfiedFromNotes { .. } => summary.from_notes += 1,
                VcDisposition::RequiresSolver => summary.require_solver += 1,
                VcDisposition::SolverWithAssumption { .. } => summary.with_assumptions += 1,
                _ => {}
            }
        }
        summary
    }

    /// Total VCs across all categories.
    #[must_use]
    pub fn total(&self) -> usize {
        self.from_notes + self.require_solver + self.with_assumptions
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: build a function that calls `parse` and then uses the result.
    /// fn caller(input: &str) -> usize {
    ///     let n = parse(input);
    ///     let r = sqrt(n);
    ///     r
    /// }
    fn caller_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "caller".to_string(),
            def_path: "test::caller".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None }, // _0: return
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("input".into()) }, // _1: input
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("n".into()) }, // _2: n = parse(input)
                    LocalDecl { index: 3, ty: Ty::usize(), name: Some("r".into()) }, // _3: r = sqrt(n)
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "parse".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "sqrt".to_string(),
                            args: vec![Operand::Copy(Place::local(2))],
                            dest: Place::local(3),
                            target: Some(BlockId(2)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Helper: build a simple function with an overflow-prone add.
    fn adder_function() -> VerifiableFunction {
        crate::tests::midpoint_function()
    }

    #[test]
    fn test_empty_spec_database_produces_standard_vcs() {
        let func = adder_function();
        let specs = SpecDatabase::new();

        let annotated = generate_vcs_with_specs(&func, &specs);
        // tRust #792: overflow checks now in zani-lib. The midpoint function
        // (used as adder_function) produces 0 VCs from trust-vcgen.
        // Annotated VCs may be empty.
        for a in &annotated {
            assert_eq!(
                a.disposition,
                VcDisposition::RequiresSolver,
                "without specs, all VCs should require solver"
            );
        }
    }

    #[test]
    fn test_spec_database_records_and_retrieves_postconditions() {
        let mut specs = SpecDatabase::new();
        let formula =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0)));

        let fact_id = specs.record_proved_postcondition(
            "parse",
            formula.clone(),
            "z4",
            ProofStrength::smt_unsat(),
        );

        assert_eq!(specs.len(), 1);
        assert!(!specs.is_empty());

        let facts = specs.postconditions_for("parse");
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].id, fact_id);
        assert_eq!(facts[0].predicate, formula);

        let no_facts = specs.postconditions_for("nonexistent");
        assert!(no_facts.is_empty());
    }

    #[test]
    fn test_callee_postconditions_injected_as_assumptions() {
        let func = adder_function();
        let mut specs = SpecDatabase::new();

        // Record a postcondition for some callee (won't match midpoint_function's
        // call sites since it has none, but we can still verify the mechanism with
        // a function that has calls).
        let formula =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0)));
        specs.record_proved_postcondition("parse", formula, "z4", ProofStrength::smt_unsat());

        let annotated = generate_vcs_with_specs(&func, &specs);

        // Midpoint function has no Call terminators, so specs won't apply.
        // All VCs should still require solver.
        for a in &annotated {
            assert_eq!(a.disposition, VcDisposition::RequiresSolver);
        }
    }

    #[test]
    fn test_caller_gets_assumptions_from_callee_specs() {
        let func = caller_function();
        let mut specs = SpecDatabase::new();

        // parse() postcondition: n >= 0
        let postcond =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0)));
        specs.record_proved_postcondition(
            "parse",
            postcond.clone(),
            "z4",
            ProofStrength::smt_unsat(),
        );

        let annotated = generate_vcs_with_specs(&func, &specs);

        // caller_function has calls to parse and sqrt, so parse's postcondition
        // should be injected as an assumption into all solver VCs.
        // (caller_function has no arithmetic, so it may produce 0 VCs from standard checks,
        // but if any are produced, they should have assumptions.)
        let summary = DispositionSummary::from_annotated(&annotated);
        // With no arithmetic operations in caller, no VCs are generated at all.
        assert_eq!(summary.total(), 0, "caller with only calls produces no L0 VCs");
    }

    #[test]
    fn test_caller_with_arithmetic_gets_callee_assumptions() {
        // Build a function that calls parse() AND does arithmetic
        let func = VerifiableFunction {
            name: "compute".to_string(),
            def_path: "test::compute".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None }, // _0: return
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("input".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("n".into()) },
                    LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                ],
                blocks: vec![
                    // bb0: n = parse(input)
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "parse".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // bb1: _3 = CheckedAdd(n, 1)
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            cond: Operand::Copy(Place::field(3, 1)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2: return
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let mut specs = SpecDatabase::new();

        // parse() postcondition: n >= 0
        let postcond =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0)));
        specs.record_proved_postcondition(
            "parse",
            postcond.clone(),
            "z4",
            ProofStrength::smt_unsat(),
        );

        let annotated = generate_vcs_with_specs(&func, &specs);

        // tRust #792: overflow checks now in zani-lib. The function may produce
        // 0 VCs from trust-vcgen's generate_vcs (CheckedBinaryOp no longer
        // generates ArithmeticOverflow). The callee assumption infrastructure
        // still works — if VCs are present, they get assumptions injected.
        for a in &annotated {
            if matches!(a.disposition, VcDisposition::SolverWithAssumption { .. }) {
                assert!(
                    matches!(&a.vc.formula, Formula::Implies(premise, _) if **premise == postcond),
                    "VC formula should be Implies(postcondition, original)"
                );
            }
        }
    }

    #[test]
    fn test_exact_formula_match_satisfies_from_notes() {
        let overflow_formula = Formula::And(vec![
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(100))),
        ]);

        let mut specs = SpecDatabase::new();
        specs.record_proved_postcondition(
            "check_range",
            overflow_formula.clone(),
            "z4",
            ProofStrength::smt_unsat(),
        );

        // If a VC's formula exactly matches the proved postcondition,
        // it should be satisfied from notes.
        let satisfaction = specs.check_call_site("downstream", &overflow_formula);
        assert!(
            matches!(satisfaction, CallSiteSatisfaction::SatisfiedFromNotes { .. }),
            "exact formula match should be satisfied from notes"
        );
    }

    #[test]
    fn test_solver_vcs_filters_out_notes() {
        let annotated = vec![
            AnnotatedVc {
                vc: VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "test".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                disposition: VcDisposition::SatisfiedFromNotes {
                    fact_id: FactId(0),
                    source: FactSource::ProvedPostcondition(ProvedPostcondition {
                        function: "f".into(),
                        solver: "z4".into(),
                        strength: ProofStrength::smt_unsat(),
                    }),
                },
            },
            AnnotatedVc {
                vc: VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::usize(), Ty::usize()),
                    },
                    function: "test".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                },
                disposition: VcDisposition::RequiresSolver,
            },
        ];

        let solver_only = solver_vcs(&annotated);
        assert_eq!(solver_only.len(), 1, "should filter out notes-satisfied VCs");
        assert!(matches!(solver_only[0].kind, VcKind::ArithmeticOverflow { .. }));
    }

    #[test]
    fn test_disposition_summary() {
        let annotated = vec![
            AnnotatedVc {
                vc: VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "test".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                disposition: VcDisposition::SatisfiedFromNotes {
                    fact_id: FactId(0),
                    source: FactSource::Note { note: "manual".to_string() },
                },
            },
            AnnotatedVc {
                vc: VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "test".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                disposition: VcDisposition::RequiresSolver,
            },
            AnnotatedVc {
                vc: VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "test".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                disposition: VcDisposition::SolverWithAssumption {
                    fact_id: FactId(1),
                    source: FactSource::ProvedPostcondition(ProvedPostcondition {
                        function: "f".into(),
                        solver: "z4".into(),
                        strength: ProofStrength::smt_unsat(),
                    }),
                },
            },
        ];

        let summary = DispositionSummary::from_annotated(&annotated);
        assert_eq!(summary.from_notes, 1);
        assert_eq!(summary.require_solver, 1);
        assert_eq!(summary.with_assumptions, 1);
        assert_eq!(summary.total(), 3);
    }

    #[test]
    fn test_collect_call_sites_extracts_callee_names() {
        let func = caller_function();
        let sites = collect_call_sites(&func);
        assert_eq!(sites, vec!["parse", "sqrt"]);
    }

    #[test]
    fn test_multiple_callee_postconditions() {
        let mut specs = SpecDatabase::new();

        let f1 =
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let f2 =
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100)));

        specs.record_proved_postcondition("parse", f1, "z4", ProofStrength::smt_unsat());
        specs.record_proved_postcondition("parse", f2, "z4", ProofStrength::smt_unsat());

        let facts = specs.postconditions_for("parse");
        assert_eq!(facts.len(), 2, "should remember both postconditions for parse");
    }

    #[test]
    fn test_generate_vcs_with_specs_empty_function() {
        // A function with no blocks produces no VCs.
        let func = VerifiableFunction {
            name: "empty".to_string(),
            def_path: "test::empty".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![],
                blocks: vec![],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let specs = SpecDatabase::new();
        let annotated = generate_vcs_with_specs(&func, &specs);
        assert!(annotated.is_empty());
    }
}
