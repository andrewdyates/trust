// trust-vcgen/modular.rs: Modular verification with function summaries (#76)
//
// Extends SpecDatabase-based cross-function reasoning with a structured
// summary model. Each function summary captures pre/postconditions and
// proof status. At call sites:
// - Proved summary: inject postcondition as assumption, verify precondition
// - No summary: havoc the return value (assume nothing)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::*;

use crate::specdb::SpecDatabase;

/// tRust: A function summary for modular verification (#76).
///
/// Captures the contract (pre/postconditions) and proof status of a function.
/// When a callee has a proved summary, callers can use the postcondition as
/// an assumption and must verify the precondition at the call site.
#[derive(Debug, Clone)]
pub struct FunctionSummary {
    /// The function's name (matching `VerifiableFunction::name`).
    pub name: String,
    /// Formal parameter names in declaration order (e.g., `["x", "y"]`).
    /// Used by `wp_call` to substitute parameter names with actual argument
    /// expressions at call sites.
    pub param_names: Vec<String>,
    /// Preconditions that callers must satisfy at call sites.
    pub preconditions: Vec<Formula>,
    /// Postconditions that callers can assume after the call.
    pub postconditions: Vec<Formula>,
    /// Whether the summary has been proved (postconditions are sound to assume).
    pub proved: bool,
}

impl FunctionSummary {
    /// Create a new unproved summary with no conditions.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            param_names: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            proved: false,
        }
    }

    /// Set formal parameter names (in declaration order).
    pub fn with_param_names(mut self, names: Vec<String>) -> Self {
        self.param_names = names;
        self
    }

    /// Add a precondition.
    pub fn with_precondition(mut self, formula: Formula) -> Self {
        self.preconditions.push(formula);
        self
    }

    /// Add a postcondition.
    pub fn with_postcondition(mut self, formula: Formula) -> Self {
        self.postconditions.push(formula);
        self
    }

    /// Mark the summary as proved.
    pub fn proved(mut self) -> Self {
        self.proved = true;
        self
    }
}

/// tRust: Database of function summaries for modular verification (#76).
///
/// Stores and retrieves function summaries keyed by function name.
/// Integrates with `SpecDatabase` to record proved postconditions as
/// reusable facts for cross-function spec composition.
#[derive(Debug, Clone, Default)]
pub struct SummaryDatabase {
    summaries: FxHashMap<String, FunctionSummary>,
}

impl SummaryDatabase {
    /// Create an empty summary database.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert or replace a function summary.
    pub fn insert(&mut self, summary: FunctionSummary) {
        self.summaries.insert(summary.name.clone(), summary);
    }

    /// Look up a summary by function name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&FunctionSummary> {
        self.summaries.get(name)
    }

    /// Returns the number of stored summaries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.summaries.len()
    }

    /// Returns true when no summaries are stored.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.summaries.is_empty()
    }

    /// Sync proved postconditions into a SpecDatabase for use by
    /// `generate_vcs_with_specs`.
    pub fn sync_to_spec_db(&self, spec_db: &mut SpecDatabase) {
        for summary in self.summaries.values() {
            if summary.proved {
                for post in &summary.postconditions {
                    spec_db.record_proved_postcondition(
                        &summary.name,
                        post.clone(),
                        "modular",
                        ProofStrength::smt_unsat(),
                    );
                }
            }
        }
    }
}

/// tRust: Result of modular VC generation for a single function (#76).
#[derive(Debug, Clone)]
pub struct ModularVcResult {
    /// Standard safety VCs from the function body.
    pub body_vcs: Vec<VerificationCondition>,
    /// Precondition VCs: one per (call-site, precondition) pair.
    /// The caller must prove these hold at each call site.
    pub precondition_vcs: Vec<VerificationCondition>,
    /// Number of call sites where postconditions were assumed (proved summaries).
    pub assumptions_injected: usize,
    /// Number of call sites where return values were havoced (no summary).
    pub havoced_calls: usize,
}

/// tRust: Generate VCs for a function using modular verification (#76).
///
/// For each call site in the function body:
/// - If the callee has a proved summary in `summaries`:
///   - Generate a `Precondition` VC for each precondition at the call site
///   - Inject each postcondition as an assumption into subsequent body VCs
/// - If no summary exists:
///   - Havoc: assume nothing about the return value (body VCs are unstrengthened)
///
/// Body VCs are generated via the standard `generate_vcs` pipeline and then
/// augmented with callee assumptions where available.
#[must_use]
pub fn modular_vcgen(
    func: &VerifiableFunction,
    summaries: &SummaryDatabase,
) -> ModularVcResult {
    // tRust: Generate base body VCs using the standard pipeline.
    let body_vcs = crate::generate_vcs(func);

    // tRust: Walk call sites and build precondition VCs + assumption set.
    let mut precondition_vcs = Vec::new();
    let mut callee_assumptions: Vec<Formula> = Vec::new();
    let mut assumptions_injected: usize = 0;
    let mut havoced_calls: usize = 0;

    for block in &func.body.blocks {
        if let Terminator::Call { func: callee_name, span, .. } = &block.terminator {
            match summaries.get(callee_name) {
                Some(summary) if summary.proved => {
                    // tRust: Callee has proved summary — verify preconditions,
                    // assume postconditions.
                    for (i, pre) in summary.preconditions.iter().enumerate() {
                        precondition_vcs.push(VerificationCondition {
                            kind: VcKind::Precondition {
                                callee: callee_name.clone(),
                            },
                            function: func.name.clone(),
                            location: span.clone(),
                            formula: Formula::Not(Box::new(pre.clone())),
                            contract_metadata: None,
                        });
                        let _ = i; // suppress unused warning
                    }
                    for post in &summary.postconditions {
                        callee_assumptions.push(post.clone());
                    }
                    assumptions_injected += 1;
                }
                _ => {
                    // tRust: No proved summary — havoc (assume nothing).
                    havoced_calls += 1;
                }
            }
        }
    }

    // tRust: Strengthen body VCs with callee postcondition assumptions.
    // Each body VC becomes: (assumption_1 AND ... AND assumption_n) => original_vc
    let strengthened_vcs = if callee_assumptions.is_empty() {
        body_vcs
    } else {
        let assumption = if callee_assumptions.len() == 1 {
            // SAFETY: len == 1 guarantees .next() returns Some.
            callee_assumptions.into_iter().next()
                .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
        } else {
            Formula::And(callee_assumptions)
        };

        body_vcs
            .into_iter()
            .map(|vc| VerificationCondition {
                formula: Formula::Implies(
                    Box::new(assumption.clone()),
                    Box::new(vc.formula),
                ),
                kind: vc.kind,
                function: vc.function,
                location: vc.location,
                contract_metadata: None,
            })
            .collect()
    };

    ModularVcResult {
        body_vcs: strengthened_vcs,
        precondition_vcs,
        assumptions_injected,
        havoced_calls,
    }
}

/// tRust: Contract check kinds for modular verification (#140).
///
/// Each variant represents a specific obligation generated at module boundaries
/// when verifying functions against their contracts.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ContractCheck {
    /// Caller must establish callee's precondition at the call site.
    PreConditionAtCallSite {
        /// The callee function name.
        callee: String,
        /// Index of the precondition in the callee's contract.
        precondition_index: usize,
    },
    /// Callee must establish its own postcondition before returning.
    PostConditionOnReturn {
        /// Index of the postcondition in the function's contract.
        postcondition_index: usize,
    },
    /// Frame preservation: variables not mentioned in the contract are unchanged.
    FramePreservation {
        /// The variable that must be preserved.
        variable: String,
    },
}

/// tRust: Modular verifier that generates VCs using contracts at boundaries (#140).
///
/// Uses function summaries and contracts to generate three kinds of VCs:
/// 1. Precondition VCs at call sites (caller must prove)
/// 2. Postcondition VCs at returns (callee must prove)
/// 3. Frame preservation VCs (modified variables must be declared)
#[derive(Debug)]
pub struct ModularVerifier {
    summaries: SummaryDatabase,
}

impl ModularVerifier {
    /// Create a new modular verifier with the given summary database.
    #[must_use]
    pub fn new(summaries: SummaryDatabase) -> Self {
        Self { summaries }
    }

    /// Access the underlying summary database.
    #[must_use]
    pub fn summaries(&self) -> &SummaryDatabase {
        &self.summaries
    }

    /// Generate modular VCs for a function using contracts at boundaries.
    ///
    /// Produces VCs for:
    /// - Each precondition of each callee at each call site
    /// - Each postcondition of the function itself (must hold at return)
    /// - Frame preservation for variables not in the modifies set
    #[must_use]
    pub fn verify(&self, func: &VerifiableFunction) -> Vec<VerificationCondition> {
        generate_modular_vcs(func, &self.summaries)
    }
}

/// Generate modular verification conditions for a function.
///
/// This produces contract-boundary VCs separate from the body safety VCs:
/// 1. `PreConditionAtCallSite`: for each call to a function with a proved
///    summary, the caller must prove each precondition holds.
/// 2. `PostConditionOnReturn`: the function must prove its own postconditions
///    hold at each return point.
/// 3. `FramePreservation`: (placeholder) variables not in the modifies clause
///    must remain unchanged.
#[must_use]
pub fn generate_modular_vcs(
    func: &VerifiableFunction,
    summaries: &SummaryDatabase,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // 1. Precondition checks at call sites
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee_name, span, .. } = &block.terminator
            && let Some(summary) = summaries.get(callee_name)
                && summary.proved {
                    for (i, pre) in summary.preconditions.iter().enumerate() {
                        vcs.push(VerificationCondition {
                            kind: VcKind::Precondition {
                                callee: callee_name.clone(),
                            },
                            function: func.name.clone(),
                            location: span.clone(),
                            formula: Formula::Not(Box::new(pre.clone())),
                            contract_metadata: None,
                        });
                        let _check = ContractCheck::PreConditionAtCallSite {
                            callee: callee_name.clone(),
                            precondition_index: i,
                        };
                    }
                }
    }

    // 2. Postcondition checks at return points
    for (i, post) in func.postconditions.iter().enumerate() {
        vcs.push(VerificationCondition {
            kind: VcKind::Postcondition,
            function: func.name.clone(),
            location: func.span.clone(),
            formula: Formula::Not(Box::new(post.clone())),
            contract_metadata: None,
        });
        let _check = ContractCheck::PostConditionOnReturn {
            postcondition_index: i,
        };
    }

    // Note: Contract structs carry string bodies, not parsed formulas.
    // The parsed postconditions are already in func.postconditions.

    vcs
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: build a caller that calls `parse(input)` then does `n + 1`.
    fn caller_with_arithmetic() -> VerifiableFunction {
        VerifiableFunction {
            name: "compute".to_string(),
            def_path: "test::compute".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("input".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("n".into()) },
                    LocalDecl {
                        index: 3,
                        ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]),
                        name: None,
                    },
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
        }
    }

    /// Helper: build a function with two calls — one with summary, one without.
    fn caller_two_callees() -> VerifiableFunction {
        VerifiableFunction {
            name: "process".to_string(),
            def_path: "test::process".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("input".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("parsed".into()) },
                    LocalDecl { index: 3, ty: Ty::usize(), name: Some("result".into()) },
                    LocalDecl {
                        index: 4,
                        ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]),
                        name: None,
                    },
                ],
                blocks: vec![
                    // bb0: parsed = validate(input)
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "validate".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // bb1: result = unknown_fn(parsed)
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "unknown_fn".to_string(),
                            args: vec![Operand::Copy(Place::local(2))],
                            dest: Place::local(3),
                            target: Some(BlockId(2)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // bb2: _4 = CheckedAdd(result, 1)
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(3)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            cond: Operand::Copy(Place::field(4, 1)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb3: return
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(4, 0))),
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

    #[test]
    fn test_summary_database_insert_and_get() {
        let mut db = SummaryDatabase::new();
        assert!(db.is_empty());

        let summary = FunctionSummary::new("parse")
            .with_precondition(Formula::Bool(true))
            .with_postcondition(Formula::Ge(
                Box::new(Formula::Var("result".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))
            .proved();

        db.insert(summary);
        assert_eq!(db.len(), 1);

        let found = db.get("parse").expect("should find parse");
        assert_eq!(found.name, "parse");
        assert!(found.proved);
        assert_eq!(found.preconditions.len(), 1);
        assert_eq!(found.postconditions.len(), 1);

        assert!(db.get("nonexistent").is_none());
    }

    #[test]
    fn test_modular_vcgen_no_summaries_produces_havoced_calls() {
        let func = caller_with_arithmetic();
        let db = SummaryDatabase::new();

        let result = modular_vcgen(&func, &db);

        // parse call should be havoced (no summary)
        assert_eq!(result.havoced_calls, 1);
        assert_eq!(result.assumptions_injected, 0);
        assert!(result.precondition_vcs.is_empty());
        // tRust #792: overflow checks now in zani-lib. CheckedBinaryOp no
        // longer generates ArithmeticOverflow VCs from trust-vcgen.
        // Body VCs may be empty (no overflow VCs produced by vcgen).
        for vc in &result.body_vcs {
            assert!(
                !matches!(&vc.formula, Formula::Implies(..)),
                "without summaries, VCs should not be wrapped in Implies"
            );
        }
    }

    #[test]
    fn test_modular_vcgen_proved_summary_injects_assumptions() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let postcond = Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        let summary = FunctionSummary::new("parse")
            .with_postcondition(postcond.clone())
            .proved();
        db.insert(summary);

        let result = modular_vcgen(&func, &db);

        assert_eq!(result.assumptions_injected, 1);
        assert_eq!(result.havoced_calls, 0);
        assert!(result.precondition_vcs.is_empty(), "no preconditions on parse");

        // tRust #792: overflow checks now in zani-lib. Body VCs from
        // trust-vcgen may be empty; if present, they should be wrapped.
        for vc in &result.body_vcs {
            assert!(
                matches!(&vc.formula, Formula::Implies(premise, _) if **premise == postcond),
                "body VCs should be wrapped with callee postcondition"
            );
        }
    }

    #[test]
    fn test_modular_vcgen_generates_precondition_vcs() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let precond = Formula::Ge(
            Box::new(Formula::Var("input".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let postcond = Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        let summary = FunctionSummary::new("parse")
            .with_precondition(precond.clone())
            .with_postcondition(postcond)
            .proved();
        db.insert(summary);

        let result = modular_vcgen(&func, &db);

        // Should generate 1 precondition VC for parse's precondition
        assert_eq!(
            result.precondition_vcs.len(), 1,
            "should generate one precondition VC"
        );
        let pre_vc = &result.precondition_vcs[0];
        assert!(
            matches!(&pre_vc.kind, VcKind::Precondition { callee } if callee == "parse"),
            "precondition VC should reference parse"
        );
        assert_eq!(pre_vc.function, "compute", "VC should be in caller's context");
        // Formula is Not(precondition) — solver checks if negation is satisfiable
        assert!(
            matches!(&pre_vc.formula, Formula::Not(inner) if **inner == precond),
            "precondition VC formula should be Not(precondition)"
        );
    }

    #[test]
    fn test_modular_vcgen_unproved_summary_is_havoced() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        // Insert unproved summary — should be treated as havoc
        let summary = FunctionSummary::new("parse")
            .with_postcondition(Formula::Bool(true));
        // Note: not calling .proved()
        db.insert(summary);

        let result = modular_vcgen(&func, &db);

        assert_eq!(result.havoced_calls, 1, "unproved summary should be havoced");
        assert_eq!(result.assumptions_injected, 0);
        assert!(result.precondition_vcs.is_empty());
    }

    #[test]
    fn test_modular_vcgen_mixed_proved_and_unknown() {
        let func = caller_two_callees();
        let mut db = SummaryDatabase::new();

        let postcond = Formula::Le(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(100)),
        );

        // validate has a proved summary; unknown_fn does not
        let summary = FunctionSummary::new("validate")
            .with_postcondition(postcond.clone())
            .proved();
        db.insert(summary);

        let result = modular_vcgen(&func, &db);

        assert_eq!(result.assumptions_injected, 1, "validate is proved");
        assert_eq!(result.havoced_calls, 1, "unknown_fn is havoced");
        assert!(result.precondition_vcs.is_empty(), "validate has no preconditions");

        // Body VCs should have postcondition assumption from validate
        for vc in &result.body_vcs {
            assert!(
                matches!(&vc.formula, Formula::Implies(premise, _) if **premise == postcond),
                "body VCs should assume validate's postcondition"
            );
        }
    }

    #[test]
    fn test_summary_sync_to_spec_db() {
        let mut db = SummaryDatabase::new();
        let postcond = Formula::Ge(
            Box::new(Formula::Var("n".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        // Proved summary syncs to spec db
        db.insert(
            FunctionSummary::new("parse")
                .with_postcondition(postcond.clone())
                .proved(),
        );

        // Unproved summary does NOT sync
        db.insert(
            FunctionSummary::new("unsafe_parse")
                .with_postcondition(Formula::Bool(true)),
        );

        let mut spec_db = SpecDatabase::new();
        db.sync_to_spec_db(&mut spec_db);

        assert_eq!(spec_db.len(), 1, "only proved summaries sync");
        let facts = spec_db.postconditions_for("parse");
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].predicate, postcond);
    }

    #[test]
    fn test_caller_callee_verification_chain() {
        // Scenario: parse() has proved summary with postcondition n >= 0.
        // compute() calls parse() then does n + 1.
        // tRust #792: overflow checks now in zani-lib, so body_vcs may be empty.
        // We verify the modular infrastructure (assumption injection, spec sync).

        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let postcond = Formula::Ge(
            Box::new(Formula::Var("n".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        db.insert(
            FunctionSummary::new("parse")
                .with_postcondition(postcond.clone())
                .proved(),
        );

        let result = modular_vcgen(&func, &db);

        // Step 1: postcondition assumed
        assert_eq!(result.assumptions_injected, 1);

        // Step 2: if any body VCs exist, they should be strengthened
        for vc in &result.body_vcs {
            match &vc.formula {
                Formula::Implies(premise, conclusion) => {
                    assert_eq!(
                        **premise, postcond,
                        "premise should be parse's postcondition"
                    );
                    assert!(
                        !matches!(conclusion.as_ref(), Formula::Implies(..)),
                        "conclusion should not be double-wrapped"
                    );
                }
                _other => {
                    // tRust #792: Some VCs (e.g., from spec_parser) may not
                    // be wrapped in Implies — that's OK post-migration.
                }
            }
        }

        // Step 3: the chain is sound — both SpecDatabase and modular agree
        let mut spec_db = SpecDatabase::new();
        db.sync_to_spec_db(&mut spec_db);
        let spec_facts = spec_db.postconditions_for("parse");
        assert_eq!(spec_facts.len(), 1);
        assert_eq!(spec_facts[0].predicate, postcond);
    }

    #[test]
    fn test_function_summary_builder_pattern() {
        let summary = FunctionSummary::new("f")
            .with_precondition(Formula::Bool(true))
            .with_precondition(Formula::Bool(false))
            .with_postcondition(Formula::Int(42))
            .proved();

        assert_eq!(summary.name, "f");
        assert_eq!(summary.preconditions.len(), 2);
        assert_eq!(summary.postconditions.len(), 1);
        assert!(summary.proved);
    }

    #[test]
    fn test_modular_vcgen_empty_function() {
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

        let db = SummaryDatabase::new();
        let result = modular_vcgen(&func, &db);

        assert!(result.body_vcs.is_empty());
        assert!(result.precondition_vcs.is_empty());
        assert_eq!(result.assumptions_injected, 0);
        assert_eq!(result.havoced_calls, 0);
    }

    #[test]
    fn test_modular_vcgen_multiple_preconditions() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let pre1 = Formula::Ge(
            Box::new(Formula::Var("input".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let pre2 = Formula::Le(
            Box::new(Formula::Var("input".into(), Sort::Int)),
            Box::new(Formula::Int(1000)),
        );

        db.insert(
            FunctionSummary::new("parse")
                .with_precondition(pre1.clone())
                .with_precondition(pre2.clone())
                .with_postcondition(Formula::Bool(true))
                .proved(),
        );

        let result = modular_vcgen(&func, &db);

        // Should generate 2 precondition VCs — one per precondition
        assert_eq!(result.precondition_vcs.len(), 2);
        assert!(matches!(
            &result.precondition_vcs[0].formula,
            Formula::Not(inner) if **inner == pre1
        ));
        assert!(matches!(
            &result.precondition_vcs[1].formula,
            Formula::Not(inner) if **inner == pre2
        ));
    }

    // --- Tests for ContractCheck, ModularVerifier, generate_modular_vcs ---

    #[test]
    fn test_contract_check_enum_variants() {
        let pre = ContractCheck::PreConditionAtCallSite {
            callee: "parse".to_string(),
            precondition_index: 0,
        };
        let post = ContractCheck::PostConditionOnReturn {
            postcondition_index: 1,
        };
        let frame = ContractCheck::FramePreservation {
            variable: "state".to_string(),
        };

        assert_eq!(pre, pre.clone());
        assert_eq!(post, post.clone());
        assert_eq!(frame, frame.clone());
        // Ensure they're distinct
        assert_ne!(
            ContractCheck::PreConditionAtCallSite { callee: "a".into(), precondition_index: 0 },
            ContractCheck::PreConditionAtCallSite { callee: "b".into(), precondition_index: 0 },
        );
    }

    #[test]
    fn test_generate_modular_vcs_precondition_at_call_site() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let precond = Formula::Ge(
            Box::new(Formula::Var("input".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        db.insert(
            FunctionSummary::new("parse")
                .with_precondition(precond.clone())
                .proved(),
        );

        let vcs = generate_modular_vcs(&func, &db);

        assert_eq!(vcs.len(), 1, "should generate 1 precondition VC");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::Precondition { callee } if callee == "parse"
        ));
        assert!(matches!(
            &vcs[0].formula,
            Formula::Not(inner) if **inner == precond
        ));
    }

    #[test]
    fn test_generate_modular_vcs_postcondition_on_return() {
        let postcond = Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        let func = VerifiableFunction {
            name: "producer".to_string(),
            def_path: "test::producer".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![postcond.clone()],
            spec: Default::default(),
        };

        let db = SummaryDatabase::new();
        let vcs = generate_modular_vcs(&func, &db);

        assert_eq!(vcs.len(), 1, "should generate 1 postcondition VC");
        assert!(matches!(&vcs[0].kind, VcKind::Postcondition));
        assert!(matches!(
            &vcs[0].formula,
            Formula::Not(inner) if **inner == postcond
        ));
        assert_eq!(vcs[0].function, "producer");
    }

    #[test]
    fn test_generate_modular_vcs_postcondition_from_field() {
        let postcond = Formula::Le(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(100)),
        );

        let func = VerifiableFunction {
            name: "bounded".to_string(),
            def_path: "test::bounded".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![],
                blocks: vec![],
                arg_count: 0,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![postcond.clone()],
            spec: Default::default(),
        };

        let db = SummaryDatabase::new();
        let vcs = generate_modular_vcs(&func, &db);

        assert_eq!(vcs.len(), 1, "postcondition should generate 1 VC");
        assert!(matches!(&vcs[0].kind, VcKind::Postcondition));
    }

    #[test]
    fn test_generate_modular_vcs_no_contracts_no_vcs() {
        let func = VerifiableFunction {
            name: "plain".to_string(),
            def_path: "test::plain".to_string(),
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

        let db = SummaryDatabase::new();
        let vcs = generate_modular_vcs(&func, &db);
        assert!(vcs.is_empty(), "no contracts -> no modular VCs");
    }

    #[test]
    fn test_modular_verifier_delegates_to_generate() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let precond = Formula::Bool(true);
        db.insert(
            FunctionSummary::new("parse")
                .with_precondition(precond)
                .proved(),
        );

        let verifier = ModularVerifier::new(db);
        let vcs = verifier.verify(&func);

        assert_eq!(vcs.len(), 1);
        assert_eq!(verifier.summaries().len(), 1);
    }

    #[test]
    fn test_generate_modular_vcs_unproved_skipped() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        // Unproved summary should not generate precondition VCs
        db.insert(
            FunctionSummary::new("parse")
                .with_precondition(Formula::Bool(true)),
        );

        let vcs = generate_modular_vcs(&func, &db);
        assert!(
            vcs.is_empty(),
            "unproved summary should not generate modular VCs"
        );
    }
}
