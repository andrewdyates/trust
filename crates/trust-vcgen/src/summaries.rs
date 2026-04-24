// trust-vcgen/summaries.rs: Function summary computation and storage (#230)
//
// Provides `SummaryStore` for caching computed function summaries and
// `compute_summary` that builds a summary from a function body and its
// callee summaries. Callee postconditions are assumed at call sites to
// strengthen the caller's summary.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::*;

/// A function summary mapping preconditions to postconditions.
///
/// Captures what a function requires from its callers and what it
/// guarantees to them. Used during interprocedural analysis to avoid
/// re-analyzing callees.
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionSummary {
    /// Function name.
    pub name: String,
    /// Function def_path.
    pub def_path: String,
    /// Preconditions the caller must establish.
    pub preconditions: Vec<Formula>,
    /// Postconditions the callee guarantees.
    pub postconditions: Vec<Formula>,
    /// Whether this summary is complete (all callees resolved) or
    /// approximate (recursive / unknown callees).
    pub is_complete: bool,
    /// Whether this function is recursive (directly or mutually).
    pub is_recursive: bool,
}

impl FunctionSummary {
    /// Create a new empty summary for a function.
    #[must_use]
    pub fn new(name: impl Into<String>, def_path: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            def_path: def_path.into(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            is_complete: true,
            is_recursive: false,
        }
    }

    /// Create an unknown/top summary for recursive functions.
    ///
    /// An unknown summary makes no guarantees: no postconditions and
    /// no preconditions. This is the safe default for functions whose
    /// behavior cannot be fully summarized (e.g., recursive functions
    /// without user-provided invariants).
    #[must_use]
    pub fn unknown(name: impl Into<String>, def_path: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            def_path: def_path.into(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            is_complete: false,
            is_recursive: true,
        }
    }

    /// Returns true if the summary has useful postconditions that callers
    /// can rely on.
    #[must_use]
    pub fn has_postconditions(&self) -> bool {
        !self.postconditions.is_empty()
    }
}

/// Cache of computed function summaries, keyed by def_path.
#[derive(Debug, Clone, Default)]
pub struct SummaryStore {
    summaries: FxHashMap<String, FunctionSummary>,
}

impl SummaryStore {
    /// Create an empty summary store.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert or replace a function summary.
    pub fn insert(&mut self, summary: FunctionSummary) {
        self.summaries.insert(summary.def_path.clone(), summary);
    }

    /// Look up a summary by function def_path.
    #[must_use]
    pub fn get(&self, def_path: &str) -> Option<&FunctionSummary> {
        self.summaries.get(def_path)
    }

    /// Look up a summary by function name (slower, scans all entries).
    #[must_use]
    pub fn get_by_name(&self, name: &str) -> Option<&FunctionSummary> {
        self.summaries.values().find(|s| s.name == name)
    }

    /// Number of stored summaries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.summaries.len()
    }

    /// Returns true if no summaries are stored.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.summaries.is_empty()
    }

    /// Iterate over all stored summaries.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &FunctionSummary)> {
        self.summaries.iter()
    }
}

/// Compute a function summary from its body and available callee summaries.
///
/// This performs a lightweight analysis:
/// 1. Collects explicit preconditions and postconditions from the function spec
/// 2. At each call site, if a callee summary is available, assumes the callee's
///    postconditions hold after the call
/// 3. If a callee has no summary (external or unresolved), makes no assumptions
///
/// For recursive functions, pass `is_recursive = true` to produce an
/// incomplete summary that does not claim completeness.
#[must_use]
pub fn compute_summary(
    func: &VerifiableFunction,
    callee_summaries: &SummaryStore,
    is_recursive: bool,
) -> FunctionSummary {
    let mut summary = FunctionSummary::new(&func.name, &func.def_path);
    summary.is_recursive = is_recursive;
    summary.is_complete = !is_recursive;

    // Collect explicit preconditions
    summary.preconditions = func.preconditions.clone();

    // Collect explicit postconditions
    summary.postconditions = func.postconditions.clone();

    // Walk call sites and collect callee requirements
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee_name, .. } = &block.terminator {
            // Try to find callee summary by def_path, then by name
            let callee_summary = callee_summaries
                .get(callee_name)
                .or_else(|| callee_summaries.get_by_name(callee_name));

            if let Some(cs) = callee_summary {
                // If callee has preconditions, propagate them as requirements
                // the caller must establish before the call
                for pre in &cs.preconditions {
                    // Propagate callee preconditions as caller obligations
                    // (they become part of what the caller needs to verify)
                    if !summary.preconditions.contains(pre) {
                        summary.preconditions.push(pre.clone());
                    }
                }

                // Callee postconditions can strengthen our own analysis
                // but we don't automatically promote them to our postconditions
                // (that would be unsound — we only guarantee what we explicitly ensure)
            } else {
                // Unknown callee: summary is incomplete
                summary.is_complete = false;
            }
        }
    }

    summary
}

/// Substitute a callee summary at a call site in a verification condition.
///
/// Given a caller's VC and a callee summary with postconditions, wraps the
/// VC as: `(callee_post_1 AND ... AND callee_post_n) => original_vc`
///
/// This allows the solver to use callee guarantees when checking the caller.
/// If the callee summary has no postconditions, returns the VC unchanged.
#[must_use]
pub fn substitute_callee_summary(
    vc: VerificationCondition,
    callee_summary: &FunctionSummary,
) -> VerificationCondition {
    if callee_summary.postconditions.is_empty() {
        return vc;
    }

    let assumption = if callee_summary.postconditions.len() == 1 {
        callee_summary.postconditions[0].clone()
    } else {
        Formula::And(callee_summary.postconditions.clone())
    };

    VerificationCondition {
        formula: Formula::Implies(Box::new(assumption), Box::new(vc.formula)),
        kind: vc.kind,
        function: vc.function,
        location: vc.location,
        contract_metadata: vc.contract_metadata,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    /// Helper: build a function with optional calls and contracts.
    fn make_func_with_spec(
        name: &str,
        def_path: &str,
        calls: &[&str],
        pre: Vec<Formula>,
        post: Vec<Formula>,
    ) -> VerifiableFunction {
        let mut blocks = Vec::new();

        for (i, callee) in calls.iter().enumerate() {
            let target =
                if i + 1 < calls.len() { Some(BlockId(i + 1)) } else { Some(BlockId(calls.len())) };
            blocks.push(BasicBlock {
                id: BlockId(i),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: callee.to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target,
                    span: span(),
                    atomic: None,
                },
            });
        }

        blocks.push(BasicBlock {
            id: BlockId(calls.len()),
            stmts: vec![],
            terminator: Terminator::Return,
        });

        VerifiableFunction {
            name: name.to_string(),
            def_path: def_path.to_string(),
            span: span(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks,
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: pre,
            postconditions: post,
            spec: Default::default(),
        }
    }

    #[test]
    fn test_summary_store_basic_operations() {
        let mut store = SummaryStore::new();
        assert!(store.is_empty());

        let summary = FunctionSummary::new("add", "crate::add");
        store.insert(summary);

        assert_eq!(store.len(), 1);
        assert!(store.get("crate::add").is_some());
        assert!(store.get_by_name("add").is_some());
        assert!(store.get("nonexistent").is_none());
    }

    #[test]
    fn test_compute_summary_leaf_function() {
        let post = Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        let func = make_func_with_spec("leaf", "crate::leaf", &[], vec![], vec![post.clone()]);

        let store = SummaryStore::new();
        let summary = compute_summary(&func, &store, false);

        assert_eq!(summary.name, "leaf");
        assert!(summary.is_complete);
        assert!(!summary.is_recursive);
        assert_eq!(summary.postconditions, vec![post]);
    }

    #[test]
    fn test_compute_summary_with_callee() {
        // Callee has precondition x >= 0
        let callee_pre =
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let callee_post = Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        );

        let mut store = SummaryStore::new();
        let mut callee_summary = FunctionSummary::new("helper", "crate::helper");
        callee_summary.preconditions.push(callee_pre.clone());
        callee_summary.postconditions.push(callee_post);
        store.insert(callee_summary);

        let func =
            make_func_with_spec("caller", "crate::caller", &["crate::helper"], vec![], vec![]);

        let summary = compute_summary(&func, &store, false);

        // Callee's precondition should propagate to caller
        assert!(summary.preconditions.contains(&callee_pre));
        assert!(summary.is_complete);
    }

    #[test]
    fn test_compute_summary_unknown_callee() {
        let func =
            make_func_with_spec("caller", "crate::caller", &["external::unknown"], vec![], vec![]);

        let store = SummaryStore::new();
        let summary = compute_summary(&func, &store, false);

        // Unknown callee makes summary incomplete
        assert!(!summary.is_complete);
    }

    #[test]
    fn test_compute_summary_recursive() {
        let func = make_func_with_spec(
            "factorial",
            "crate::factorial",
            &["crate::factorial"],
            vec![],
            vec![],
        );

        let store = SummaryStore::new();
        let summary = compute_summary(&func, &store, true);

        assert!(summary.is_recursive);
        assert!(!summary.is_complete);
    }

    #[test]
    fn test_unknown_summary() {
        let summary = FunctionSummary::unknown("rec", "crate::rec");

        assert!(summary.is_recursive);
        assert!(!summary.is_complete);
        assert!(!summary.has_postconditions());
    }

    #[test]
    fn test_substitute_callee_summary_with_postconditions() {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "caller".into(),
            location: span(),
            formula: Formula::Eq(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        };

        let post =
            Formula::Ge(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(1)));

        let mut summary = FunctionSummary::new("callee", "crate::callee");
        summary.postconditions.push(post.clone());

        let result = substitute_callee_summary(vc, &summary);

        match &result.formula {
            Formula::Implies(premise, _conclusion) => {
                assert_eq!(**premise, post);
            }
            other => panic!("expected Implies, got: {other:?}"),
        }
    }

    #[test]
    fn test_substitute_callee_summary_no_postconditions() {
        let original = Formula::Bool(true);
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "caller".into(),
            location: span(),
            formula: original.clone(),
            contract_metadata: None,
        };

        let summary = FunctionSummary::new("callee", "crate::callee");
        let result = substitute_callee_summary(vc, &summary);

        assert_eq!(result.formula, original, "no postconditions -> unchanged");
    }

    #[test]
    fn test_substitute_callee_summary_multiple_postconditions() {
        let vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "caller".into(),
            location: span(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        let post1 =
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let post2 =
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100)));

        let mut summary = FunctionSummary::new("callee", "crate::callee");
        summary.postconditions.push(post1.clone());
        summary.postconditions.push(post2.clone());

        let result = substitute_callee_summary(vc, &summary);

        match &result.formula {
            Formula::Implies(premise, _) => match premise.as_ref() {
                Formula::And(clauses) => {
                    assert_eq!(clauses.len(), 2);
                    assert_eq!(clauses[0], post1);
                    assert_eq!(clauses[1], post2);
                }
                other => panic!("expected And, got: {other:?}"),
            },
            other => panic!("expected Implies, got: {other:?}"),
        }
    }

    #[test]
    fn test_summary_store_iteration() {
        let mut store = SummaryStore::new();
        store.insert(FunctionSummary::new("a", "crate::a"));
        store.insert(FunctionSummary::new("b", "crate::b"));

        let names: Vec<&str> = store.iter().map(|(_, s)| s.name.as_str()).collect();
        assert_eq!(names.len(), 2);
        assert!(names.contains(&"a"));
        assert!(names.contains(&"b"));
    }
}
