// trust-vcgen/vc_splitter.rs: Proof obligation splitter (#265)
//
// Decomposes complex VCs into independent sub-obligations for parallel solving.
// Uses formula structure analysis to find independent conjuncts that can be
// checked separately.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;

use trust_types::{Formula, VerificationCondition, VerificationResult};

// ---------------------------------------------------------------------------
// Split strategy
// ---------------------------------------------------------------------------

/// Strategy for splitting a VC.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(clippy::enum_variant_names)]
pub enum SplitStrategy {
    /// Split top-level conjunction into independent VCs.
    ConjunctionSplit,
    /// Split by case analysis (disjunction in hypothesis).
    CaseSplit,
    /// No split applicable.
    NoSplit,
}

// ---------------------------------------------------------------------------
// VC splitter
// ---------------------------------------------------------------------------

/// Splits complex VCs into independent sub-obligations.
pub struct VcSplitter;

impl VcSplitter {
    /// Determine the best split strategy for a VC.
    #[must_use]
    pub fn analyze(vc: &VerificationCondition) -> SplitStrategy {
        match &vc.formula {
            Formula::And(conjuncts) if conjuncts.len() > 1 => {
                if Self::are_independent(conjuncts) {
                    SplitStrategy::ConjunctionSplit
                } else {
                    SplitStrategy::NoSplit
                }
            }
            Formula::Implies(_, body) => {
                if let Formula::And(conjuncts) = body.as_ref() {
                    if conjuncts.len() > 1 && Self::are_independent(conjuncts) {
                        SplitStrategy::ConjunctionSplit
                    } else {
                        SplitStrategy::NoSplit
                    }
                } else {
                    SplitStrategy::NoSplit
                }
            }
            _ => SplitStrategy::NoSplit,
        }
    }

    /// Split a VC into sub-obligations.
    #[must_use]
    pub fn split(vc: &VerificationCondition) -> Vec<VerificationCondition> {
        match &vc.formula {
            Formula::And(conjuncts) if conjuncts.len() > 1 => {
                conjuncts.iter().map(|f| {
                    VerificationCondition {
                        kind: vc.kind.clone(),
                        function: vc.function.clone(),
                        location: vc.location.clone(),
                        formula: f.clone(),
                        contract_metadata: vc.contract_metadata,
                    }
                }).collect()
            }
            Formula::Implies(hyp, body) => {
                if let Formula::And(conjuncts) = body.as_ref()
                    && conjuncts.len() > 1
                {
                    return conjuncts.iter().map(|f| {
                        VerificationCondition {
                            kind: vc.kind.clone(),
                            function: vc.function.clone(),
                            location: vc.location.clone(),
                            formula: Formula::Implies(hyp.clone(), Box::new(f.clone())),
                            contract_metadata: vc.contract_metadata,
                        }
                    }).collect();
                }
                vec![vc.clone()]
            }
            _ => vec![vc.clone()],
        }
    }

    /// Check if formulas are variable-independent (no shared free variables).
    fn are_independent(formulas: &[Formula]) -> bool {
        let var_sets: Vec<FxHashSet<String>> = formulas.iter()
            .map(Self::free_variables)
            .collect();

        for i in 0..var_sets.len() {
            for j in (i + 1)..var_sets.len() {
                if !var_sets[i].is_disjoint(&var_sets[j]) {
                    return false;
                }
            }
        }
        true
    }

    /// Collect free variables from a formula.
    fn free_variables(formula: &Formula) -> FxHashSet<String> {
        let mut vars = FxHashSet::default();
        Self::collect_vars(formula, &mut vars);
        vars
    }

    fn collect_vars(formula: &Formula, vars: &mut FxHashSet<String>) {
        match formula {
            Formula::Var(name, _) => { vars.insert(name.clone()); }
            Formula::Not(f) => Self::collect_vars(f, vars),
            Formula::And(fs) => { for f in fs { Self::collect_vars(f, vars); } }
            Formula::Or(fs) => { for f in fs { Self::collect_vars(f, vars); } }
            Formula::Implies(a, b) => {
                Self::collect_vars(a, vars);
                Self::collect_vars(b, vars);
            }
            _ => {
                for child in formula.children() {
                    Self::collect_vars(child, vars);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Merge results
// ---------------------------------------------------------------------------

/// Merge strategy for combining sub-VC results.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MergeStrategy {
    /// All sub-VCs must pass for the parent to pass.
    AllMustPass,
    /// Any sub-VC failing means the parent fails.
    FailFast,
}

/// Merge sub-VC results back into a unified result.
pub fn merge_results(
    results: &[VerificationResult],
    _strategy: &MergeStrategy,
) -> MergedResult {
    let mut proved = 0;
    let mut failed = 0;
    let mut unknown = 0;

    for r in results {
        match r {
            VerificationResult::Proved { .. } => proved += 1,
            VerificationResult::Failed { .. } => failed += 1,
            _ => unknown += 1,
        }
    }

    let overall = if failed > 0 {
        MergedOutcome::Failed
    } else if unknown > 0 {
        MergedOutcome::Partial { proved, unknown }
    } else {
        MergedOutcome::AllProved
    };

    MergedResult {
        sub_count: results.len(),
        proved,
        failed,
        unknown,
        outcome: overall,
    }
}

/// Result of merging sub-VC results.
#[derive(Debug, Clone)]
pub struct MergedResult {
    pub sub_count: usize,
    pub proved: usize,
    pub failed: usize,
    pub unknown: usize,
    pub outcome: MergedOutcome,
}

/// Overall outcome from merging.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MergedOutcome {
    AllProved,
    Failed,
    Partial { proved: usize, unknown: usize },
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{ProofStrength, Sort, SourceSpan, VcKind};

    fn make_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "f".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    #[test]
    fn test_split_conjunction() {
        let f = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
        ]);
        let vc = make_vc(f);
        let split = VcSplitter::split(&vc);
        assert_eq!(split.len(), 2);
    }

    #[test]
    fn test_no_split_single() {
        let f = Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let vc = make_vc(f);
        let split = VcSplitter::split(&vc);
        assert_eq!(split.len(), 1);
    }

    #[test]
    fn test_split_implies_conjunction() {
        let hyp = Formula::Bool(true);
        let body = Formula::And(vec![
            Formula::Var("a".into(), Sort::Bool),
            Formula::Var("b".into(), Sort::Bool),
        ]);
        let f = Formula::Implies(Box::new(hyp), Box::new(body));
        let vc = make_vc(f);
        let split = VcSplitter::split(&vc);
        assert_eq!(split.len(), 2);
        // Each sub-VC should be an implication
        for sub in &split {
            assert!(matches!(sub.formula, Formula::Implies(_, _)));
        }
    }

    #[test]
    fn test_analyze_strategy() {
        let f = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
        ]);
        let vc = make_vc(f);
        assert_eq!(VcSplitter::analyze(&vc), SplitStrategy::ConjunctionSplit);
    }

    #[test]
    fn test_analyze_no_split() {
        let f = Formula::Bool(true);
        let vc = make_vc(f);
        assert_eq!(VcSplitter::analyze(&vc), SplitStrategy::NoSplit);
    }

    #[test]
    fn test_free_variables() {
        let f = Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        );
        let vars = VcSplitter::free_variables(&f);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains("x"));
        assert!(vars.contains("y"));
    }

    #[test]
    fn test_merge_all_proved() {
        let results = vec![
            VerificationResult::Proved { solver: "z4".into(), time_ms: 1, strength: ProofStrength::smt_unsat(), proof_certificate: None, solver_warnings: None },
            VerificationResult::Proved { solver: "z4".into(), time_ms: 2, strength: ProofStrength::smt_unsat(), proof_certificate: None, solver_warnings: None },
        ];
        let merged = merge_results(&results, &MergeStrategy::AllMustPass);
        assert_eq!(merged.outcome, MergedOutcome::AllProved);
        assert_eq!(merged.proved, 2);
    }

    #[test]
    fn test_merge_with_failure() {
        let results = vec![
            VerificationResult::Proved { solver: "z4".into(), time_ms: 1, strength: ProofStrength::smt_unsat(), proof_certificate: None, solver_warnings: None },
            VerificationResult::Failed { solver: "z4".into(), time_ms: 1, counterexample: None },
        ];
        let merged = merge_results(&results, &MergeStrategy::AllMustPass);
        assert_eq!(merged.outcome, MergedOutcome::Failed);
        assert_eq!(merged.failed, 1);
    }

    #[test]
    fn test_merge_partial() {
        let results = vec![
            VerificationResult::Proved { solver: "z4".into(), time_ms: 1, strength: ProofStrength::smt_unsat(), proof_certificate: None, solver_warnings: None },
            VerificationResult::Unknown { solver: "z4".into(), time_ms: 1, reason: "complex".into() },
        ];
        let merged = merge_results(&results, &MergeStrategy::AllMustPass);
        assert!(matches!(merged.outcome, MergedOutcome::Partial { .. }));
    }

    #[test]
    fn test_merge_empty() {
        let merged = merge_results(&[], &MergeStrategy::AllMustPass);
        assert_eq!(merged.outcome, MergedOutcome::AllProved);
        assert_eq!(merged.sub_count, 0);
    }

    #[test]
    fn test_independent_formulas() {
        let x = Formula::Var("x".into(), Sort::Int);
        let y = Formula::Var("y".into(), Sort::Int);
        assert!(VcSplitter::are_independent(&[
            Formula::Gt(Box::new(x), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(y), Box::new(Formula::Int(10))),
        ]));
    }

    #[test]
    fn test_dependent_formulas() {
        let x1 = Formula::Var("x".into(), Sort::Int);
        let x2 = Formula::Var("x".into(), Sort::Int);
        assert!(!VcSplitter::are_independent(&[
            Formula::Gt(Box::new(x1), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(x2), Box::new(Formula::Int(10))),
        ]));
    }

    #[test]
    fn test_split_preserves_metadata() {
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "safe_div".into(),
            location: SourceSpan::default(),
            formula: f,
            contract_metadata: None,
        };
        let split = VcSplitter::split(&vc);
        for sub in &split {
            assert_eq!(sub.function, "safe_div");
            assert!(matches!(sub.kind, VcKind::DivisionByZero));
        }
    }
}
