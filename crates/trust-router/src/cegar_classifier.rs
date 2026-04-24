// trust-router: CEGAR VC classifier
//
// Analyzes formula complexity and VC characteristics to decide whether
// CEGAR (predicate abstraction + refinement) is more appropriate than
// direct SMT solving. Loops, recursion, and deeply nested formulas
// benefit from CEGAR's abstraction-refinement loop.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::{Formula, VcKind, VerificationCondition};

/// Score threshold above which a VC should be dispatched to CEGAR.
const CEGAR_THRESHOLD: u32 = 30;

/// Classification result for a VC's suitability for CEGAR.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CegarClassification {
    /// Numeric score: higher = more suitable for CEGAR.
    pub score: u32,
    /// Whether this VC should be dispatched to CEGAR.
    pub should_use_cegar: bool,
    /// Reasons contributing to the score.
    pub reasons: Vec<CegarReason>,
}

/// A reason contributing to CEGAR suitability score.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CegarReason {
    /// Formula contains loop-like patterns (back-edges, repeated variables).
    LoopPattern { score_contribution: u32 },
    /// Formula references recursive function calls.
    RecursionPattern { score_contribution: u32 },
    /// Formula has deep nesting (many nested quantifiers/connectives).
    DeepNesting { depth: u32, score_contribution: u32 },
    /// VC kind is known to benefit from CEGAR (e.g., termination).
    BeneficialKind { kind_desc: String, score_contribution: u32 },
    /// Formula has many variables (high-dimensional state space).
    HighDimensionality { var_count: u32, score_contribution: u32 },
    /// Formula uses quantifiers (forall/exists patterns).
    Quantified { score_contribution: u32 },
}

/// Classify a VC for CEGAR dispatch suitability.
#[must_use]
pub fn classify(vc: &VerificationCondition) -> CegarClassification {
    classify_with_threshold(vc, CEGAR_THRESHOLD)
}

/// Classify a VC with a custom threshold.
#[must_use]
pub fn classify_with_threshold(vc: &VerificationCondition, threshold: u32) -> CegarClassification {
    let mut reasons = Vec::new();
    let mut score: u32 = 0;

    // 1. Check VcKind for CEGAR-beneficial patterns.
    if let Some(reason) = kind_score(&vc.kind) {
        score += reason.contribution();
        reasons.push(reason);
    }

    // 2. Analyze formula nesting depth.
    let depth = formula_depth(&vc.formula);
    if depth >= 4 {
        let contribution = (depth - 3) * 5;
        score += contribution;
        reasons.push(CegarReason::DeepNesting { depth, score_contribution: contribution });
    }

    // 3. Count distinct variables for dimensionality.
    let var_count = count_variables(&vc.formula);
    if var_count >= 6 {
        let contribution = (var_count - 5) * 3;
        score += contribution;
        reasons
            .push(CegarReason::HighDimensionality { var_count, score_contribution: contribution });
    }

    // 4. Detect loop patterns in the formula.
    if has_loop_pattern(&vc.formula) {
        let contribution = 20;
        score += contribution;
        reasons.push(CegarReason::LoopPattern { score_contribution: contribution });
    }

    // 5. Detect recursion patterns (function name referencing itself in formula).
    if has_recursion_pattern(&vc.formula, vc.function.as_str()) {
        let contribution = 25;
        score += contribution;
        reasons.push(CegarReason::RecursionPattern { score_contribution: contribution });
    }

    // 6. Detect quantifier-like patterns (Implies with universally-quantified feel).
    if has_quantifier_pattern(&vc.formula) {
        let contribution = 15;
        score += contribution;
        reasons.push(CegarReason::Quantified { score_contribution: contribution });
    }

    CegarClassification { score, should_use_cegar: score >= threshold, reasons }
}

impl CegarReason {
    /// The score contribution from this reason.
    #[must_use]
    pub fn contribution(&self) -> u32 {
        match self {
            CegarReason::LoopPattern { score_contribution }
            | CegarReason::RecursionPattern { score_contribution }
            | CegarReason::DeepNesting { score_contribution, .. }
            | CegarReason::BeneficialKind { score_contribution, .. }
            | CegarReason::HighDimensionality { score_contribution, .. }
            | CegarReason::Quantified { score_contribution } => *score_contribution,
        }
    }
}

/// Score contribution from the VC kind itself.
fn kind_score(kind: &VcKind) -> Option<CegarReason> {
    match kind {
        // tRust #194: NonTermination VCs must NOT be routed to CEGAR/IC3/PDR.
        // PDR and k-induction prove safety (AG !bad), not termination
        // (something eventually happens). Termination requires:
        //   - lean5 (inductive proofs with decreasing measures)
        //   - sunder (deductive verification with ranking functions)
        //   - tla2 (liveness checking via Buchi automata)
        VcKind::NonTermination { .. } => None,
        // Loop invariant assertions benefit from refinement.
        VcKind::Assertion { message }
            if message.contains("loop") || message.contains("invariant") =>
        {
            Some(CegarReason::BeneficialKind {
                kind_desc: "loop/invariant assertion".to_string(),
                score_contribution: 25,
            })
        }
        // Postconditions with complex structure benefit from CEGAR.
        VcKind::Postcondition => Some(CegarReason::BeneficialKind {
            kind_desc: "postcondition".to_string(),
            score_contribution: 10,
        }),
        // Preconditions with callee context.
        VcKind::Precondition { .. } => Some(CegarReason::BeneficialKind {
            kind_desc: "precondition".to_string(),
            score_contribution: 8,
        }),
        // Simple safety checks -- SMT is usually better.
        VcKind::DivisionByZero
        | VcKind::RemainderByZero
        | VcKind::IndexOutOfBounds
        | VcKind::SliceBoundsCheck
        | VcKind::Unreachable => None,
        // Arithmetic overflow -- sometimes benefits from CEGAR.
        VcKind::ArithmeticOverflow { .. }
        | VcKind::ShiftOverflow { .. }
        | VcKind::CastOverflow { .. }
        | VcKind::NegationOverflow { .. } => Some(CegarReason::BeneficialKind {
            kind_desc: "overflow".to_string(),
            score_contribution: 5,
        }),
        // Domain-level properties -- CEGAR can help but temporal is better.
        _ => None,
    }
}

/// Compute the nesting depth of a formula.
#[must_use]
pub fn formula_depth(formula: &Formula) -> u32 {
    match formula {
        Formula::Bool(_) | Formula::Int(_) | Formula::BitVec { .. } | Formula::Var(..) => 0,

        Formula::Not(inner) | Formula::Neg(inner) => 1 + formula_depth(inner),

        Formula::And(children) | Formula::Or(children) => {
            children.iter().map(formula_depth).max().unwrap_or(0) + 1
        }

        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => 1 + formula_depth(a).max(formula_depth(b)),

        // Bitvector ops (3-arg with width).
        Formula::BvAdd(a, b, _)
        | Formula::BvSub(a, b, _)
        | Formula::BvMul(a, b, _)
        | Formula::BvUDiv(a, b, _)
        | Formula::BvSDiv(a, b, _)
        | Formula::BvURem(a, b, _)
        | Formula::BvSRem(a, b, _)
        | Formula::BvAnd(a, b, _)
        | Formula::BvOr(a, b, _)
        | Formula::BvXor(a, b, _) => 1 + formula_depth(a).max(formula_depth(b)),

        // Catch any new variants conservatively.
        _ => 0,
    }
}

/// Count distinct variables in a formula.
#[must_use]
pub fn count_variables(formula: &Formula) -> u32 {
    let mut vars = FxHashSet::default();
    collect_variables(formula, &mut vars);
    vars.len() as u32
}

pub(crate) fn collect_variables(formula: &Formula, vars: &mut FxHashSet<String>) {
    match formula {
        Formula::Var(name, _) => {
            vars.insert(name.clone());
        }
        Formula::Bool(_) | Formula::Int(_) | Formula::BitVec { .. } => {}

        Formula::Not(inner) | Formula::Neg(inner) => {
            collect_variables(inner, vars);
        }

        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                collect_variables(child, vars);
            }
        }

        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => {
            collect_variables(a, vars);
            collect_variables(b, vars);
        }

        Formula::BvAdd(a, b, _)
        | Formula::BvSub(a, b, _)
        | Formula::BvMul(a, b, _)
        | Formula::BvUDiv(a, b, _)
        | Formula::BvSDiv(a, b, _)
        | Formula::BvURem(a, b, _)
        | Formula::BvSRem(a, b, _)
        | Formula::BvAnd(a, b, _)
        | Formula::BvOr(a, b, _)
        | Formula::BvXor(a, b, _) => {
            collect_variables(a, vars);
            collect_variables(b, vars);
        }

        _ => {}
    }
}

/// Detect loop-like patterns in a formula.
///
/// Heuristic: a formula contains loop patterns if it references primed variables
/// (e.g., `x'`, `_next_x`) or contains And/Or with repeated variable references.
fn has_loop_pattern(formula: &Formula) -> bool {
    let mut vars = FxHashSet::default();
    collect_variables(formula, &mut vars);

    // Primed variable convention: x' or x_next or _next_x.
    let has_primed =
        vars.iter().any(|v| v.ends_with('\'') || v.contains("_next_") || v.starts_with("next_"));

    if has_primed {
        return true;
    }

    // Check for back-edge pattern: variables appearing in both LHS and RHS of
    // nested implications or equalities, suggesting loop invariant structure.
    matches!(formula, Formula::And(children) if children.len() >= 3 && {
        let depth = formula_depth(formula);
        depth >= 3 && vars.len() >= 4
    })
}

/// Detect recursion patterns: the formula references the function name.
fn has_recursion_pattern(formula: &Formula, function_name: &str) -> bool {
    if function_name.is_empty() {
        return false;
    }
    let mut vars = FxHashSet::default();
    collect_variables(formula, &mut vars);
    vars.iter().any(|v| v.contains(function_name))
}

/// Detect quantifier-like patterns (deeply nested Implies chains).
fn has_quantifier_pattern(formula: &Formula) -> bool {
    match formula {
        Formula::Implies(_, consequent) => matches!(consequent.as_ref(), Formula::Implies(..)),
        Formula::And(children) => children.iter().any(|c| matches!(c, Formula::Implies(..))),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{BinOp, Sort, SourceSpan, Ty};

    use super::*;

    fn make_vc(kind: VcKind, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    #[test]
    fn test_classify_simple_division_by_zero_low_score() {
        let vc = make_vc(VcKind::DivisionByZero, Formula::Bool(false));
        let result = classify(&vc);
        assert!(!result.should_use_cegar);
        assert_eq!(result.score, 0);
    }

    #[test]
    fn test_classify_non_termination_excluded_from_cegar() {
        // tRust #194: NonTermination VCs must NOT be routed to CEGAR/IC3/PDR.
        // PDR proves safety (AG !bad), not termination.
        let vc = make_vc(
            VcKind::NonTermination { context: "loop".to_string(), measure: "n".to_string() },
            Formula::Bool(false),
        );
        let result = classify(&vc);
        assert_eq!(result.score, 0, "NonTermination should contribute 0 to CEGAR score");
        assert!(!result.should_use_cegar, "NonTermination must not trigger CEGAR");
        assert!(
            !result.reasons.iter().any(|r| matches!(r, CegarReason::BeneficialKind { .. })),
            "NonTermination should not produce a BeneficialKind reason"
        );
    }

    #[test]
    fn test_classify_deep_nesting_adds_score() {
        // Build a deeply nested formula: ((x + y) > (a + b)) AND ((c > d) AND (e > f))
        let x = Formula::Var("x".into(), Sort::Int);
        let y = Formula::Var("y".into(), Sort::Int);
        let a = Formula::Var("a".into(), Sort::Int);
        let b = Formula::Var("b".into(), Sort::Int);
        let c = Formula::Var("c".into(), Sort::Int);
        let d = Formula::Var("d".into(), Sort::Int);
        let e = Formula::Var("e".into(), Sort::Int);
        let f = Formula::Var("f".into(), Sort::Int);

        let sum_xy = Formula::Add(Box::new(x), Box::new(y));
        let sum_ab = Formula::Add(Box::new(a), Box::new(b));
        let cmp1 = Formula::Gt(Box::new(sum_xy), Box::new(sum_ab));
        let cmp2 = Formula::Gt(Box::new(c), Box::new(d));
        let cmp3 = Formula::Gt(Box::new(e), Box::new(f));
        let inner = Formula::And(vec![cmp2, cmp3]);
        let formula = Formula::And(vec![cmp1, inner]);

        let vc = make_vc(VcKind::Postcondition, formula);
        let result = classify(&vc);
        // Should have deep nesting + high dimensionality + postcondition kind
        assert!(result.score > 0);
        assert!(result.reasons.iter().any(|r| matches!(r, CegarReason::HighDimensionality { .. })));
    }

    #[test]
    fn test_classify_many_variables_adds_dimensionality() {
        let vars: Vec<Formula> =
            (0..10).map(|i| Formula::Var(format!("v{i}"), Sort::Int)).collect();
        let formula = Formula::And(
            vars.windows(2)
                .map(|w| Formula::Lt(Box::new(w[0].clone()), Box::new(w[1].clone())))
                .collect(),
        );
        let vc = make_vc(VcKind::DivisionByZero, formula);
        let result = classify(&vc);
        let dim_reason =
            result.reasons.iter().find(|r| matches!(r, CegarReason::HighDimensionality { .. }));
        assert!(dim_reason.is_some());
    }

    #[test]
    fn test_classify_loop_pattern_detected() {
        // Formula with primed variables (loop pattern).
        let x = Formula::Var("x".into(), Sort::Int);
        let x_next = Formula::Var("x_next_iter".into(), Sort::Int);
        let formula = Formula::Lt(Box::new(x), Box::new(x_next));

        let vc = make_vc(VcKind::DivisionByZero, formula);
        let result = classify(&vc);
        assert!(result.reasons.iter().any(|r| matches!(r, CegarReason::LoopPattern { .. })));
    }

    #[test]
    fn test_classify_recursion_pattern_detected() {
        // Formula referencing function name as variable.
        let f = Formula::Var("test_fn_result".into(), Sort::Int);
        let formula = Formula::Gt(Box::new(f), Box::new(Formula::Int(0)));

        let vc = make_vc(VcKind::Postcondition, formula);
        let result = classify(&vc);
        assert!(result.reasons.iter().any(|r| matches!(r, CegarReason::RecursionPattern { .. })));
    }

    #[test]
    fn test_classify_quantifier_pattern() {
        let x = Formula::Var("x".into(), Sort::Int);
        let y = Formula::Var("y".into(), Sort::Int);
        let _inner = Formula::Implies(
            Box::new(Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(0)))),
            Box::new(Formula::Gt(Box::new(y.clone()), Box::new(Formula::Int(0)))),
        );
        let formula = Formula::Implies(
            Box::new(Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(0)))),
            Box::new(Formula::Implies(
                Box::new(Formula::Gt(Box::new(y.clone()), Box::new(Formula::Int(0)))),
                Box::new(Formula::Lt(Box::new(x), Box::new(y))),
            )),
        );
        let vc = make_vc(VcKind::Postcondition, formula);
        let result = classify(&vc);
        assert!(result.reasons.iter().any(|r| matches!(r, CegarReason::Quantified { .. })));
    }

    #[test]
    fn test_classify_custom_threshold() {
        let vc = make_vc(VcKind::Postcondition, Formula::Bool(false));
        // Postcondition gives 10 points. Threshold 5 should trigger CEGAR.
        let result = classify_with_threshold(&vc, 5);
        assert!(result.should_use_cegar);
        // Threshold 50 should not trigger CEGAR.
        let result = classify_with_threshold(&vc, 50);
        assert!(!result.should_use_cegar);
    }

    #[test]
    fn test_formula_depth_literals() {
        assert_eq!(formula_depth(&Formula::Bool(true)), 0);
        assert_eq!(formula_depth(&Formula::Int(42)), 0);
        assert_eq!(formula_depth(&Formula::Var("x".into(), Sort::Int)), 0);
    }

    #[test]
    fn test_formula_depth_nested() {
        let inner =
            Formula::Add(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(1)));
        assert_eq!(formula_depth(&inner), 1);

        let outer = Formula::Gt(Box::new(inner), Box::new(Formula::Int(10)));
        assert_eq!(formula_depth(&outer), 2);

        let deeper = Formula::Not(Box::new(outer));
        assert_eq!(formula_depth(&deeper), 3);
    }

    #[test]
    fn test_count_variables_empty() {
        assert_eq!(count_variables(&Formula::Bool(true)), 0);
        assert_eq!(count_variables(&Formula::Int(0)), 0);
    }

    #[test]
    fn test_count_variables_distinct() {
        let formula = Formula::And(vec![
            Formula::Var("x".into(), Sort::Int),
            Formula::Var("y".into(), Sort::Int),
            Formula::Var("x".into(), Sort::Int), // duplicate
        ]);
        assert_eq!(count_variables(&formula), 2);
    }

    #[test]
    fn test_kind_score_overflow_small() {
        let kind =
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) };
        let reason = kind_score(&kind);
        assert!(reason.is_some());
        assert_eq!(reason.unwrap().contribution(), 5);
    }

    #[test]
    fn test_kind_score_assertion_with_loop() {
        let kind = VcKind::Assertion { message: "loop invariant violated".to_string() };
        let reason = kind_score(&kind);
        assert!(reason.is_some());
        assert_eq!(reason.unwrap().contribution(), 25);
    }

    #[test]
    fn test_classify_combined_high_score() {
        // tRust #194: Build a VC that hits multiple CEGAR indicators.
        // Use a loop-invariant assertion (not NonTermination) since NonTermination
        // is excluded from CEGAR scoring.
        let vars: Vec<Formula> = (0..8).map(|i| Formula::Var(format!("v{i}"), Sort::Int)).collect();
        let primed = Formula::Var("v0_next_step".into(), Sort::Int);
        let inner = Formula::Implies(
            Box::new(Formula::Gt(Box::new(vars[0].clone()), Box::new(Formula::Int(0)))),
            Box::new(Formula::Implies(
                Box::new(Formula::Lt(Box::new(vars[1].clone()), Box::new(vars[2].clone()))),
                Box::new(Formula::Eq(Box::new(primed), Box::new(vars[3].clone()))),
            )),
        );
        let formula = Formula::And(vec![
            inner,
            Formula::Lt(Box::new(vars[4].clone()), Box::new(vars[5].clone())),
            Formula::Gt(Box::new(vars[6].clone()), Box::new(vars[7].clone())),
        ]);

        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "loop invariant: counter decreases".to_string() },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        };

        let result = classify(&vc);
        // loop-invariant assertion (25) + loop pattern (20) + quantifier (15) + dimensionality + depth
        assert!(result.should_use_cegar, "combined indicators should trigger CEGAR");
        assert!(result.score >= 50, "score should be high, got {}", result.score);
    }
}
