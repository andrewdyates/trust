// trust-vcgen/loop_invariant_gen.rs: Loop invariant VC generation (#310)
//
// Generates verification conditions for loop invariants following the
// classical Hoare-logic approach:
//   - Initiation: invariant holds on loop entry
//   - Consecution: invariant preserved by loop body
//   - Sufficiency: invariant implies postcondition at loop exit
//   - Termination: ranking function decreases on each iteration
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{BlockId, Formula, Sort, SourceSpan, VerificationCondition, VcKind};

/// A loop invariant: a formula that holds at a specific loop header.
#[derive(Debug, Clone, PartialEq)]
pub struct LoopInvariant {
    /// The invariant formula (must hold at the loop header on every iteration).
    pub formula: Formula,
    /// The loop header block where this invariant applies.
    pub loop_header: BlockId,
    /// Source location of the invariant annotation (if any).
    pub span: SourceSpan,
}

/// The four kinds of verification conditions for loop invariants.
#[derive(Debug, Clone, PartialEq)]
pub enum InvariantVC {
    /// The invariant holds when the loop is first entered.
    /// VC: precondition /\ init_assignments => invariant
    Initiation {
        /// The invariant to check.
        invariant: Formula,
        /// Precondition (context before loop entry).
        precondition: Formula,
        /// The loop header block.
        loop_header: BlockId,
    },
    /// The invariant is preserved by one iteration of the loop body.
    /// VC: invariant /\ loop_guard /\ body_effect => invariant'
    Consecution {
        /// The invariant to check.
        invariant: Formula,
        /// The loop guard condition (condition under which the loop body executes).
        loop_guard: Formula,
        /// The loop body's effect as a transition relation.
        body_effect: Formula,
        /// The loop header block.
        loop_header: BlockId,
    },
    /// The invariant, combined with loop exit, implies the postcondition.
    /// VC: invariant /\ !loop_guard => postcondition
    Sufficiency {
        /// The invariant assumption.
        invariant: Formula,
        /// The negation of the loop guard (loop exit condition).
        exit_condition: Formula,
        /// The postcondition to establish.
        postcondition: Formula,
        /// The loop header block.
        loop_header: BlockId,
    },
    /// The ranking function decreases on each iteration (termination).
    /// VC: invariant /\ loop_guard => ranking(pre) > ranking(post) /\ ranking(post) >= 0
    Termination {
        /// The invariant assumption.
        invariant: Formula,
        /// The loop guard condition.
        loop_guard: Formula,
        /// The ranking function applied to pre-state.
        ranking: RankingFunction,
        /// The loop header block.
        loop_header: BlockId,
    },
}

/// A ranking function for termination checking.
///
/// The ranking function maps program states to a well-founded domain
/// (non-negative integers). It must strictly decrease on each loop iteration.
#[derive(Debug, Clone, PartialEq)]
pub struct RankingFunction {
    /// The ranking expression in the pre-state (before loop body).
    pub pre_value: Formula,
    /// The ranking expression in the post-state (after loop body).
    pub post_value: Formula,
    /// Human-readable description of the ranking function.
    pub description: String,
}

/// Generate all invariant VCs for a loop given its invariant and context.
///
/// Produces up to 4 VCs: initiation, consecution, sufficiency, and termination.
/// Termination is only generated when a ranking function is provided.
#[must_use]
pub fn generate_invariant_vcs(
    function_name: &str,
    invariant: &LoopInvariant,
    precondition: &Formula,
    loop_guard: &Formula,
    body_effect: &Formula,
    postcondition: &Formula,
    ranking: Option<&RankingFunction>,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // 1. Initiation: precondition => invariant
    vcs.push(check_initiation(
        function_name,
        &invariant.formula,
        precondition,
        invariant.loop_header,
        &invariant.span,
    ));

    // 2. Consecution: invariant /\ guard /\ body => invariant'
    vcs.push(check_consecution(
        function_name,
        &invariant.formula,
        loop_guard,
        body_effect,
        invariant.loop_header,
        &invariant.span,
    ));

    // 3. Sufficiency: invariant /\ !guard => postcondition
    vcs.push(check_sufficiency(
        function_name,
        &invariant.formula,
        loop_guard,
        postcondition,
        invariant.loop_header,
        &invariant.span,
    ));

    // 4. Termination (optional)
    if let Some(rank) = ranking {
        vcs.push(check_termination(
            function_name,
            &invariant.formula,
            loop_guard,
            rank,
            invariant.loop_header,
            &invariant.span,
        ));
    }

    vcs
}

/// Generate the initiation VC: the invariant holds on loop entry.
///
/// The VC checks that `precondition => invariant` is valid.
/// We negate for the solver: `precondition /\ !invariant` should be UNSAT.
#[must_use]
pub fn check_initiation(
    function_name: &str,
    invariant: &Formula,
    precondition: &Formula,
    loop_header: BlockId,
    span: &SourceSpan,
) -> VerificationCondition {
    // Solver convention: formula is SAT iff violation exists.
    // Violation of initiation: precondition holds but invariant does not.
    let formula = Formula::And(vec![
        precondition.clone(),
        Formula::Not(Box::new(invariant.clone())),
    ]);

    VerificationCondition {
        kind: VcKind::Assertion {
            message: format!(
                "Loop invariant initiation at bb{}",
                loop_header.0
            ),
        },
        function: function_name.to_string(),
        location: span.clone(),
        formula,
        contract_metadata: None,
    }
}

/// Generate the consecution VC: the invariant is preserved by the loop body.
///
/// The VC checks that `invariant /\ guard /\ body_effect => invariant'` is valid.
/// We negate: `invariant /\ guard /\ body_effect /\ !invariant'` should be UNSAT.
#[must_use]
pub fn check_consecution(
    function_name: &str,
    invariant: &Formula,
    loop_guard: &Formula,
    body_effect: &Formula,
    loop_header: BlockId,
    span: &SourceSpan,
) -> VerificationCondition {
    // Violation: invariant + guard + body hold, but invariant after body does not.
    let formula = Formula::And(vec![
        invariant.clone(),
        loop_guard.clone(),
        body_effect.clone(),
        Formula::Not(Box::new(invariant.clone())),
    ]);

    VerificationCondition {
        kind: VcKind::Assertion {
            message: format!(
                "Loop invariant consecution at bb{}",
                loop_header.0
            ),
        },
        function: function_name.to_string(),
        location: span.clone(),
        formula,
        contract_metadata: None,
    }
}

/// Generate the sufficiency VC: the invariant implies the postcondition at exit.
///
/// The VC checks that `invariant /\ !guard => postcondition` is valid.
/// We negate: `invariant /\ !guard /\ !postcondition` should be UNSAT.
#[must_use]
pub fn check_sufficiency(
    function_name: &str,
    invariant: &Formula,
    loop_guard: &Formula,
    postcondition: &Formula,
    loop_header: BlockId,
    span: &SourceSpan,
) -> VerificationCondition {
    // Violation: invariant holds, loop exits, but postcondition fails.
    let formula = Formula::And(vec![
        invariant.clone(),
        Formula::Not(Box::new(loop_guard.clone())),
        Formula::Not(Box::new(postcondition.clone())),
    ]);

    VerificationCondition {
        kind: VcKind::Assertion {
            message: format!(
                "Loop invariant sufficiency at bb{}",
                loop_header.0
            ),
        },
        function: function_name.to_string(),
        location: span.clone(),
        formula,
        contract_metadata: None,
    }
}

/// Generate the termination VC using a ranking function.
///
/// Checks that under the invariant and guard, the ranking function
/// strictly decreases and remains non-negative.
#[must_use]
pub(crate) fn check_termination(
    function_name: &str,
    invariant: &Formula,
    loop_guard: &Formula,
    ranking: &RankingFunction,
    loop_header: BlockId,
    span: &SourceSpan,
) -> VerificationCondition {
    // The ranking function must:
    //   1. Decrease strictly: pre_value > post_value
    //   2. Remain bounded: post_value >= 0
    //
    // Violation: invariant /\ guard /\ !(pre > post /\ post >= 0)
    // Equivalently: invariant /\ guard /\ (pre <= post \/ post < 0)
    let decrease = Formula::Gt(
        Box::new(ranking.pre_value.clone()),
        Box::new(ranking.post_value.clone()),
    );
    let bounded = Formula::Ge(
        Box::new(ranking.post_value.clone()),
        Box::new(Formula::Int(0)),
    );
    let termination_condition = Formula::And(vec![decrease, bounded]);

    let formula = Formula::And(vec![
        invariant.clone(),
        loop_guard.clone(),
        Formula::Not(Box::new(termination_condition)),
    ]);

    VerificationCondition {
        kind: VcKind::NonTermination {
            context: format!("loop at bb{}", loop_header.0),
            measure: ranking.description.clone(),
        },
        function: function_name.to_string(),
        location: span.clone(),
        formula,
        contract_metadata: None,
    }
}

/// Count the number of invariant VCs by kind.
#[must_use]
pub fn classify_invariant_vc(vc: &VerificationCondition) -> Option<&'static str> {
    match &vc.kind {
        VcKind::Assertion { message } if message.contains("initiation") => {
            Some("initiation")
        }
        VcKind::Assertion { message } if message.contains("consecution") => {
            Some("consecution")
        }
        VcKind::Assertion { message } if message.contains("sufficiency") => {
            Some("sufficiency")
        }
        VcKind::NonTermination { context, .. } if context.starts_with("loop") => {
            Some("termination")
        }
        _ => None,
    }
}

/// Build a simple ranking function from a variable that decreases toward zero.
///
/// Convenience helper for the common case where a loop counter `var` starts
/// at `bound` and decreases by `step` each iteration.
#[must_use]
pub fn ranking_from_countdown(
    var_name: &str,
    var_post_name: &str,
) -> RankingFunction {
    RankingFunction {
        pre_value: Formula::Var(var_name.to_string(), Sort::Int),
        post_value: Formula::Var(var_post_name.to_string(), Sort::Int),
        description: format!("{var_name} decreases toward 0"),
    }
}

/// Build a ranking function from the difference `bound - var` for ascending loops.
///
/// For a loop `while var < bound`, the ranking function is `bound - var`,
/// which decreases each iteration as `var` increases.
#[must_use]
pub fn ranking_from_bound_diff(
    var_name: &str,
    var_post_name: &str,
    bound_name: &str,
) -> RankingFunction {
    RankingFunction {
        pre_value: Formula::Sub(
            Box::new(Formula::Var(bound_name.to_string(), Sort::Int)),
            Box::new(Formula::Var(var_name.to_string(), Sort::Int)),
        ),
        post_value: Formula::Sub(
            Box::new(Formula::Var(bound_name.to_string(), Sort::Int)),
            Box::new(Formula::Var(var_post_name.to_string(), Sort::Int)),
        ),
        description: format!("{bound_name} - {var_name}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_invariant() -> LoopInvariant {
        LoopInvariant {
            formula: Formula::And(vec![
                Formula::Ge(
                    Box::new(Formula::Var("i".to_string(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Le(
                    Box::new(Formula::Var("i".to_string(), Sort::Int)),
                    Box::new(Formula::Var("n".to_string(), Sort::Int)),
                ),
            ]),
            loop_header: BlockId(1),
            span: SourceSpan::default(),
        }
    }

    fn sample_guard() -> Formula {
        Formula::Lt(
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
            Box::new(Formula::Var("n".to_string(), Sort::Int)),
        )
    }

    fn sample_precondition() -> Formula {
        Formula::Ge(
            Box::new(Formula::Var("n".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )
    }

    fn sample_body_effect() -> Formula {
        // i' = i + 1 encoded as: i_post == i + 1
        Formula::Eq(
            Box::new(Formula::Var("i_post".to_string(), Sort::Int)),
            Box::new(Formula::Add(
                Box::new(Formula::Var("i".to_string(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
        )
    }

    fn sample_postcondition() -> Formula {
        Formula::Eq(
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
            Box::new(Formula::Var("n".to_string(), Sort::Int)),
        )
    }

    fn sample_ranking() -> RankingFunction {
        ranking_from_bound_diff("i", "i_post", "n")
    }

    #[test]
    fn test_generate_invariant_vcs_without_ranking_produces_3() {
        let inv = sample_invariant();
        let vcs = generate_invariant_vcs(
            "test_fn",
            &inv,
            &sample_precondition(),
            &sample_guard(),
            &sample_body_effect(),
            &sample_postcondition(),
            None,
        );
        assert_eq!(vcs.len(), 3, "without ranking: initiation + consecution + sufficiency");
    }

    #[test]
    fn test_generate_invariant_vcs_with_ranking_produces_4() {
        let inv = sample_invariant();
        let rank = sample_ranking();
        let vcs = generate_invariant_vcs(
            "test_fn",
            &inv,
            &sample_precondition(),
            &sample_guard(),
            &sample_body_effect(),
            &sample_postcondition(),
            Some(&rank),
        );
        assert_eq!(vcs.len(), 4, "with ranking: initiation + consecution + sufficiency + termination");
    }

    #[test]
    fn test_initiation_vc_structure() {
        let vc = check_initiation(
            "f",
            &Formula::Var("inv".to_string(), Sort::Bool),
            &Formula::Bool(true),
            BlockId(1),
            &SourceSpan::default(),
        );
        assert_eq!(vc.function, "f");
        match &vc.formula {
            Formula::And(parts) => {
                assert_eq!(parts.len(), 2);
                assert!(matches!(&parts[0], Formula::Bool(true)));
                assert!(matches!(&parts[1], Formula::Not(_)));
            }
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_consecution_vc_structure() {
        let inv = Formula::Var("inv".to_string(), Sort::Bool);
        let guard = Formula::Var("guard".to_string(), Sort::Bool);
        let body = Formula::Var("body".to_string(), Sort::Bool);
        let vc = check_consecution("f", &inv, &guard, &body, BlockId(2), &SourceSpan::default());

        match &vc.formula {
            Formula::And(parts) => {
                assert_eq!(parts.len(), 4, "consecution: inv, guard, body, !inv");
                assert!(matches!(&parts[3], Formula::Not(_)));
            }
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_sufficiency_vc_structure() {
        let inv = Formula::Var("inv".to_string(), Sort::Bool);
        let guard = Formula::Var("guard".to_string(), Sort::Bool);
        let post = Formula::Var("post".to_string(), Sort::Bool);
        let vc = check_sufficiency("f", &inv, &guard, &post, BlockId(3), &SourceSpan::default());

        match &vc.formula {
            Formula::And(parts) => {
                assert_eq!(parts.len(), 3, "sufficiency: inv, !guard, !post");
                // Second element should be Not(guard)
                assert!(matches!(&parts[1], Formula::Not(g) if matches!(g.as_ref(), Formula::Var(n, _) if n == "guard")));
                // Third element should be Not(post)
                assert!(matches!(&parts[2], Formula::Not(p) if matches!(p.as_ref(), Formula::Var(n, _) if n == "post")));
            }
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_termination_vc_uses_ranking() {
        let inv = Formula::Bool(true);
        let guard = Formula::Bool(true);
        let rank = RankingFunction {
            pre_value: Formula::Var("r_pre".to_string(), Sort::Int),
            post_value: Formula::Var("r_post".to_string(), Sort::Int),
            description: "test rank".to_string(),
        };
        let vc = check_termination("f", &inv, &guard, &rank, BlockId(1), &SourceSpan::default());

        assert!(matches!(&vc.kind, VcKind::NonTermination { context, measure }
            if context.starts_with("loop at bb") && measure == "test rank"
        ));
        // Formula should be And([inv, guard, Not(And([Gt, Ge]))])
        match &vc.formula {
            Formula::And(parts) => {
                assert_eq!(parts.len(), 3);
                assert!(matches!(&parts[2], Formula::Not(_)));
            }
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_classify_invariant_vc_initiation() {
        let vc = check_initiation(
            "f",
            &Formula::Bool(true),
            &Formula::Bool(true),
            BlockId(0),
            &SourceSpan::default(),
        );
        assert_eq!(classify_invariant_vc(&vc), Some("initiation"));
    }

    #[test]
    fn test_classify_invariant_vc_consecution() {
        let vc = check_consecution(
            "f",
            &Formula::Bool(true),
            &Formula::Bool(true),
            &Formula::Bool(true),
            BlockId(0),
            &SourceSpan::default(),
        );
        assert_eq!(classify_invariant_vc(&vc), Some("consecution"));
    }

    #[test]
    fn test_classify_invariant_vc_sufficiency() {
        let vc = check_sufficiency(
            "f",
            &Formula::Bool(true),
            &Formula::Bool(true),
            &Formula::Bool(true),
            BlockId(0),
            &SourceSpan::default(),
        );
        assert_eq!(classify_invariant_vc(&vc), Some("sufficiency"));
    }

    #[test]
    fn test_classify_invariant_vc_termination() {
        let rank = RankingFunction {
            pre_value: Formula::Var("x".to_string(), Sort::Int),
            post_value: Formula::Var("x_post".to_string(), Sort::Int),
            description: "x".to_string(),
        };
        let vc = check_termination(
            "f",
            &Formula::Bool(true),
            &Formula::Bool(true),
            &rank,
            BlockId(0),
            &SourceSpan::default(),
        );
        assert_eq!(classify_invariant_vc(&vc), Some("termination"));
    }

    #[test]
    fn test_classify_invariant_vc_unrelated() {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        assert_eq!(classify_invariant_vc(&vc), None);
    }

    #[test]
    fn test_ranking_from_countdown() {
        let rank = ranking_from_countdown("n", "n_post");
        assert!(matches!(&rank.pre_value, Formula::Var(name, Sort::Int) if name == "n"));
        assert!(matches!(&rank.post_value, Formula::Var(name, Sort::Int) if name == "n_post"));
        assert!(rank.description.contains("decreases toward 0"));
    }

    #[test]
    fn test_ranking_from_bound_diff() {
        let rank = ranking_from_bound_diff("i", "i_post", "n");
        // pre_value should be Sub(n, i)
        assert!(matches!(&rank.pre_value, Formula::Sub(_, _)));
        // post_value should be Sub(n, i_post)
        assert!(matches!(&rank.post_value, Formula::Sub(_, _)));
        assert!(rank.description.contains("n - i"));
    }

    #[test]
    fn test_loop_invariant_equality() {
        let inv1 = LoopInvariant {
            formula: Formula::Bool(true),
            loop_header: BlockId(1),
            span: SourceSpan::default(),
        };
        let inv2 = LoopInvariant {
            formula: Formula::Bool(true),
            loop_header: BlockId(1),
            span: SourceSpan::default(),
        };
        assert_eq!(inv1, inv2);
    }

    #[test]
    fn test_invariant_vc_enum_equality() {
        let vc1 = InvariantVC::Initiation {
            invariant: Formula::Bool(true),
            precondition: Formula::Bool(true),
            loop_header: BlockId(0),
        };
        let vc2 = InvariantVC::Initiation {
            invariant: Formula::Bool(true),
            precondition: Formula::Bool(true),
            loop_header: BlockId(0),
        };
        assert_eq!(vc1, vc2);
    }

    #[test]
    fn test_full_pipeline_all_vcs_reference_function() {
        let inv = sample_invariant();
        let rank = sample_ranking();
        let vcs = generate_invariant_vcs(
            "my_loop",
            &inv,
            &sample_precondition(),
            &sample_guard(),
            &sample_body_effect(),
            &sample_postcondition(),
            Some(&rank),
        );
        for vc in &vcs {
            assert_eq!(vc.function, "my_loop", "all VCs should reference the function name");
        }
    }

    #[test]
    fn test_full_pipeline_all_vcs_have_formulas() {
        let inv = sample_invariant();
        let vcs = generate_invariant_vcs(
            "f",
            &inv,
            &sample_precondition(),
            &sample_guard(),
            &sample_body_effect(),
            &sample_postcondition(),
            None,
        );
        for vc in &vcs {
            // Every VC formula should be an And (our encoding)
            assert!(
                matches!(&vc.formula, Formula::And(_)),
                "each VC formula should be an And conjunction, got: {:?}",
                vc.formula
            );
        }
    }
}
