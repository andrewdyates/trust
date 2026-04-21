// trust-vcgen/liveness.rs: Liveness and fairness VC generation (#49)
//
// Generates verification conditions for liveness properties (something good
// eventually happens) and fairness constraints (enabled actions eventually
// execute). These VCs are dispatched to tla2 via trust-router for tableau
// construction and SCC-based model checking.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

/// tRust: A state machine model for liveness checking (#49).
///
/// Represents the states and transitions of a concurrent system extracted
/// from async Rust code. Liveness properties are checked against this model.
#[derive(Debug, Clone)]
pub struct StateMachineModel {
    /// Name of the model (e.g., function or module name).
    pub name: String,
    /// State variables with their types.
    pub state_vars: Vec<StateVariable>,
    /// Named actions (transitions).
    pub actions: Vec<Action>,
    /// Fairness constraints on actions.
    pub fairness: Vec<FairnessConstraint>,
    /// Liveness properties to verify.
    pub liveness_properties: Vec<LivenessProperty>,
}

/// A state variable in the model.
#[derive(Debug, Clone)]
pub struct StateVariable {
    /// Variable name.
    pub name: String,
    /// Variable type description (for diagnostics).
    pub ty: String,
}

/// A named action (state transition) in the model.
#[derive(Debug, Clone)]
pub struct Action {
    /// Action name.
    pub name: String,
    /// Enabling condition (when the action can fire).
    pub enabled: String,
    /// Effect description (what the action does).
    pub effect: String,
}

/// Generate liveness VCs from a state machine model.
///
/// For each liveness property, generates a VC with kind `VcKind::Liveness`.
/// For each fairness constraint, generates a VC with kind `VcKind::Fairness`.
/// The formula encodes the negation of the property so that SAT = violation.
#[must_use]
pub fn generate_liveness_vcs(
    model: &StateMachineModel,
    span: &SourceSpan,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // Generate a VC for each liveness property.
    for property in &model.liveness_properties {
        let formula = liveness_to_formula(property);
        vcs.push(VerificationCondition {
            kind: VcKind::Liveness { property: property.clone() },
            function: model.name.clone(),
            location: span.clone(),
            formula,
            contract_metadata: None,
        });
    }

    // Generate a VC for each fairness constraint.
    for constraint in &model.fairness {
        let formula = fairness_to_formula(constraint, &model.actions);
        vcs.push(VerificationCondition {
            kind: VcKind::Fairness { constraint: constraint.clone() },
            function: model.name.clone(),
            location: span.clone(),
            formula,
            contract_metadata: None,
        });
    }

    vcs
}

/// Convert a liveness property into an SMT formula.
///
/// The formula represents the *negation* of the liveness property, following
/// the VC convention: SAT = violation found, UNSAT = property holds.
///
/// For temporal properties, this is encoded structurally rather than as a
/// flat SMT formula, since the actual checking is done by tla2's tableau
/// construction. The formula serves as a witness structure.
fn liveness_to_formula(property: &LivenessProperty) -> Formula {
    // Build a structural encoding of the temporal property.
    // The predicate becomes a variable, and the temporal operator is encoded
    // as the negation of the desired property.
    let pred_var = Formula::Var(
        format!("liveness_{}", property.name),
        Sort::Bool,
    );

    match property.operator {
        TemporalOperator::Eventually => {
            // <>P negated: [](NOT P) — P never holds.
            // Encode as: exists a cycle where P is always false.
            Formula::Not(Box::new(pred_var))
        }
        TemporalOperator::Always => {
            // []P negated: <>(NOT P) — P eventually fails.
            // Encode as: exists a reachable state where P is false.
            Formula::Not(Box::new(pred_var))
        }
        TemporalOperator::AlwaysEventually => {
            // []<>P negated: <>[](NOT P) — eventually P stops recurring.
            // Encode as: exists a cycle reachable where P never holds again.
            Formula::Not(Box::new(pred_var))
        }
        TemporalOperator::LeadsTo => {
            // (P ~> Q) negated: <>(P AND [](NOT Q)) — P holds but Q never follows.
            let q_var = Formula::Var(
                format!(
                    "liveness_{}_consequent",
                    property.name
                ),
                Sort::Bool,
            );
            Formula::And(vec![pred_var, Formula::Not(Box::new(q_var))])
        }
        _ => Formula::Bool(true),
    }
}

/// Convert a fairness constraint into an SMT formula.
///
/// The formula encodes the *negation* of the fairness condition:
/// - WF(A): NOT([]<>enabled(A) => []<>A) = []<>enabled(A) AND <>[](NOT A)
/// - SF(A): NOT([]<>enabled(A) => []<>A) = similar but with stronger enabling
fn fairness_to_formula(constraint: &FairnessConstraint, actions: &[Action]) -> Formula {
    let action_name = constraint.action();

    // Find the enabling condition for this action.
    let enabled_var = Formula::Var(format!("enabled_{action_name}"), Sort::Bool);
    let action_var = Formula::Var(format!("taken_{action_name}"), Sort::Bool);

    // Check if any model action matches this fairness constraint.
    let _has_matching_action = actions.iter().any(|a| a.name == action_name);

    // Negation of fairness: enabled infinitely often but never taken.
    // This is the witness condition for a fairness violation.
    Formula::And(vec![enabled_var, Formula::Not(Box::new(action_var))])
}

/// Build a starvation freedom model for a set of concurrent entities.
///
/// Starvation freedom means: for all entities t, []<>Progress(t).
/// This is the standard progress property for concurrent systems.
#[must_use]
pub fn starvation_freedom_model(
    name: &str,
    entities: &[&str],
    scheduler_action: &str,
    state_vars: &[&str],
) -> StateMachineModel {
    let vars: Vec<String> = state_vars.iter().map(|s| (*s).to_string()).collect();

    let mut liveness_properties = Vec::new();
    let mut fairness = Vec::new();

    // Each entity gets an always-eventually progress property.
    for entity in entities {
        liveness_properties.push(LivenessProperty {
            name: format!("progress_{entity}"),
            operator: TemporalOperator::AlwaysEventually,
            predicate: format!("Progress({entity})"),
            consequent: None,
            fairness: vec![FairnessConstraint::Weak {
                action: scheduler_action.to_string(),
                vars: vars.clone(),
            }],
        });
    }

    // The scheduler action is weakly fair by default (tokio-style).
    fairness.push(FairnessConstraint::Weak {
        action: scheduler_action.to_string(),
        vars: vars.clone(),
    });

    StateMachineModel {
        name: name.to_string(),
        state_vars: state_vars
            .iter()
            .map(|v| StateVariable { name: v.to_string(), ty: "state".to_string() })
            .collect(),
        actions: vec![Action {
            name: scheduler_action.to_string(),
            enabled: "TRUE".to_string(),
            effect: format!("schedules one of: {}", entities.join(", ")),
        }],
        fairness,
        liveness_properties,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_eventually_property(name: &str, pred: &str) -> LivenessProperty {
        LivenessProperty {
            name: name.to_string(),
            operator: TemporalOperator::Eventually,
            predicate: pred.to_string(),
            consequent: None,
            fairness: vec![],
        }
    }

    fn make_leads_to_property(name: &str, p: &str, q: &str) -> LivenessProperty {
        LivenessProperty {
            name: name.to_string(),
            operator: TemporalOperator::LeadsTo,
            predicate: p.to_string(),
            consequent: Some(q.to_string()),
            fairness: vec![],
        }
    }

    fn make_simple_model(props: Vec<LivenessProperty>) -> StateMachineModel {
        StateMachineModel {
            name: "test_model".to_string(),
            state_vars: vec![StateVariable {
                name: "state".to_string(),
                ty: "u32".to_string(),
            }],
            actions: vec![Action {
                name: "step".to_string(),
                enabled: "TRUE".to_string(),
                effect: "advance state".to_string(),
            }],
            fairness: vec![],
            liveness_properties: props,
        }
    }

    #[test]
    fn test_generate_liveness_vc_eventually() {
        let prop = make_eventually_property("termination", "done");
        let model = make_simple_model(vec![prop]);
        let span = SourceSpan::default();

        let vcs = generate_liveness_vcs(&model, &span);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(&vcs[0].kind, VcKind::Liveness { property } if property.name == "termination"));
        assert_eq!(vcs[0].kind.proof_level(), ProofLevel::L2Domain);
        assert_eq!(vcs[0].function, "test_model");
    }

    #[test]
    fn test_generate_liveness_vc_leads_to() {
        let prop = make_leads_to_property("req_resp", "request", "response");
        let model = make_simple_model(vec![prop]);
        let span = SourceSpan::default();

        let vcs = generate_liveness_vcs(&model, &span);
        assert_eq!(vcs.len(), 1);

        match &vcs[0].kind {
            VcKind::Liveness { property } => {
                assert_eq!(property.operator, TemporalOperator::LeadsTo);
                assert_eq!(property.consequent.as_deref(), Some("response"));
            }
            other => panic!("expected Liveness, got {other:?}"),
        }

        // The formula should be an And (P AND NOT Q) for leads-to negation.
        assert!(matches!(&vcs[0].formula, Formula::And(_)));
    }

    #[test]
    fn test_generate_fairness_vcs() {
        let model = StateMachineModel {
            name: "scheduler".to_string(),
            state_vars: vec![StateVariable { name: "queue".into(), ty: "Vec<Task>".into() }],
            actions: vec![Action {
                name: "dispatch".into(),
                enabled: "queue.len() > 0".into(),
                effect: "run next task".into(),
            }],
            fairness: vec![
                FairnessConstraint::Weak {
                    action: "dispatch".into(),
                    vars: vec!["queue".into()],
                },
                FairnessConstraint::Strong {
                    action: "priority_run".into(),
                    vars: vec!["priority_queue".into()],
                },
            ],
            liveness_properties: vec![],
        };
        let span = SourceSpan::default();

        let vcs = generate_liveness_vcs(&model, &span);
        assert_eq!(vcs.len(), 2);
        assert!(matches!(&vcs[0].kind, VcKind::Fairness { constraint }
            if matches!(constraint, FairnessConstraint::Weak { action, .. } if action == "dispatch")));
        assert!(matches!(&vcs[1].kind, VcKind::Fairness { constraint }
            if constraint.is_strong()));
    }

    #[test]
    fn test_generate_liveness_and_fairness_combined() {
        let model = StateMachineModel {
            name: "async_worker".to_string(),
            state_vars: vec![StateVariable { name: "tasks".into(), ty: "Vec".into() }],
            actions: vec![Action {
                name: "schedule".into(),
                enabled: "TRUE".into(),
                effect: "pick next task".into(),
            }],
            fairness: vec![FairnessConstraint::Weak {
                action: "schedule".into(),
                vars: vec!["tasks".into()],
            }],
            liveness_properties: vec![LivenessProperty {
                name: "progress".into(),
                operator: TemporalOperator::AlwaysEventually,
                predicate: "task_complete".into(),
                consequent: None,
                fairness: vec![FairnessConstraint::Weak {
                    action: "schedule".into(),
                    vars: vec!["tasks".into()],
                }],
            }],
        };
        let span = SourceSpan::default();

        let vcs = generate_liveness_vcs(&model, &span);
        // 1 liveness + 1 fairness = 2 VCs
        assert_eq!(vcs.len(), 2);
        assert!(matches!(&vcs[0].kind, VcKind::Liveness { .. }));
        assert!(matches!(&vcs[1].kind, VcKind::Fairness { .. }));
    }

    #[test]
    fn test_starvation_freedom_model() {
        let model = starvation_freedom_model(
            "tokio_scheduler",
            &["task_a", "task_b", "task_c"],
            "schedule",
            &["ready_queue", "running"],
        );

        assert_eq!(model.name, "tokio_scheduler");
        assert_eq!(model.state_vars.len(), 2);
        assert_eq!(model.actions.len(), 1);
        assert_eq!(model.fairness.len(), 1);
        assert_eq!(model.liveness_properties.len(), 3);

        // Each entity gets a progress property.
        for (i, entity) in ["task_a", "task_b", "task_c"].iter().enumerate() {
            let prop = &model.liveness_properties[i];
            assert_eq!(prop.name, format!("progress_{entity}"));
            assert_eq!(prop.operator, TemporalOperator::AlwaysEventually);
            assert!(prop.predicate.contains(entity));
            assert_eq!(prop.fairness.len(), 1);
        }

        // Generate VCs from the model.
        let span = SourceSpan::default();
        let vcs = generate_liveness_vcs(&model, &span);
        // 3 liveness + 1 fairness = 4 VCs
        assert_eq!(vcs.len(), 4);
        assert_eq!(
            vcs.iter().filter(|vc| matches!(&vc.kind, VcKind::Liveness { .. })).count(),
            3
        );
        assert_eq!(
            vcs.iter().filter(|vc| matches!(&vc.kind, VcKind::Fairness { .. })).count(),
            1
        );
    }

    #[test]
    fn test_empty_model_produces_no_vcs() {
        let model = StateMachineModel {
            name: "empty".to_string(),
            state_vars: vec![],
            actions: vec![],
            fairness: vec![],
            liveness_properties: vec![],
        };
        let vcs = generate_liveness_vcs(&model, &SourceSpan::default());
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_liveness_formula_eventually_is_negated() {
        let prop = make_eventually_property("done_check", "done");
        let formula = liveness_to_formula(&prop);
        // Eventually negated: NOT(pred_var)
        assert!(matches!(formula, Formula::Not(_)));
    }

    #[test]
    fn test_liveness_formula_leads_to_structure() {
        let prop = make_leads_to_property("p_to_q", "P", "Q");
        let formula = liveness_to_formula(&prop);
        // LeadsTo negated: P AND NOT Q
        match formula {
            Formula::And(parts) => {
                assert_eq!(parts.len(), 2);
                assert!(matches!(&parts[0], Formula::Var(name, Sort::Bool) if name == "liveness_p_to_q"));
                assert!(matches!(&parts[1], Formula::Not(_)));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_fairness_formula_structure() {
        let constraint = FairnessConstraint::Weak {
            action: "step".into(),
            vars: vec!["x".into()],
        };
        let actions = vec![Action {
            name: "step".into(),
            enabled: "TRUE".into(),
            effect: "increment".into(),
        }];
        let formula = fairness_to_formula(&constraint, &actions);
        // Fairness negated: enabled AND NOT taken
        match formula {
            Formula::And(parts) => {
                assert_eq!(parts.len(), 2);
                assert!(matches!(&parts[0], Formula::Var(name, Sort::Bool) if name == "enabled_step"));
                assert!(matches!(&parts[1], Formula::Not(inner)
                    if matches!(inner.as_ref(), Formula::Var(name, Sort::Bool) if name == "taken_step")));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_all_liveness_vcs_are_l2_domain() {
        let model = starvation_freedom_model(
            "test",
            &["a", "b"],
            "sched",
            &["q"],
        );
        let vcs = generate_liveness_vcs(&model, &SourceSpan::default());
        for vc in &vcs {
            assert_eq!(
                vc.kind.proof_level(),
                ProofLevel::L2Domain,
                "all liveness/fairness VCs must be L2Domain"
            );
        }
    }
}
