// trust-temporal/refinement.rs: Refinement checks between impl and spec machines
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, SourceSpan, VcKind, VerificationCondition};

use crate::{StateId, StateMachine, Transition};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RefinementSpec {
    pub spec_file: String,
    pub state_map: Vec<StateMapping>,
    pub action_map: Vec<ActionMapping>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StateMapping {
    pub impl_field: String,
    pub spec_var: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ActionMapping {
    pub impl_fn: String,
    pub spec_action: String,
}

pub(crate) struct RefinementChecker<'a> {
    impl_machine: &'a StateMachine,
    spec_machine: &'a StateMachine,
    spec: &'a RefinementSpec,
}

impl<'a> RefinementChecker<'a> {
    #[must_use]
    pub(crate) fn new(
        impl_machine: &'a StateMachine,
        spec_machine: &'a StateMachine,
        spec: &'a RefinementSpec,
    ) -> Self {
        Self { impl_machine, spec_machine, spec }
    }

    #[must_use]
    pub(crate) fn check(&self) -> RefinementResult {
        let mut violations = Vec::new();

        for transition in &self.impl_machine.transitions {
            let impl_state_name = self.state_name(self.impl_machine, transition.from);
            let Some(spec_action) = self.spec_action_for(transition) else {
                violations.push(RefinementViolation {
                    impl_state: transition.from,
                    impl_action: transition.event.clone(),
                    description: format!(
                        "impl action `{}` from state `{}` is unmapped in refinement spec `{}`",
                        transition.event, impl_state_name, self.spec.spec_file
                    ),
                });
                continue;
            };

            let Some(spec_from) = self.spec_state_for(transition.from) else {
                violations.push(RefinementViolation {
                    impl_state: transition.from,
                    impl_action: transition.event.clone(),
                    description: format!(
                        "impl state `{}` has no corresponding state in spec `{}` for action `{}`",
                        impl_state_name, self.spec.spec_file, transition.event
                    ),
                });
                continue;
            };

            if !has_transition(&self.spec_machine.transitions, spec_from, &spec_action) {
                let spec_state_name = self.state_name(self.spec_machine, spec_from);
                violations.push(RefinementViolation {
                    impl_state: transition.from,
                    impl_action: transition.event.clone(),
                    description: format!(
                        "impl action `{}` from state `{}` does not refine spec action `{}` from state `{}`",
                        transition.event, impl_state_name, spec_action, spec_state_name
                    ),
                });
            }
        }

        RefinementResult { violations, spec_file: self.spec.spec_file.clone() }
    }

    fn spec_action_for(&self, transition: &Transition) -> Option<String> {
        if self.spec.action_map.is_empty() {
            return Some(transition.event.clone());
        }

        self.spec
            .action_map
            .iter()
            .find(|mapping| mapping.impl_fn == transition.event)
            .map(|mapping| mapping.spec_action.clone())
    }

    fn spec_state_for(&self, impl_state_id: StateId) -> Option<StateId> {
        let impl_state = self.impl_machine.state(impl_state_id)?;

        if self.spec.state_map.is_empty() {
            return self.spec_machine.states.get(impl_state.id.0).map(|state| state.id);
        }

        self.spec
            .state_map
            .iter()
            .filter(|mapping| mapping.impl_field == impl_state.name)
            .find_map(|mapping| {
                self.spec_machine
                    .states
                    .iter()
                    .find(|state| {
                        state.name == mapping.spec_var || state.name.contains(&mapping.spec_var)
                    })
                    .map(|state| state.id)
            })
            .or_else(|| {
                self.spec_machine
                    .states
                    .iter()
                    .find(|state| state.name == impl_state.name)
                    .map(|state| state.id)
            })
    }

    fn state_name(&self, machine: &StateMachine, state_id: StateId) -> String {
        machine
            .state(state_id)
            .map(|state| state.name.clone())
            .unwrap_or_else(|| format!("state_{}", state_id.0))
    }
}

#[derive(Debug, Clone)]
pub(crate) struct RefinementResult {
    pub violations: Vec<RefinementViolation>,
    spec_file: String,
}

impl RefinementResult {
    #[must_use]
    pub(crate) fn is_ok(&self) -> bool {
        self.violations.is_empty()
    }

    #[must_use]
    pub(crate) fn into_vcs(self, function: &str, location: SourceSpan) -> Vec<VerificationCondition> {
        let Self { violations, spec_file } = self;

        violations
            .into_iter()
            .map(|violation| VerificationCondition {
                kind: VcKind::RefinementViolation {
                    spec_file: spec_file.clone(),
                    action: violation.impl_action.clone(),
                },
                function: function.to_string(),
                location: location.clone(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            })
            .collect()
    }
}

#[derive(Debug, Clone)]
pub(crate) struct RefinementViolation {
    pub impl_state: StateId,
    pub impl_action: String,
    pub description: String,
}

fn has_transition(transitions: &[Transition], from: StateId, event: &str) -> bool {
    transitions.iter().any(|transition| transition.from == from && transition.event == event)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{State, StateMachineBuilder};

    fn spec_config(spec_file: &str) -> RefinementSpec {
        RefinementSpec {
            spec_file: spec_file.to_string(),
            state_map: Vec::new(),
            action_map: Vec::new(),
        }
    }

    fn two_state_machine(idle: &str, busy: &str, event: &str) -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), idle))
            .add_state(State::new(StateId(1), busy))
            .add_transition(Transition::new(StateId(0), StateId(1), event))
            .build()
    }

    #[test]
    fn test_refinement_matching_machines_no_violations() {
        let spec_machine = two_state_machine("Idle", "Busy", "start");
        let impl_machine = two_state_machine("Idle", "Busy", "start");
        let result =
            RefinementChecker::new(&impl_machine, &spec_machine, &spec_config("bank.tla")).check();

        assert!(result.is_ok());
        assert!(result.violations.is_empty());
    }

    #[test]
    fn test_refinement_extra_impl_action_violation() {
        let spec_machine = two_state_machine("Idle", "Busy", "start");
        let impl_machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle"))
            .add_state(State::new(StateId(1), "Busy"))
            .add_transition(Transition::new(StateId(0), StateId(1), "start"))
            .add_transition(Transition::new(StateId(1), StateId(1), "panic"))
            .build();
        let spec = RefinementSpec {
            spec_file: "bank.tla".to_string(),
            state_map: Vec::new(),
            action_map: vec![ActionMapping {
                impl_fn: "start".to_string(),
                spec_action: "start".to_string(),
            }],
        };

        let result = RefinementChecker::new(&impl_machine, &spec_machine, &spec).check();

        assert_eq!(result.violations.len(), 1);
        assert_eq!(result.violations[0].impl_action, "panic");
        assert!(result.violations[0].description.contains("unmapped"));
    }

    #[test]
    fn test_refinement_missing_spec_transition_violation() {
        let spec_machine = two_state_machine("Idle", "Busy", "start");
        let impl_machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle"))
            .add_state(State::new(StateId(1), "Busy"))
            .add_state(State::new(StateId(2), "Done"))
            .add_transition(Transition::new(StateId(0), StateId(1), "start"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
            .build();

        let result =
            RefinementChecker::new(&impl_machine, &spec_machine, &spec_config("bank.tla")).check();

        assert_eq!(result.violations.len(), 1);
        assert_eq!(result.violations[0].impl_action, "finish");
        assert!(result.violations[0].description.contains("does not refine"));
    }

    #[test]
    fn test_refinement_with_action_mapping() {
        let spec_machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle"))
            .add_state(State::new(StateId(1), "Busy"))
            .add_state(State::new(StateId(2), "Done"))
            .add_transition(Transition::new(StateId(0), StateId(1), "start"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
            .build();
        let impl_machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle"))
            .add_state(State::new(StateId(1), "Busy"))
            .add_state(State::new(StateId(2), "Done"))
            .add_transition(Transition::new(StateId(0), StateId(1), "begin"))
            .add_transition(Transition::new(StateId(1), StateId(2), "complete"))
            .build();
        let spec = RefinementSpec {
            spec_file: "workflow.tla".to_string(),
            state_map: Vec::new(),
            action_map: vec![
                ActionMapping { impl_fn: "begin".to_string(), spec_action: "start".to_string() },
                ActionMapping {
                    impl_fn: "complete".to_string(),
                    spec_action: "finish".to_string(),
                },
            ],
        };

        let result = RefinementChecker::new(&impl_machine, &spec_machine, &spec).check();

        assert!(result.is_ok());
    }

    #[test]
    fn test_refinement_with_state_mapping() {
        let impl_machine = two_state_machine("impl_idle", "impl_busy", "tick");
        let spec_machine = StateMachineBuilder::new(StateId(5))
            .add_state(State::new(StateId(8), "SpecBusyState"))
            .add_state(State::new(StateId(5), "SpecIdleState"))
            .add_transition(Transition::new(StateId(5), StateId(8), "tick"))
            .build();
        let spec = RefinementSpec {
            spec_file: "mapped.tla".to_string(),
            state_map: vec![
                StateMapping { impl_field: "impl_idle".to_string(), spec_var: "Idle".to_string() },
                StateMapping { impl_field: "impl_busy".to_string(), spec_var: "Busy".to_string() },
            ],
            action_map: Vec::new(),
        };

        let result = RefinementChecker::new(&impl_machine, &spec_machine, &spec).check();

        assert!(result.is_ok());
    }

    #[test]
    fn test_refinement_empty_machines_ok() {
        let spec_machine = StateMachine::new(StateId(0));
        let impl_machine = StateMachine::new(StateId(0));

        let result =
            RefinementChecker::new(&impl_machine, &spec_machine, &spec_config("empty.tla")).check();

        assert!(result.is_ok());
    }

    #[test]
    fn test_refinement_result_into_vcs() {
        let result = RefinementResult {
            violations: vec![RefinementViolation {
                impl_state: StateId(1),
                impl_action: "withdraw".to_string(),
                description: "withdraw is invalid".to_string(),
            }],
            spec_file: "bank.tla".to_string(),
        };

        let vcs = result.into_vcs("bank::step", SourceSpan::default());

        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::RefinementViolation { spec_file, action }
                if spec_file == "bank.tla" && action == "withdraw"
        ));
    }

    #[test]
    fn test_refinement_bank_example() {
        let spec_machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Open"))
            .add_transition(Transition::new(StateId(0), StateId(0), "deposit"))
            .add_transition(Transition::new(StateId(0), StateId(0), "withdraw"))
            .build();
        let impl_machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Open"))
            .add_state(State::new(StateId(1), "Overdrawn"))
            .add_transition(Transition::new(StateId(0), StateId(0), "deposit"))
            .add_transition(Transition::new(StateId(0), StateId(0), "withdraw"))
            .add_transition(Transition::new(StateId(0), StateId(1), "overdraft"))
            .build();
        let spec = RefinementSpec {
            spec_file: "bank.tla".to_string(),
            state_map: Vec::new(),
            action_map: vec![
                ActionMapping {
                    impl_fn: "deposit".to_string(),
                    spec_action: "deposit".to_string(),
                },
                ActionMapping {
                    impl_fn: "withdraw".to_string(),
                    spec_action: "withdraw".to_string(),
                },
            ],
        };

        let result = RefinementChecker::new(&impl_machine, &spec_machine, &spec).check();

        assert_eq!(result.violations.len(), 1);
        assert_eq!(result.violations[0].impl_action, "overdraft");
    }
}
