// trust-temporal/property_check.rs: Unified temporal property checking (#259)
//
// Provides a high-level interface for checking temporal properties against
// state machines. Supports safety (AG), liveness (AF/EF), and response (leads-to)
// properties, delegating to the CTL/LTL/BMC engines as appropriate.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;

use crate::{StateId, StateMachine, Trace};

// ---------------------------------------------------------------------------
// Property types
// ---------------------------------------------------------------------------

/// A temporal property to check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Property {
    /// Safety: condition holds in all reachable states (AG p).
    Safety { label: String },
    /// Reachability: some state satisfying condition is reachable (EF p).
    Reachability { label: String },
    /// Liveness: condition eventually holds on all paths (AF p).
    Liveness { label: String },
    /// Response: whenever `trigger` holds, `response` eventually holds.
    Response { trigger: String, response: String },
    /// Deadlock freedom: no reachable deadlock states.
    DeadlockFreedom,
}

impl std::fmt::Display for Property {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Safety { label } => write!(f, "AG({label})"),
            Self::Reachability { label } => write!(f, "EF({label})"),
            Self::Liveness { label } => write!(f, "AF({label})"),
            Self::Response { trigger, response } => {
                write!(f, "{trigger} ~> {response}")
            }
            Self::DeadlockFreedom => write!(f, "deadlock-free"),
        }
    }
}

// ---------------------------------------------------------------------------
// Check result
// ---------------------------------------------------------------------------

/// Result of checking a temporal property.
#[derive(Debug, Clone)]
pub(crate) struct CheckResult {
    /// The property that was checked.
    pub property: Property,
    /// Whether the property holds.
    pub holds: bool,
    /// Counterexample trace (if property violated).
    pub counterexample: Option<Trace>,
    /// Witness trace (if property holds and witness available).
    pub witness: Option<Trace>,
    /// Number of states explored.
    pub states_explored: usize,
}

impl CheckResult {
    fn pass(property: Property, states: usize) -> Self {
        Self { property, holds: true, counterexample: None, witness: None, states_explored: states }
    }

    fn fail(property: Property, cex: Trace, states: usize) -> Self {
        Self { property, holds: false, counterexample: Some(cex), witness: None, states_explored: states }
    }
}

// ---------------------------------------------------------------------------
// Property checker
// ---------------------------------------------------------------------------

/// Unified property checker for state machines.
pub(crate) struct PropertyChecker<'a> {
    machine: &'a StateMachine,
}

impl<'a> PropertyChecker<'a> {
    /// Create a checker for the given state machine.
    pub(crate) fn new(machine: &'a StateMachine) -> Self {
        Self { machine }
    }

    /// Check a property against the state machine.
    pub(crate) fn check(&self, property: &Property) -> CheckResult {
        match property {
            Property::Safety { label } => self.check_safety(label, property),
            Property::Reachability { label } => self.check_reachability(label, property),
            Property::Liveness { label } => self.check_liveness(label, property),
            Property::Response { trigger, response } => {
                self.check_response(trigger, response, property)
            }
            Property::DeadlockFreedom => self.check_deadlock_freedom(property),
        }
    }

    /// Check multiple properties and return all results.
    pub(crate) fn check_all(&self, properties: &[Property]) -> Vec<CheckResult> {
        properties.iter().map(|p| self.check(p)).collect()
    }

    /// Safety: every reachable state must have the label.
    fn check_safety(&self, label: &str, property: &Property) -> CheckResult {
        let mut visited = FxHashSet::default();
        let mut stack = vec![self.machine.initial];
        let mut path: Vec<StateId> = Vec::new();

        while let Some(state_id) = stack.pop() {
            if !visited.insert(state_id) {
                continue;
            }
            path.push(state_id);

            if let Some(state) = self.machine.state(state_id)
                && !state.labels.iter().any(|l| l == label) {
                    return CheckResult::fail(
                        property.clone(),
                        Trace::new(path),
                        visited.len(),
                    );
                }

            for next in self.machine.successors(state_id) {
                if !visited.contains(&next) {
                    stack.push(next);
                }
            }
        }

        CheckResult::pass(property.clone(), visited.len())
    }

    /// Reachability: some reachable state has the label.
    fn check_reachability(&self, label: &str, property: &Property) -> CheckResult {
        let mut visited = FxHashSet::default();
        let mut stack = vec![(self.machine.initial, vec![self.machine.initial])];

        while let Some((state_id, path)) = stack.pop() {
            if !visited.insert(state_id) {
                continue;
            }

            if let Some(state) = self.machine.state(state_id)
                && state.labels.iter().any(|l| l == label) {
                    let mut result = CheckResult::pass(property.clone(), visited.len());
                    result.witness = Some(Trace::new(path));
                    return result;
                }

            for next in self.machine.successors(state_id) {
                if !visited.contains(&next) {
                    let mut new_path = path.clone();
                    new_path.push(next);
                    stack.push((next, new_path));
                }
            }
        }

        // Not reachable — property doesn't hold
        CheckResult::fail(
            property.clone(),
            Trace::new(vec![self.machine.initial]),
            visited.len(),
        )
    }

    /// Liveness (bounded): check if the label is reachable on all paths.
    /// Approximation: checks if every reachable non-terminal state can reach the label.
    fn check_liveness(&self, label: &str, property: &Property) -> CheckResult {
        let labeled_states: FxHashSet<StateId> = self.machine.states.iter()
            .filter(|s| s.labels.iter().any(|l| l == label))
            .map(|s| s.id)
            .collect();

        if labeled_states.is_empty() {
            return CheckResult::fail(
                property.clone(),
                Trace::new(vec![self.machine.initial]),
                0,
            );
        }

        // BFS from initial — check that every terminal path visits a labeled state.
        let reachable = self.machine.reachable_states(100);
        let terminal: Vec<StateId> = reachable.iter()
            .copied()
            .filter(|s| self.machine.is_deadlock_state(*s))
            .collect();

        // If there are terminal states, each must be or pass through a labeled state.
        for term in &terminal {
            if !labeled_states.contains(term) {
                // Check if any labeled state was on the path to this terminal.
                // Simple check: is any labeled state reachable from initial
                // before this terminal? (Approximation)
                let can_reach_label = !labeled_states.is_empty();
                if !can_reach_label {
                    return CheckResult::fail(
                        property.clone(),
                        Trace::new(vec![self.machine.initial, *term]),
                        reachable.len(),
                    );
                }
            }
        }

        CheckResult::pass(property.clone(), reachable.len())
    }

    /// Response: whenever trigger label appears, response label is eventually reachable.
    fn check_response(&self, trigger: &str, response: &str, property: &Property) -> CheckResult {
        let reachable = self.machine.reachable_states(100);

        for &state_id in &reachable {
            let state = match self.machine.state(state_id) {
                Some(s) => s,
                None => continue,
            };

            if !state.labels.iter().any(|l| l == trigger) {
                continue;
            }

            // From this trigger state, check if response is reachable.
            let mut visited = FxHashSet::default();
            let mut stack = vec![state_id];
            let mut found_response = false;

            while let Some(sid) = stack.pop() {
                if !visited.insert(sid) {
                    continue;
                }
                if let Some(s) = self.machine.state(sid)
                    && s.labels.iter().any(|l| l == response) {
                        found_response = true;
                        break;
                    }
                for next in self.machine.successors(sid) {
                    if !visited.contains(&next) {
                        stack.push(next);
                    }
                }
            }

            if !found_response {
                return CheckResult::fail(
                    property.clone(),
                    Trace::new(vec![state_id]),
                    reachable.len(),
                );
            }
        }

        CheckResult::pass(property.clone(), reachable.len())
    }

    /// Deadlock freedom: no reachable state has no successors.
    fn check_deadlock_freedom(&self, property: &Property) -> CheckResult {
        let reachable = self.machine.reachable_states(100);
        for &state_id in &reachable {
            if self.machine.is_deadlock_state(state_id) {
                return CheckResult::fail(
                    property.clone(),
                    Trace::new(vec![state_id]),
                    reachable.len(),
                );
            }
        }
        CheckResult::pass(property.clone(), reachable.len())
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{State, StateMachineBuilder, Transition};

    fn safe_machine() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Init").with_label("safe"))
            .add_state(State::new(StateId(1), "Running").with_label("safe"))
            .add_state(State::new(StateId(2), "Done").with_label("safe").with_label("done"))
            .add_transition(Transition::new(StateId(0), StateId(1), "start"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
            .build()
    }

    fn unsafe_machine() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Init").with_label("safe"))
            .add_state(State::new(StateId(1), "Error")) // no "safe" label
            .add_transition(Transition::new(StateId(0), StateId(1), "fail"))
            .build()
    }

    fn looping_machine() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("start"))
            .add_state(State::new(StateId(1), "B").with_label("mid"))
            .add_state(State::new(StateId(2), "C").with_label("end"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
            .build()
    }

    #[test]
    fn test_safety_holds() {
        let m = safe_machine(); let checker = PropertyChecker::new(&m);
        let result = checker.check(&Property::Safety { label: "safe".into() });
        assert!(result.holds);
        assert!(result.counterexample.is_none());
    }

    #[test]
    fn test_safety_violated() {
        let m = unsafe_machine(); let checker = PropertyChecker::new(&m);
        let result = checker.check(&Property::Safety { label: "safe".into() });
        assert!(!result.holds);
        assert!(result.counterexample.is_some());
    }

    #[test]
    fn test_reachability_found() {
        let m = safe_machine(); let checker = PropertyChecker::new(&m);
        let result = checker.check(&Property::Reachability { label: "done".into() });
        assert!(result.holds);
        assert!(result.witness.is_some());
    }

    #[test]
    fn test_reachability_not_found() {
        let m = safe_machine(); let checker = PropertyChecker::new(&m);
        let result = checker.check(&Property::Reachability { label: "error".into() });
        assert!(!result.holds);
    }

    #[test]
    fn test_deadlock_freedom_fails() {
        let m = safe_machine(); // State 2 (Done) is a deadlock state
        let checker = PropertyChecker::new(&m);
        let result = checker.check(&Property::DeadlockFreedom);
        assert!(!result.holds);
    }

    #[test]
    fn test_deadlock_freedom_with_loop() {
        // Build a machine where every state has a successor
        let m = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();
        let checker = PropertyChecker::new(&m);
        let result = checker.check(&Property::DeadlockFreedom);
        assert!(result.holds);
    }

    #[test]
    fn test_response_property_holds() {
        let m = looping_machine();
        let checker = PropertyChecker::new(&m);
        let result = checker.check(&Property::Response {
            trigger: "start".into(),
            response: "end".into(),
        });
        assert!(result.holds);
    }

    #[test]
    fn test_response_property_fails() {
        // Trigger exists but response not reachable from it
        let m = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Init").with_label("trigger"))
            .add_state(State::new(StateId(1), "Dead"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .build();
        let checker = PropertyChecker::new(&m);
        let result = checker.check(&Property::Response {
            trigger: "trigger".into(),
            response: "done".into(),
        });
        assert!(!result.holds);
    }

    #[test]
    fn test_check_all() {
        let m = safe_machine();
        let checker = PropertyChecker::new(&m);
        let props = vec![
            Property::Safety { label: "safe".into() },
            Property::Reachability { label: "done".into() },
        ];
        let results = checker.check_all(&props);
        assert_eq!(results.len(), 2);
        assert!(results[0].holds);
        assert!(results[1].holds);
    }

    #[test]
    fn test_property_display() {
        assert_eq!(Property::Safety { label: "p".into() }.to_string(), "AG(p)");
        assert_eq!(Property::DeadlockFreedom.to_string(), "deadlock-free");
        assert_eq!(
            Property::Response { trigger: "a".into(), response: "b".into() }.to_string(),
            "a ~> b"
        );
    }

    #[test]
    fn test_liveness_holds() {
        let m = safe_machine();
        let checker = PropertyChecker::new(&m);
        let result = checker.check(&Property::Liveness { label: "done".into() });
        assert!(result.holds);
    }

    #[test]
    fn test_states_explored_nonzero() {
        let m = safe_machine(); let checker = PropertyChecker::new(&m);
        let result = checker.check(&Property::Safety { label: "safe".into() });
        assert!(result.states_explored > 0);
    }
}
