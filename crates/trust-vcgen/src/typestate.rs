// tRust #338: Type state verification for trust-vcgen.
//
// Verifies that objects transition through valid states according to a
// type state machine. Detects invalid transitions, unreachable states,
// deadlocks, and protocol violations.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};

/// A single state in the type state machine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeState {
    /// Name of the state.
    pub name: String,
    /// Properties that hold in this state.
    pub properties: Vec<String>,
}

/// A transition between two states, triggered by a method call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StateTransition {
    /// Source state name.
    pub from: String,
    /// Target state name.
    pub to: String,
    /// Method that triggers this transition.
    pub method: String,
    /// Optional guard condition (must hold for transition to fire).
    pub guard: Option<String>,
}

/// A complete type state machine definition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeStateMachine {
    /// All states in the machine.
    pub states: Vec<TypeState>,
    /// All transitions between states.
    pub transitions: Vec<StateTransition>,
    /// The initial state name.
    pub initial_state: String,
    /// States that represent error conditions.
    pub error_states: Vec<String>,
}

/// Errors that can occur during type state verification.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum TransitionError {
    /// An invalid transition was attempted.
    #[error("invalid transition from `{from}` to `{to}`")]
    InvalidTransition {
        /// Source state.
        from: String,
        /// Target state.
        to: String,
    },
    /// A state is unreachable from the initial state.
    #[error("unreachable state: `{0}`")]
    UnreachableState(String),
    /// A deadlock was detected (states with no outgoing transitions that
    /// are not designated as terminal/error states).
    #[error("deadlock detected in states: {0:?}")]
    DeadlockDetected(Vec<String>),
    /// The initial state has not been defined or does not exist.
    #[error("missing initial state")]
    MissingInitialState,
}

/// A property that must hold in a given state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StateProperty {
    /// The state this property applies to.
    pub state_name: String,
    /// The invariant expression (as a string).
    pub invariant: String,
}

/// Builder and verifier for type state machines.
#[derive(Debug, Clone, Default)]
pub struct TypeStateVerifier {
    states: Vec<TypeState>,
    transitions: Vec<StateTransition>,
    initial_state: Option<String>,
    error_states: Vec<String>,
}

impl TypeStateVerifier {
    /// Create a new, empty verifier.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a state to the machine.
    pub fn add_state(&mut self, state: TypeState) {
        self.states.push(state);
    }

    /// Add a transition to the machine.
    pub fn add_transition(&mut self, transition: StateTransition) {
        self.transitions.push(transition);
    }

    /// Set the initial state. The state must be added separately via
    /// `add_state`.
    pub fn set_initial(&mut self, state: &str) {
        self.initial_state = Some(state.to_string());
    }

    /// Mark a state as an error/terminal state.
    pub fn add_error_state(&mut self, state: &str) {
        self.error_states.push(state.to_string());
    }

    // -- internal helpers --------------------------------------------------

    /// Collect the set of state names.
    fn state_names(&self) -> FxHashSet<&str> {
        self.states.iter().map(|s| s.name.as_str()).collect()
    }

    /// Build an adjacency list (state name -> set of reachable state names).
    fn adjacency(&self) -> FxHashMap<&str, FxHashSet<&str>> {
        let mut adj: FxHashMap<&str, FxHashSet<&str>> = FxHashMap::default();
        for t in &self.transitions {
            adj.entry(t.from.as_str()).or_default().insert(t.to.as_str());
        }
        adj
    }

    /// BFS from `start`, returning the set of reachable state names.
    fn reachable_from<'a>(&'a self, start: &'a str) -> FxHashSet<&'a str> {
        let adj = self.adjacency();
        let mut visited: FxHashSet<&str> = FxHashSet::default();
        let mut queue: VecDeque<&str> = VecDeque::new();
        visited.insert(start);
        queue.push_back(start);
        while let Some(cur) = queue.pop_front() {
            if let Some(neighbours) = adj.get(cur) {
                for &next in neighbours {
                    if visited.insert(next) {
                        queue.push_back(next);
                    }
                }
            }
        }
        visited
    }

    // -- public verification API -------------------------------------------

    /// Verify that every transition references valid states and that the
    /// initial state exists.
    pub fn verify_transitions(&self) -> Result<(), TransitionError> {
        let initial = self.initial_state.as_deref().ok_or(TransitionError::MissingInitialState)?;
        let names = self.state_names();
        if !names.contains(initial) {
            return Err(TransitionError::MissingInitialState);
        }
        for t in &self.transitions {
            if !names.contains(t.from.as_str()) || !names.contains(t.to.as_str()) {
                return Err(TransitionError::InvalidTransition {
                    from: t.from.clone(),
                    to: t.to.clone(),
                });
            }
        }
        Ok(())
    }

    /// Build a `TypeStateMachine` after verification.
    pub fn build_state_machine(&self) -> Result<TypeStateMachine, TransitionError> {
        self.verify_transitions()?;
        Ok(TypeStateMachine {
            states: self.states.clone(),
            transitions: self.transitions.clone(),
            // SAFETY: verify_transitions() above ensures initial_state is Some.
            initial_state: self
                .initial_state
                .clone()
                .unwrap_or_else(|| unreachable!("initial_state None after verify_transitions")),
            error_states: self.error_states.clone(),
        })
    }

    /// Check that a sequence of state names forms a valid protocol trace
    /// starting from the initial state.
    pub fn check_protocol(&self, trace: &[&str]) -> Result<(), TransitionError> {
        let initial = self.initial_state.as_deref().ok_or(TransitionError::MissingInitialState)?;
        if trace.is_empty() {
            return Ok(());
        }
        if trace[0] != initial {
            return Err(TransitionError::InvalidTransition {
                from: initial.to_string(),
                to: trace[0].to_string(),
            });
        }
        let adj = self.adjacency();
        for window in trace.windows(2) {
            let from = window[0];
            let to = window[1];
            let valid = adj.get(from).is_some_and(|set| set.contains(to));
            if !valid {
                return Err(TransitionError::InvalidTransition {
                    from: from.to_string(),
                    to: to.to_string(),
                });
            }
        }
        Ok(())
    }

    /// Return the list of states that are unreachable from the initial state.
    #[must_use]
    pub fn unreachable_states(&self) -> Vec<String> {
        let Some(initial) = self.initial_state.as_deref() else {
            return self.states.iter().map(|s| s.name.clone()).collect();
        };
        let reachable = self.reachable_from(initial);
        self.states
            .iter()
            .filter(|s| !reachable.contains(s.name.as_str()))
            .map(|s| s.name.clone())
            .collect()
    }

    /// Check whether state `to` is reachable from state `from`.
    #[must_use]
    pub fn can_reach(&self, from: &str, to: &str) -> bool {
        self.reachable_from(from).contains(to)
    }

    /// Return states that have no outgoing transitions and are not marked
    /// as error/terminal states. These represent potential deadlocks.
    #[must_use]
    pub fn deadlock_states(&self) -> Vec<String> {
        let names = self.state_names();
        let adj = self.adjacency();
        let error_set: FxHashSet<&str> = self.error_states.iter().map(String::as_str).collect();
        names
            .into_iter()
            .filter(|name| {
                let has_outgoing = adj.get(name).is_some_and(|s| !s.is_empty());
                !has_outgoing && !error_set.contains(name)
            })
            .map(|s| s.to_string())
            .sorted_unstable()
    }
}

/// Extension trait to sort iterators (avoids pulling in itertools).
trait SortedUnstable: Iterator {
    fn sorted_unstable(self) -> Vec<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        let mut v: Vec<_> = self.collect();
        v.sort_unstable();
        v
    }
}

impl<I: Iterator> SortedUnstable for I {}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create a simple state with no properties.
    fn state(name: &str) -> TypeState {
        TypeState { name: name.to_string(), properties: vec![] }
    }

    /// Helper: create a transition with no guard.
    fn trans(from: &str, to: &str, method: &str) -> StateTransition {
        StateTransition {
            from: from.to_string(),
            to: to.to_string(),
            method: method.to_string(),
            guard: None,
        }
    }

    /// Helper: build the classic file-handle state machine:
    /// Closed -> Open -> (Read | Write) -> Closed
    fn file_handle_verifier() -> TypeStateVerifier {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("Closed"));
        v.add_state(state("Open"));
        v.add_state(state("Reading"));
        v.add_state(state("Writing"));
        v.add_transition(trans("Closed", "Open", "open"));
        v.add_transition(trans("Open", "Reading", "read"));
        v.add_transition(trans("Open", "Writing", "write"));
        v.add_transition(trans("Reading", "Open", "done_read"));
        v.add_transition(trans("Writing", "Open", "done_write"));
        v.add_transition(trans("Open", "Closed", "close"));
        v.set_initial("Closed");
        v
    }

    #[test]
    fn test_typestate_verifier_new_is_empty() {
        let v = TypeStateVerifier::new();
        assert!(v.states.is_empty());
        assert!(v.transitions.is_empty());
        assert!(v.initial_state.is_none());
    }

    #[test]
    fn test_typestate_verify_transitions_valid() {
        let v = file_handle_verifier();
        assert!(v.verify_transitions().is_ok());
    }

    #[test]
    fn test_typestate_verify_transitions_missing_initial() {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("A"));
        assert_eq!(v.verify_transitions(), Err(TransitionError::MissingInitialState));
    }

    #[test]
    fn test_typestate_verify_transitions_invalid_state_ref() {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("A"));
        v.set_initial("A");
        v.add_transition(trans("A", "B", "go"));
        let err = v.verify_transitions().unwrap_err();
        assert!(matches!(err, TransitionError::InvalidTransition { from, to }
            if from == "A" && to == "B"));
    }

    #[test]
    fn test_typestate_build_state_machine_success() {
        let v = file_handle_verifier();
        let machine = v.build_state_machine().unwrap();
        assert_eq!(machine.initial_state, "Closed");
        assert_eq!(machine.states.len(), 4);
        assert_eq!(machine.transitions.len(), 6);
    }

    #[test]
    fn test_typestate_build_state_machine_missing_initial() {
        let v = TypeStateVerifier::new();
        assert!(v.build_state_machine().is_err());
    }

    #[test]
    fn test_typestate_check_protocol_valid_trace() {
        let v = file_handle_verifier();
        assert!(v.check_protocol(&["Closed", "Open", "Reading", "Open", "Closed"]).is_ok());
    }

    #[test]
    fn test_typestate_check_protocol_invalid_trace() {
        let v = file_handle_verifier();
        let err = v.check_protocol(&["Closed", "Reading"]).unwrap_err();
        assert!(matches!(err, TransitionError::InvalidTransition { from, to }
            if from == "Closed" && to == "Reading"));
    }

    #[test]
    fn test_typestate_check_protocol_wrong_start() {
        let v = file_handle_verifier();
        let err = v.check_protocol(&["Open", "Closed"]).unwrap_err();
        assert!(
            matches!(&err, TransitionError::InvalidTransition { from, to }
                if from == "Closed" && to == "Open"
            ) || matches!(&err, TransitionError::InvalidTransition { .. })
        );
    }

    #[test]
    fn test_typestate_check_protocol_empty_trace() {
        let v = file_handle_verifier();
        assert!(v.check_protocol(&[]).is_ok());
    }

    #[test]
    fn test_typestate_unreachable_states_none() {
        let v = file_handle_verifier();
        assert!(v.unreachable_states().is_empty());
    }

    #[test]
    fn test_typestate_unreachable_states_detected() {
        let mut v = file_handle_verifier();
        v.add_state(state("Orphan"));
        let unreachable = v.unreachable_states();
        assert_eq!(unreachable, vec!["Orphan".to_string()]);
    }

    #[test]
    fn test_typestate_can_reach_true() {
        let v = file_handle_verifier();
        assert!(v.can_reach("Closed", "Writing"));
    }

    #[test]
    fn test_typestate_can_reach_false() {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("A"));
        v.add_state(state("B"));
        v.set_initial("A");
        // No transitions from A to B.
        assert!(!v.can_reach("A", "B"));
    }

    #[test]
    fn test_typestate_can_reach_self() {
        let v = file_handle_verifier();
        assert!(v.can_reach("Closed", "Closed"));
    }

    #[test]
    fn test_typestate_deadlock_states_detected() {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("Init"));
        v.add_state(state("Running"));
        v.add_state(state("Stuck"));
        v.add_transition(trans("Init", "Running", "start"));
        v.add_transition(trans("Running", "Stuck", "fail"));
        v.set_initial("Init");
        // "Stuck" has no outgoing transitions and is not an error state.
        let deadlocks = v.deadlock_states();
        assert!(deadlocks.contains(&"Stuck".to_string()));
    }

    #[test]
    fn test_typestate_deadlock_states_error_excluded() {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("Init"));
        v.add_state(state("Terminal"));
        v.add_transition(trans("Init", "Terminal", "finish"));
        v.set_initial("Init");
        v.add_error_state("Terminal");
        // "Terminal" has no outgoing transitions but IS an error/terminal state.
        let deadlocks = v.deadlock_states();
        assert!(!deadlocks.contains(&"Terminal".to_string()));
    }

    #[test]
    fn test_typestate_state_property() {
        let prop =
            StateProperty { state_name: "Open".to_string(), invariant: "fd >= 0".to_string() };
        assert_eq!(prop.state_name, "Open");
        assert_eq!(prop.invariant, "fd >= 0");
    }

    #[test]
    fn test_typestate_transition_with_guard() {
        let t = StateTransition {
            from: "Open".to_string(),
            to: "Locked".to_string(),
            method: "lock".to_string(),
            guard: Some("has_permission".to_string()),
        };
        assert_eq!(t.guard, Some("has_permission".to_string()));
    }

    #[test]
    fn test_typestate_deadlock_detected_error_variant() {
        let err = TransitionError::DeadlockDetected(vec!["A".into(), "B".into()]);
        let msg = format!("{err}");
        assert!(msg.contains("deadlock"));
        assert!(msg.contains("A"));
        assert!(msg.contains("B"));
    }

    #[test]
    fn test_typestate_initial_state_not_in_states() {
        let mut v = TypeStateVerifier::new();
        v.add_state(state("A"));
        v.set_initial("B"); // B not added as state
        assert_eq!(v.verify_transitions(), Err(TransitionError::MissingInitialState));
    }
}
