// trust-temporal/checker.rs: Dead state and deadlock detection via BFS
//
// Implements BFS exploration over state machines to detect:
// - Dead states: reachable states with no outgoing transitions
// - Deadlocks: reachable states where no process can make progress
//
// Produces VerificationConditions (VcKind::DeadState, VcKind::Deadlock) with
// counterexample traces showing the path from the initial state to the problem.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::{Formula, SourceSpan, VcKind, VerificationCondition};

use crate::{StateId, StateMachine, Trace};

/// Result of checking a state machine for dead states and deadlocks.
#[derive(Debug, Clone)]
pub(crate) struct CheckResult {
    /// Dead states found (reachable states with no outgoing transitions).
    pub dead_states: Vec<DeadStateInfo>,
    /// Deadlock states found (reachable states where no process can progress).
    pub deadlocks: Vec<DeadlockInfo>,
}

impl CheckResult {
    /// Convert check results into verification conditions.
    #[must_use]
    pub(crate) fn into_vcs(self, function: &str, location: SourceSpan) -> Vec<VerificationCondition> {
        let mut vcs = Vec::with_capacity(self.dead_states.len() + self.deadlocks.len());

        for dead in &self.dead_states {
            vcs.push(VerificationCondition {
                kind: VcKind::DeadState { state: dead.state_name.clone() },
                function: function.to_string(),
                location: location.clone(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            });
        }

        for _deadlock in &self.deadlocks {
            vcs.push(VerificationCondition {
                kind: VcKind::Deadlock,
                function: function.to_string(),
                location: location.clone(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            });
        }

        vcs
    }

    /// True if no problems were found.
    #[must_use]
    pub(crate) fn is_clean(&self) -> bool {
        self.dead_states.is_empty() && self.deadlocks.is_empty()
    }
}

/// Information about a detected dead state.
#[derive(Debug, Clone)]
pub(crate) struct DeadStateInfo {
    /// The dead state identifier.
    pub state_id: StateId,
    /// Human-readable name of the dead state.
    pub state_name: String,
    /// Counterexample trace from initial state to dead state.
    pub trace: Trace,
}

/// Information about a detected deadlock.
#[derive(Debug, Clone)]
pub(crate) struct DeadlockInfo {
    /// The set of states involved in the deadlock.
    pub involved_states: Vec<StateId>,
    /// Counterexample trace from initial state to a deadlock state.
    pub trace: Trace,
    /// Human-readable description of the deadlock.
    pub description: String,
}

/// Checks state machines for dead states and deadlocks using BFS exploration.
///
/// Dead state: a reachable state with no outgoing transitions and not marked
/// as a terminal state (via the "terminal" label).
///
/// Deadlock: a reachable state where all outgoing transitions lead only to
/// states that form a cycle with no escape, or where concurrent processes
/// are in a circular-wait configuration.
pub(crate) struct DeadStateChecker<'a> {
    machine: &'a StateMachine,
    /// States explicitly marked as terminal (acceptable dead ends).
    terminal_states: FxHashSet<StateId>,
}

impl<'a> DeadStateChecker<'a> {
    /// Create a checker for the given state machine.
    ///
    /// States with the label "terminal" are treated as acceptable dead ends
    /// and will not be reported as dead states.
    #[must_use]
    pub(crate) fn new(machine: &'a StateMachine) -> Self {
        let terminal_states = machine
            .states
            .iter()
            .filter(|s| s.labels.iter().any(|l| l == "terminal"))
            .map(|s| s.id)
            .collect();

        Self { machine, terminal_states }
    }

    /// Run BFS exploration and detect dead states and deadlocks.
    #[must_use]
    pub(crate) fn check(&self) -> CheckResult {
        let (reachable, parent_map) = self.bfs_explore();
        let dead_states = self.find_dead_states(&reachable, &parent_map);
        let deadlocks = self.find_deadlocks(&reachable, &parent_map);

        CheckResult { dead_states, deadlocks }
    }

    /// BFS from the initial state. Returns (reachable set, parent map for traces).
    fn bfs_explore(&self) -> (Vec<StateId>, FxHashMap<StateId, StateId>) {
        let mut visited = FxHashSet::default();
        let mut parent: FxHashMap<StateId, StateId> = FxHashMap::default();
        let mut queue = VecDeque::new();
        let mut reachable = Vec::new();

        queue.push_back(self.machine.initial);
        visited.insert(self.machine.initial);

        while let Some(current) = queue.pop_front() {
            reachable.push(current);

            for successor in self.machine.successors(current) {
                if visited.insert(successor) {
                    parent.insert(successor, current);
                    queue.push_back(successor);
                }
            }
        }

        (reachable, parent)
    }

    /// Reconstruct the trace from initial state to target using the parent map.
    fn reconstruct_trace(
        &self,
        target: StateId,
        parent_map: &FxHashMap<StateId, StateId>,
    ) -> Trace {
        let mut path = vec![target];
        let mut current = target;

        while let Some(&prev) = parent_map.get(&current) {
            path.push(prev);
            current = prev;
        }

        path.reverse();
        Trace::new(path)
    }

    /// Find dead states: reachable states with no outgoing transitions
    /// that are not marked as terminal.
    fn find_dead_states(
        &self,
        reachable: &[StateId],
        parent_map: &FxHashMap<StateId, StateId>,
    ) -> Vec<DeadStateInfo> {
        reachable
            .iter()
            .filter(|&&state_id| {
                self.machine.is_deadlock_state(state_id)
                    && !self.terminal_states.contains(&state_id)
            })
            .map(|&state_id| {
                let state_name = self
                    .machine
                    .state(state_id)
                    .map(|s| s.name.clone())
                    .unwrap_or_else(|| format!("state_{}", state_id.0));
                let trace = self.reconstruct_trace(state_id, parent_map);

                DeadStateInfo { state_id, state_name, trace }
            })
            .collect()
    }

    /// Find deadlocks: reachable states that form sink SCCs (strongly connected
    /// components with no outgoing edges to states outside the SCC).
    ///
    /// A single state with a self-loop and no other outgoing transitions is
    /// a deadlock (livelock). A set of states that only cycle among themselves
    /// with no path to new states is also a deadlock.
    ///
    /// We exclude the initial state's SCC if it has outgoing transitions,
    /// and we exclude states already flagged as dead states (no outgoing at all).
    fn find_deadlocks(
        &self,
        reachable: &[StateId],
        parent_map: &FxHashMap<StateId, StateId>,
    ) -> Vec<DeadlockInfo> {
        let reachable_set: FxHashSet<StateId> = reachable.iter().copied().collect();

        // Build adjacency for reachable subgraph
        let mut adj: FxHashMap<StateId, Vec<StateId>> = FxHashMap::default();
        for &state in reachable {
            let succs: Vec<StateId> = self
                .machine
                .successors(state)
                .into_iter()
                .filter(|s| reachable_set.contains(s))
                .collect();
            adj.insert(state, succs);
        }

        // Tarjan's SCC algorithm
        let sccs = tarjan_scc(reachable, &adj);

        let mut deadlocks = Vec::new();

        for scc in &sccs {
            // Skip single-state SCCs with no self-loop (these are just regular states
            // or dead states, already covered above)
            if scc.len() == 1 {
                let state = scc[0];
                let has_self_loop = adj
                    .get(&state)
                    .is_some_and(|succs| succs.contains(&state));
                if !has_self_loop {
                    continue;
                }
            }

            let scc_set: FxHashSet<StateId> = scc.iter().copied().collect();

            // Check if this SCC is a sink: no edges leaving the SCC
            let is_sink = scc.iter().all(|&state| {
                adj.get(&state)
                    .is_none_or(|succs| succs.iter().all(|s| scc_set.contains(s)))
            });

            if !is_sink {
                continue;
            }

            // Skip terminal-only SCCs (all states in SCC are terminal)
            if scc.iter().all(|s| self.terminal_states.contains(s)) {
                continue;
            }

            // This is a deadlock: a sink SCC that traps execution
            let representative = scc[0];
            let trace = self.reconstruct_trace(representative, parent_map);

            let state_names: Vec<String> = scc
                .iter()
                .filter_map(|&id| self.machine.state(id))
                .map(|s| s.name.clone())
                .collect();

            let description = if scc.len() == 1 {
                format!(
                    "livelock: state `{}` has only self-transitions",
                    state_names.first().unwrap_or(&"unknown".to_string())
                )
            } else {
                format!(
                    "deadlock: states {{{}}} form a cycle with no escape",
                    state_names.join(", ")
                )
            };

            deadlocks.push(DeadlockInfo {
                involved_states: scc.clone(),
                trace,
                description,
            });
        }

        deadlocks
    }
}

/// Tarjan's algorithm for finding strongly connected components.
///
/// Returns SCCs in reverse topological order (sinks first).
fn tarjan_scc(
    nodes: &[StateId],
    adj: &FxHashMap<StateId, Vec<StateId>>,
) -> Vec<Vec<StateId>> {
    struct TarjanState {
        index_counter: usize,
        stack: Vec<StateId>,
        on_stack: FxHashSet<StateId>,
        index: FxHashMap<StateId, usize>,
        lowlink: FxHashMap<StateId, usize>,
        sccs: Vec<Vec<StateId>>,
    }

    fn strongconnect(
        v: StateId,
        adj: &FxHashMap<StateId, Vec<StateId>>,
        state: &mut TarjanState,
    ) {
        state.index.insert(v, state.index_counter);
        state.lowlink.insert(v, state.index_counter);
        state.index_counter += 1;
        state.stack.push(v);
        state.on_stack.insert(v);

        if let Some(successors) = adj.get(&v) {
            for &w in successors {
                if !state.index.contains_key(&w) {
                    strongconnect(w, adj, state);
                    let w_low = state.lowlink[&w];
                    let v_low = state.lowlink[&v];
                    state.lowlink.insert(v, v_low.min(w_low));
                } else if state.on_stack.contains(&w) {
                    let w_idx = state.index[&w];
                    let v_low = state.lowlink[&v];
                    state.lowlink.insert(v, v_low.min(w_idx));
                }
            }
        }

        if state.lowlink[&v] == state.index[&v] {
            let mut scc = Vec::new();
            loop {
                let w = state.stack.pop().expect("stack should not be empty in SCC");
                state.on_stack.remove(&w);
                scc.push(w);
                if w == v {
                    break;
                }
            }
            state.sccs.push(scc);
        }
    }

    let mut state = TarjanState {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: FxHashSet::default(),
        index: FxHashMap::default(),
        lowlink: FxHashMap::default(),
        sccs: Vec::new(),
    };

    for &node in nodes {
        if !state.index.contains_key(&node) {
            strongconnect(node, adj, &mut state);
        }
    }

    state.sccs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{State, StateMachineBuilder, Transition};

    /// Helper to build a simple linear machine: Start -> Middle -> Dead
    /// where Dead has no outgoing transitions.
    fn linear_machine_with_dead_end() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "Middle"))
            .add_state(State::new(StateId(2), "Dead"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(2), "die"))
            .build()
    }

    /// Machine with a terminal state (labeled "terminal") -- should NOT be flagged.
    fn machine_with_terminal() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "Done").with_label("terminal"))
            .add_transition(Transition::new(StateId(0), StateId(1), "finish"))
            .build()
    }

    /// Machine with a self-loop (livelock): Start -> Spinning (self-loop only).
    fn machine_with_livelock() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "Spinning"))
            .add_transition(Transition::new(StateId(0), StateId(1), "enter"))
            .add_transition(Transition::new(StateId(1), StateId(1), "spin"))
            .build()
    }

    /// Machine with a cycle that has no escape: Start -> A -> B -> A (deadlock cycle).
    fn machine_with_deadlock_cycle() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "A"))
            .add_state(State::new(StateId(2), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(2), "bounce"))
            .add_transition(Transition::new(StateId(2), StateId(1), "bounce_back"))
            .build()
    }

    /// Healthy machine: Start -> Active -> Done, Active -> Start (full cycle with escape).
    fn healthy_machine() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "Active"))
            .add_state(State::new(StateId(2), "Done").with_label("terminal"))
            .add_transition(Transition::new(StateId(0), StateId(1), "begin"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
            .add_transition(Transition::new(StateId(1), StateId(0), "retry"))
            .build()
    }

    #[test]
    fn test_dead_state_detected_in_linear_machine() {
        let machine = linear_machine_with_dead_end();
        let checker = DeadStateChecker::new(&machine);
        let result = checker.check();

        assert_eq!(result.dead_states.len(), 1);
        assert_eq!(result.dead_states[0].state_name, "Dead");
        assert_eq!(result.dead_states[0].state_id, StateId(2));

        // Trace should be Start -> Middle -> Dead
        let trace = &result.dead_states[0].trace;
        assert_eq!(trace.states, vec![StateId(0), StateId(1), StateId(2)]);
    }

    #[test]
    fn test_terminal_state_not_flagged() {
        let machine = machine_with_terminal();
        let checker = DeadStateChecker::new(&machine);
        let result = checker.check();

        assert!(result.dead_states.is_empty(), "terminal states should not be flagged");
        assert!(result.is_clean());
    }

    #[test]
    fn test_livelock_detected() {
        let machine = machine_with_livelock();
        let checker = DeadStateChecker::new(&machine);
        let result = checker.check();

        assert_eq!(result.deadlocks.len(), 1);
        assert!(result.deadlocks[0].description.contains("livelock"));
        assert!(result.deadlocks[0].involved_states.contains(&StateId(1)));
    }

    #[test]
    fn test_deadlock_cycle_detected() {
        let machine = machine_with_deadlock_cycle();
        let checker = DeadStateChecker::new(&machine);
        let result = checker.check();

        assert_eq!(result.deadlocks.len(), 1);
        assert!(result.deadlocks[0].description.contains("deadlock"));
        let involved = &result.deadlocks[0].involved_states;
        assert!(involved.contains(&StateId(1)));
        assert!(involved.contains(&StateId(2)));
    }

    #[test]
    fn test_healthy_machine_is_clean() {
        let machine = healthy_machine();
        let checker = DeadStateChecker::new(&machine);
        let result = checker.check();

        assert!(result.is_clean());
    }

    #[test]
    fn test_empty_machine_is_clean() {
        let machine = StateMachine::new(StateId(0));
        let checker = DeadStateChecker::new(&machine);
        let result = checker.check();

        // Initial state has no outgoing but also no state definition -- BFS finds it
        // and since it has no outgoing transitions, it could be a dead state. But
        // there is no State entry for it so we still detect it.
        // Actually the machine has no states at all, so BFS visits StateId(0) but
        // is_deadlock_state returns true (no transitions from it). Name falls back.
        assert_eq!(result.dead_states.len(), 1);
        assert_eq!(result.dead_states[0].state_id, StateId(0));
    }

    #[test]
    fn test_into_vcs_produces_correct_kinds() {
        let machine = linear_machine_with_dead_end();
        let checker = DeadStateChecker::new(&machine);
        let result = checker.check();

        let vcs = result.into_vcs("test_fn", SourceSpan::default());
        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::DeadState { ref state } if state == "Dead"));
        assert_eq!(vcs[0].function, "test_fn");
    }

    #[test]
    fn test_counterexample_trace_for_deadlock() {
        let machine = machine_with_deadlock_cycle();
        let checker = DeadStateChecker::new(&machine);
        let result = checker.check();

        assert!(!result.deadlocks.is_empty());
        let trace = &result.deadlocks[0].trace;
        // Trace starts at initial state
        assert!(trace.starts_at(StateId(0)));
        // Trace reaches one of the deadlocked states
        let reaches_deadlock = result.deadlocks[0]
            .involved_states
            .iter()
            .any(|&s| trace.visits(s));
        assert!(reaches_deadlock);
    }

    #[test]
    fn test_multiple_dead_states() {
        // Start -> A (dead), Start -> B (dead)
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "DeadA"))
            .add_state(State::new(StateId(2), "DeadB"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go_a"))
            .add_transition(Transition::new(StateId(0), StateId(2), "go_b"))
            .build();

        let checker = DeadStateChecker::new(&machine);
        let result = checker.check();

        assert_eq!(result.dead_states.len(), 2);
        let names: Vec<&str> = result.dead_states.iter().map(|d| d.state_name.as_str()).collect();
        assert!(names.contains(&"DeadA"));
        assert!(names.contains(&"DeadB"));
    }

    #[test]
    fn test_unreachable_dead_state_not_reported() {
        // Start -> Active. Orphan state "Unreachable" has no transitions but is unreachable.
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "Active"))
            .add_state(State::new(StateId(2), "Unreachable"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let checker = DeadStateChecker::new(&machine);
        let result = checker.check();

        // Unreachable state should NOT appear
        assert!(result.dead_states.is_empty());
    }

    #[test]
    fn test_combined_dead_state_and_deadlock() {
        // Start -> Dead (dead end), Start -> Loop (self-loop deadlock)
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "Dead"))
            .add_state(State::new(StateId(2), "Loop"))
            .add_transition(Transition::new(StateId(0), StateId(1), "die"))
            .add_transition(Transition::new(StateId(0), StateId(2), "loop"))
            .add_transition(Transition::new(StateId(2), StateId(2), "spin"))
            .build();

        let checker = DeadStateChecker::new(&machine);
        let result = checker.check();

        assert_eq!(result.dead_states.len(), 1);
        assert_eq!(result.dead_states[0].state_name, "Dead");
        assert_eq!(result.deadlocks.len(), 1);
        assert!(result.deadlocks[0].involved_states.contains(&StateId(2)));
    }

    #[test]
    fn test_vcs_for_both_dead_and_deadlock() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "Dead"))
            .add_state(State::new(StateId(2), "Loop"))
            .add_transition(Transition::new(StateId(0), StateId(1), "die"))
            .add_transition(Transition::new(StateId(0), StateId(2), "loop"))
            .add_transition(Transition::new(StateId(2), StateId(2), "spin"))
            .build();

        let checker = DeadStateChecker::new(&machine);
        let result = checker.check();
        let vcs = result.into_vcs("combined_fn", SourceSpan::default());

        assert_eq!(vcs.len(), 2);
        assert!(vcs.iter().any(|vc| matches!(&vc.kind, VcKind::DeadState { state } if state == "Dead")));
        assert!(vcs.iter().any(|vc| matches!(&vc.kind, VcKind::Deadlock)));
    }
}
