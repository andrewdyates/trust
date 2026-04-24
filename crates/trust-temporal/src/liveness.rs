// trust-temporal/liveness.rs: Liveness property checking for state machines
//
// Checks liveness properties ("something good eventually happens") using
// Buchi automata construction over state machine graphs. Produces lasso-shaped
// counterexamples (prefix + cycle) when a liveness property is violated.
//
// Key concepts:
// - LivenessProperty: a named "eventually" formula over state labels
// - ResponseProperty: if P then eventually Q
// - Buchi automata: acceptance = visit accepting states infinitely often
// - Lasso counterexample: finite prefix + repeating cycle that avoids acceptance
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};

use crate::{StateId, StateMachine};

/// A liveness property: something must eventually hold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LivenessProperty {
    /// Human-readable name for the property.
    pub name: String,
    /// The state label that must eventually be reached.
    /// A state satisfies this if its labels contain `eventually_formula`.
    pub eventually_formula: String,
}

impl LivenessProperty {
    /// Create a new liveness property.
    #[must_use]
    pub fn new(name: impl Into<String>, eventually_formula: impl Into<String>) -> Self {
        Self { name: name.into(), eventually_formula: eventually_formula.into() }
    }
}

/// A response property: if P holds, then Q must eventually hold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResponseProperty {
    /// Human-readable name.
    pub name: String,
    /// Trigger condition (label that must be present).
    pub trigger: String,
    /// Response condition (label that must eventually be reached).
    pub response: String,
}

#[cfg(test)]
impl ResponseProperty {
    /// Create a new response property.
    #[must_use]
    fn new(
        name: impl Into<String>,
        trigger: impl Into<String>,
        response: impl Into<String>,
    ) -> Self {
        Self { name: name.into(), trigger: trigger.into(), response: response.into() }
    }

    /// Convert to a liveness property by encoding as "from any trigger state,
    /// eventually reach a response state".
    #[must_use]
    fn to_liveness(&self) -> LivenessProperty {
        LivenessProperty { name: self.name.clone(), eventually_formula: self.response.clone() }
    }
}

/// Result of a liveness check.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum LivenessResult {
    /// The property is satisfied: all infinite paths eventually reach an
    /// accepting state.
    Satisfied,
    /// The property is violated: there exists an infinite path (lasso-shaped)
    /// that never reaches an accepting state.
    Violated {
        /// Lasso-shaped counterexample: prefix leads to a cycle.
        /// `lasso_trace[..cycle_start]` is the prefix.
        /// `lasso_trace[cycle_start..]` is the repeating cycle.
        lasso_trace: Vec<StateId>,
        /// Index where the cycle begins in `lasso_trace`.
        cycle_start: usize,
    },
}

#[cfg(test)]
impl LivenessResult {
    /// Returns true if the property is satisfied.
    #[must_use]
    pub(crate) fn is_satisfied(&self) -> bool {
        matches!(self, LivenessResult::Satisfied)
    }
}

/// Check a liveness property against a state machine.
///
/// A liveness property `F phi` (eventually phi) is satisfied if every infinite
/// execution path eventually visits a state whose labels contain `phi`.
///
/// The algorithm:
/// 1. Identify "accepting" states: those whose labels contain the formula.
/// 2. Find all reachable strongly connected components (SCCs).
/// 3. If any non-trivial SCC (has a cycle) is reachable and contains no
///    accepting state, then liveness is violated. Produce a lasso counterexample.
///
/// Non-trivial SCC: has at least one internal edge (including self-loops).
#[must_use]
pub fn check_liveness(sm: &StateMachine, prop: &LivenessProperty) -> LivenessResult {
    if sm.states.is_empty() {
        return LivenessResult::Satisfied;
    }

    // Identify accepting states
    let accepting: FxHashSet<StateId> = sm
        .states
        .iter()
        .filter(|s| s.labels.contains(&prop.eventually_formula))
        .map(|s| s.id)
        .collect();

    // Build adjacency map
    let adj = build_adjacency(sm);

    // Find reachable state IDs from initial
    let reachable = reachable_set(sm.initial, &adj);

    // Find SCCs using Tarjan's algorithm
    let sccs = tarjan_scc(&reachable, &adj);

    // Check each SCC for violations
    for scc in &sccs {
        // Skip trivial SCCs (single node with no self-loop)
        if scc.len() == 1 {
            let state = scc[0];
            let has_self_loop = adj.get(&state).is_some_and(|succs| succs.contains(&state));
            if !has_self_loop {
                continue;
            }
        }

        // Check if this SCC has any accepting state
        let has_accepting = scc.iter().any(|s| accepting.contains(s));
        if !has_accepting {
            // Violation found: build a lasso counterexample
            let lasso = build_lasso(sm.initial, scc, &adj);
            return LivenessResult::Violated {
                lasso_trace: lasso.trace,
                cycle_start: lasso.cycle_start,
            };
        }
    }

    LivenessResult::Satisfied
}

/// Check a response property: G(trigger -> F response).
///
/// For every reachable state with the trigger label, check that all infinite
/// paths from it eventually reach a state with the response label.
#[cfg(test)]
#[must_use]
fn check_response(sm: &StateMachine, prop: &ResponseProperty) -> LivenessResult {
    if sm.states.is_empty() {
        return LivenessResult::Satisfied;
    }

    let adj = build_adjacency(sm);
    let reachable = reachable_set(sm.initial, &adj);

    // Find trigger states
    let trigger_states: Vec<StateId> = sm
        .states
        .iter()
        .filter(|s| reachable.contains(&s.id))
        .filter(|s| s.labels.contains(&prop.trigger))
        .map(|s| s.id)
        .collect();

    // Response states
    let response_states: FxHashSet<StateId> =
        sm.states.iter().filter(|s| s.labels.contains(&prop.response)).map(|s| s.id).collect();

    // For each trigger state, check liveness of reaching a response state
    for trigger_id in &trigger_states {
        // Find SCCs reachable from trigger_id
        let reachable_from_trigger = reachable_set(*trigger_id, &adj);
        let sccs = tarjan_scc(&reachable_from_trigger, &adj);

        for scc in &sccs {
            if scc.len() == 1 {
                let state = scc[0];
                let has_self_loop = adj.get(&state).is_some_and(|succs| succs.contains(&state));
                if !has_self_loop {
                    continue;
                }
            }

            let has_response = scc.iter().any(|s| response_states.contains(s));
            if !has_response {
                let lasso = build_lasso(sm.initial, scc, &adj);
                return LivenessResult::Violated {
                    lasso_trace: lasso.trace,
                    cycle_start: lasso.cycle_start,
                };
            }
        }
    }

    LivenessResult::Satisfied
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Build an adjacency map from a state machine.
fn build_adjacency(sm: &StateMachine) -> FxHashMap<StateId, Vec<StateId>> {
    let mut adj: FxHashMap<StateId, Vec<StateId>> = FxHashMap::default();
    for s in &sm.states {
        adj.entry(s.id).or_default();
    }
    for t in &sm.transitions {
        adj.entry(t.from).or_default().push(t.to);
    }
    adj
}

/// BFS to find all reachable states from `start`.
fn reachable_set(start: StateId, adj: &FxHashMap<StateId, Vec<StateId>>) -> FxHashSet<StateId> {
    let mut visited = FxHashSet::default();
    let mut queue = VecDeque::new();
    visited.insert(start);
    queue.push_back(start);
    while let Some(current) = queue.pop_front() {
        if let Some(succs) = adj.get(&current) {
            for &next in succs {
                if visited.insert(next) {
                    queue.push_back(next);
                }
            }
        }
    }
    visited
}

/// Tarjan's SCC algorithm. Returns SCCs in reverse topological order.
fn tarjan_scc(
    states: &FxHashSet<StateId>,
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
        states: &FxHashSet<StateId>,
        adj: &FxHashMap<StateId, Vec<StateId>>,
        ts: &mut TarjanState,
    ) {
        ts.index.insert(v, ts.index_counter);
        ts.lowlink.insert(v, ts.index_counter);
        ts.index_counter += 1;
        ts.stack.push(v);
        ts.on_stack.insert(v);

        if let Some(succs) = adj.get(&v) {
            for &w in succs {
                if !states.contains(&w) {
                    continue;
                }
                if !ts.index.contains_key(&w) {
                    strongconnect(w, states, adj, ts);
                    let w_ll = ts.lowlink[&w];
                    let v_ll = ts.lowlink.get_mut(&v).expect("invariant: v in lowlink");
                    *v_ll = (*v_ll).min(w_ll);
                } else if ts.on_stack.contains(&w) {
                    let w_idx = ts.index[&w];
                    let v_ll = ts.lowlink.get_mut(&v).expect("invariant: v in lowlink");
                    *v_ll = (*v_ll).min(w_idx);
                }
            }
        }

        if ts.lowlink[&v] == ts.index[&v] {
            let mut scc = Vec::new();
            while let Some(w) = ts.stack.pop() {
                ts.on_stack.remove(&w);
                scc.push(w);
                if w == v {
                    break;
                }
            }
            ts.sccs.push(scc);
        }
    }

    let mut ts = TarjanState {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: FxHashSet::default(),
        index: FxHashMap::default(),
        lowlink: FxHashMap::default(),
        sccs: Vec::new(),
    };

    // Sort for deterministic order
    let mut sorted_states: Vec<StateId> = states.iter().copied().collect();
    sorted_states.sort();

    for &v in &sorted_states {
        if !ts.index.contains_key(&v) {
            strongconnect(v, states, adj, &mut ts);
        }
    }

    ts.sccs
}

/// A lasso-shaped trace: prefix leading to a cycle.
struct Lasso {
    trace: Vec<StateId>,
    cycle_start: usize,
}

/// Build a lasso-shaped counterexample: path from initial to an SCC node,
/// then a cycle within the SCC.
fn build_lasso(initial: StateId, scc: &[StateId], adj: &FxHashMap<StateId, Vec<StateId>>) -> Lasso {
    let scc_set: FxHashSet<StateId> = scc.iter().copied().collect();
    let scc_entry = scc[0];

    // BFS from initial to scc_entry (prefix)
    let prefix = bfs_path(initial, scc_entry, adj);

    // Find a cycle within the SCC starting and ending at scc_entry
    let cycle = find_cycle_in_scc(scc_entry, &scc_set, adj);

    let cycle_start = prefix.len();
    let mut trace = prefix;
    trace.extend_from_slice(&cycle);

    Lasso { trace, cycle_start }
}

/// BFS shortest path from `start` to `target`.
fn bfs_path(
    start: StateId,
    target: StateId,
    adj: &FxHashMap<StateId, Vec<StateId>>,
) -> Vec<StateId> {
    if start == target {
        return vec![start];
    }

    let mut visited = FxHashSet::default();
    let mut parent: FxHashMap<StateId, StateId> = FxHashMap::default();
    let mut queue = VecDeque::new();
    visited.insert(start);
    queue.push_back(start);

    while let Some(current) = queue.pop_front() {
        if let Some(succs) = adj.get(&current) {
            for &next in succs {
                if visited.insert(next) {
                    parent.insert(next, current);
                    if next == target {
                        let mut path = vec![target];
                        let mut cur = target;
                        while let Some(&prev) = parent.get(&cur) {
                            path.push(prev);
                            cur = prev;
                        }
                        path.reverse();
                        return path;
                    }
                    queue.push_back(next);
                }
            }
        }
    }

    vec![start]
}

/// Find a cycle within an SCC starting at `entry`.
fn find_cycle_in_scc(
    entry: StateId,
    scc_set: &FxHashSet<StateId>,
    adj: &FxHashMap<StateId, Vec<StateId>>,
) -> Vec<StateId> {
    // DFS to find a path from entry back to entry within the SCC
    let mut visited = FxHashSet::default();
    let mut parent: FxHashMap<StateId, StateId> = FxHashMap::default();
    let mut stack = Vec::new();

    if let Some(succs) = adj.get(&entry) {
        for &next in succs {
            if scc_set.contains(&next) {
                stack.push(next);
                parent.insert(next, entry);
            }
        }
    }

    while let Some(current) = stack.pop() {
        if current == entry {
            // Found cycle, reconstruct
            // Trace back through parent from entry (the second visit)
            // We need to go backwards from the predecessor that led to entry
            if let Some(&pred) = parent.get(&current) {
                let mut back = pred;
                let mut path = vec![entry, back];
                while back != entry {
                    if let Some(&p) = parent.get(&back) {
                        back = p;
                        path.push(back);
                    } else {
                        break;
                    }
                }
                path.reverse();
                return path;
            }
            return vec![entry, entry];
        }
        if !visited.insert(current) {
            continue;
        }
        if let Some(succs) = adj.get(&current) {
            for &next in succs {
                if !visited.contains(&next) && scc_set.contains(&next) {
                    parent.insert(next, current);
                    stack.push(next);
                } else if next == entry {
                    // Found the back-edge to entry
                    parent.insert(next, current);
                    let mut path = vec![entry];
                    let mut back = current;
                    path.push(back);
                    while back != entry {
                        if let Some(&p) = parent.get(&back) {
                            back = p;
                            path.push(back);
                        } else {
                            break;
                        }
                    }
                    path.reverse();
                    return path;
                }
            }
        }
    }

    // Fallback: self-loop
    vec![entry, entry]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{State, StateMachineBuilder, Transition};

    // ---- check_liveness: satisfied ----

    #[test]
    fn test_liveness_simple_satisfied() {
        // Linear: Idle -> Working -> Done(accepting)
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("idle"))
            .add_state(State::new(StateId(1), "Working").with_label("working"))
            .add_state(State::new(StateId(2), "Done").with_label("done"))
            .add_transition(Transition::new(StateId(0), StateId(1), "start"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
            .build();

        let prop = LivenessProperty::new("eventually_done", "done");
        // No cycles at all, so no infinite non-accepting path.
        let result = check_liveness(&sm, &prop);
        assert!(result.is_satisfied());
    }

    #[test]
    fn test_liveness_cycle_with_accepting_state() {
        // Cycle: A -> B -> C -> A, where C has accepting label
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("b"))
            .add_state(State::new(StateId(2), "C").with_label("goal"))
            .add_transition(Transition::new(StateId(0), StateId(1), "ab"))
            .add_transition(Transition::new(StateId(1), StateId(2), "bc"))
            .add_transition(Transition::new(StateId(2), StateId(0), "ca"))
            .build();

        let prop = LivenessProperty::new("reach_goal", "goal");
        let result = check_liveness(&sm, &prop);
        assert!(result.is_satisfied());
    }

    #[test]
    fn test_liveness_empty_machine() {
        let sm = StateMachineBuilder::new(StateId(0)).build();
        let prop = LivenessProperty::new("test", "anything");
        // StateMachineBuilder inserts a default state with name "state_0" and no labels.
        // Since there are no transitions and thus no cycles, liveness is vacuously true.
        let result = check_liveness(&sm, &prop);
        assert!(result.is_satisfied());
    }

    // ---- check_liveness: violated ----

    #[test]
    fn test_liveness_violation_self_loop() {
        // Idle -> Spin(self-loop, no accepting label)
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("idle"))
            .add_state(State::new(StateId(1), "Spin").with_label("spinning"))
            .add_transition(Transition::new(StateId(0), StateId(1), "enter"))
            .add_transition(Transition::new(StateId(1), StateId(1), "spin"))
            .build();

        let prop = LivenessProperty::new("eventually_done", "done");
        let result = check_liveness(&sm, &prop);

        match &result {
            LivenessResult::Violated { lasso_trace, cycle_start } => {
                // Prefix ends before cycle
                assert!(*cycle_start > 0 || lasso_trace[0] == StateId(1));
                // Cycle must include Spin
                let cycle = &lasso_trace[*cycle_start..];
                assert!(cycle.contains(&StateId(1)));
            }
            LivenessResult::Satisfied => panic!("expected violation"),
        }
    }

    #[test]
    fn test_liveness_violation_cycle_no_accepting() {
        // A -> B -> A (cycle), neither has "done" label
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("b"))
            .add_transition(Transition::new(StateId(0), StateId(1), "ab"))
            .add_transition(Transition::new(StateId(1), StateId(0), "ba"))
            .build();

        let prop = LivenessProperty::new("eventually_done", "done");
        let result = check_liveness(&sm, &prop);

        match &result {
            LivenessResult::Violated { lasso_trace, cycle_start } => {
                assert!(!lasso_trace.is_empty());
                let cycle = &lasso_trace[*cycle_start..];
                assert!(cycle.len() >= 2, "cycle should have at least 2 states");
            }
            LivenessResult::Satisfied => panic!("expected violation"),
        }
    }

    #[test]
    fn test_liveness_lasso_structure() {
        // Init -> Loop1 -> Loop2 -> Loop1 (trapped cycle)
        // Init has no accepting labels; the cycle has none either
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Init"))
            .add_state(State::new(StateId(1), "Loop1"))
            .add_state(State::new(StateId(2), "Loop2"))
            .add_transition(Transition::new(StateId(0), StateId(1), "enter"))
            .add_transition(Transition::new(StateId(1), StateId(2), "step"))
            .add_transition(Transition::new(StateId(2), StateId(1), "back"))
            .build();

        let prop = LivenessProperty::new("reach_goal", "goal");
        let result = check_liveness(&sm, &prop);

        match &result {
            LivenessResult::Violated { lasso_trace, cycle_start } => {
                // Prefix: path from Init to the cycle
                let prefix = &lasso_trace[..*cycle_start];
                assert!(prefix.contains(&StateId(0)), "prefix should start from init");

                // Cycle: should contain loop states
                let cycle = &lasso_trace[*cycle_start..];
                assert!(!cycle.is_empty(), "cycle should not be empty");
            }
            LivenessResult::Satisfied => panic!("expected violation"),
        }
    }

    // ---- check_response ----

    #[test]
    fn test_response_satisfied() {
        // request -> process -> response -> idle -> request -> ...
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("idle"))
            .add_state(State::new(StateId(1), "Requested").with_label("request"))
            .add_state(State::new(StateId(2), "Processing").with_label("processing"))
            .add_state(State::new(StateId(3), "Responded").with_label("response"))
            .add_transition(Transition::new(StateId(0), StateId(1), "req"))
            .add_transition(Transition::new(StateId(1), StateId(2), "process"))
            .add_transition(Transition::new(StateId(2), StateId(3), "respond"))
            .add_transition(Transition::new(StateId(3), StateId(0), "reset"))
            .build();

        let prop = ResponseProperty::new("req_resp", "request", "response");
        let result = check_response(&sm, &prop);
        assert!(result.is_satisfied());
    }

    #[test]
    fn test_response_violated_stuck_after_trigger() {
        // request -> spin(self-loop) — never reaches response
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("idle"))
            .add_state(State::new(StateId(1), "Requested").with_label("request"))
            .add_state(State::new(StateId(2), "Spin").with_label("stuck"))
            .add_transition(Transition::new(StateId(0), StateId(1), "req"))
            .add_transition(Transition::new(StateId(1), StateId(2), "enter_spin"))
            .add_transition(Transition::new(StateId(2), StateId(2), "spin"))
            .build();

        let prop = ResponseProperty::new("req_resp", "request", "response");
        let result = check_response(&sm, &prop);
        assert!(!result.is_satisfied());
    }

    #[test]
    fn test_response_no_trigger_vacuously_true() {
        // No state has the trigger label
        let sm = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("b"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let prop = ResponseProperty::new("req_resp", "request", "response");
        let result = check_response(&sm, &prop);
        assert!(result.is_satisfied());
    }

    // ---- ResponseProperty conversion ----

    #[test]
    fn test_response_to_liveness() {
        let rp = ResponseProperty::new("req_resp", "request", "response");
        let lp = rp.to_liveness();
        assert_eq!(lp.name, "req_resp");
        assert_eq!(lp.eventually_formula, "response");
    }
}
