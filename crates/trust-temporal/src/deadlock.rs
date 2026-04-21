// trust-temporal/deadlock.rs: Deadlock detection for enum-based state machines
//
// Detects deadlock paths in EnumStateMachine:
// - Cycles that cannot reach terminal states
// - States where all transitions require impossible guards
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use crate::extract_enum::EnumStateMachine;

/// A path through the state machine that leads to a deadlock.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeadlockPath {
    /// Sequence of state names from the initial state to the deadlock.
    pub path: Vec<String>,
    /// Kind of deadlock detected.
    pub kind: DeadlockKind,
}

/// Classification of deadlock type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DeadlockKind {
    /// State has no outgoing transitions and is not a terminal state.
    Sink { state: String },
    /// A cycle of states with no path to any terminal state.
    TrappedCycle { cycle_states: Vec<String> },
    /// All outgoing transitions from this state have impossible guards.
    AllGuardsImpossible { state: String, guards: Vec<String> },
}

/// Check an `EnumStateMachine` for deadlock paths.
///
/// Terminal states are identified by `terminal_states`. A deadlock occurs when
/// execution can reach a state (or set of states) from which no terminal state
/// is reachable.
///
/// Returns a list of `DeadlockPath`s, each showing a path from the initial
/// state to the deadlock condition.
#[must_use]
pub(crate) fn check_deadlock(
    sm: &EnumStateMachine,
    terminal_states: &[String],
) -> Vec<DeadlockPath> {
    let terminal_set: FxHashSet<&str> = terminal_states.iter().map(|s| s.as_str()).collect();
    let mut results = Vec::new();

    let Some(initial_idx) = sm.initial_state else {
        return results;
    };
    let Some(initial_name) = sm.states.get(initial_idx) else {
        return results;
    };

    // Build adjacency list
    let mut adj: FxHashMap<&str, Vec<&str>> = FxHashMap::default();
    for t in &sm.transitions {
        adj.entry(t.from.as_str()).or_default().push(t.to.as_str());
    }

    // Compute which states can reach a terminal state (backward reachability)
    let can_reach_terminal = backward_reachable(sm, &adj, &terminal_set);

    // Find reachable states from initial
    let reachable = forward_reachable(initial_name, &adj);

    // 1. Check for sink states (no outgoing, not terminal)
    for state in &sm.states {
        if !reachable.contains(state.as_str()) {
            continue;
        }
        if terminal_set.contains(state.as_str()) {
            continue;
        }
        let has_outgoing = adj
            .get(state.as_str())
            .is_some_and(|succs| !succs.is_empty());
        if !has_outgoing {
            let path = find_path(initial_name, state, &adj);
            results.push(DeadlockPath {
                path,
                kind: DeadlockKind::Sink { state: state.clone() },
            });
        }
    }

    // 2. Check for trapped cycles: reachable states that cannot reach any terminal
    let trapped: Vec<&str> = sm
        .states
        .iter()
        .filter(|s| reachable.contains(s.as_str()))
        .filter(|s| !can_reach_terminal.contains(s.as_str()))
        .filter(|s| !terminal_set.contains(s.as_str()))
        .filter(|s| {
            // Only include states that have outgoing transitions (sinks handled above)
            adj.get(s.as_str())
                .is_some_and(|succs| !succs.is_empty())
        })
        .map(|s| s.as_str())
        .collect();

    if !trapped.is_empty() {
        // Group trapped states into connected components (cycles)
        let cycles = find_trapped_cycles(&trapped, &adj);
        for cycle in cycles {
            let representative = cycle[0];
            let path = find_path(initial_name, representative, &adj);
            results.push(DeadlockPath {
                path,
                kind: DeadlockKind::TrappedCycle {
                    cycle_states: cycle.iter().map(|s| s.to_string()).collect(),
                },
            });
        }
    }

    // 3. Check for all-guards-impossible states
    for state in &sm.states {
        if !reachable.contains(state.as_str()) {
            continue;
        }
        let outgoing: Vec<_> = sm
            .transitions
            .iter()
            .filter(|t| t.from == *state)
            .collect();

        if outgoing.is_empty() {
            continue; // Sink, already handled
        }

        let all_guarded = outgoing.iter().all(|t| t.guard.is_some());
        if all_guarded && !outgoing.is_empty() {
            let guards: Vec<String> = outgoing
                .iter()
                .filter_map(|t| t.guard.clone())
                .collect();
            let path = find_path(initial_name, state, &adj);
            results.push(DeadlockPath {
                path,
                kind: DeadlockKind::AllGuardsImpossible {
                    state: state.clone(),
                    guards,
                },
            });
        }
    }

    results
}

/// Compute the set of states reachable from `start` using BFS.
fn forward_reachable<'a>(
    start: &'a str,
    adj: &FxHashMap<&'a str, Vec<&'a str>>,
) -> FxHashSet<&'a str> {
    let mut visited = FxHashSet::default();
    let mut queue = std::collections::VecDeque::new();
    visited.insert(start);
    queue.push_back(start);

    while let Some(current) = queue.pop_front() {
        if let Some(neighbors) = adj.get(current) {
            for &next in neighbors {
                if visited.insert(next) {
                    queue.push_back(next);
                }
            }
        }
    }

    visited
}

/// Compute backward reachability: which states can reach any terminal state.
fn backward_reachable<'a>(
    sm: &'a EnumStateMachine,
    _adj: &FxHashMap<&'a str, Vec<&'a str>>,
    terminal_set: &FxHashSet<&'a str>,
) -> FxHashSet<&'a str> {
    // Build reverse adjacency: to -> [from]
    let mut rev_adj: FxHashMap<&str, Vec<&str>> = FxHashMap::default();
    for t in &sm.transitions {
        rev_adj.entry(t.to.as_str()).or_default().push(t.from.as_str());
    }

    // BFS backward from all terminal states
    let mut visited = FxHashSet::default();
    let mut queue = std::collections::VecDeque::new();

    for &terminal in terminal_set {
        if visited.insert(terminal) {
            queue.push_back(terminal);
        }
    }

    while let Some(current) = queue.pop_front() {
        if let Some(predecessors) = rev_adj.get(current) {
            for &prev in predecessors {
                if visited.insert(prev) {
                    queue.push_back(prev);
                }
            }
        }
    }

    visited
}

/// Find a shortest path from `start` to `target` using BFS.
fn find_path(
    start: &str,
    target: &str,
    adj: &FxHashMap<&str, Vec<&str>>,
) -> Vec<String> {
    if start == target {
        return vec![start.to_string()];
    }

    let mut visited = FxHashSet::default();
    let mut parent: FxHashMap<&str, &str> = FxHashMap::default();
    let mut queue = std::collections::VecDeque::new();

    visited.insert(start);
    queue.push_back(start);

    while let Some(current) = queue.pop_front() {
        if let Some(neighbors) = adj.get(current) {
            for &next in neighbors {
                if visited.insert(next) {
                    parent.insert(next, current);
                    if next == target {
                        // Reconstruct path
                        let mut path = vec![next.to_string()];
                        let mut cur = next;
                        while let Some(&prev) = parent.get(cur) {
                            path.push(prev.to_string());
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

    // No path found, return start alone
    vec![start.to_string()]
}

/// Find connected components (cycles) within trapped states.
fn find_trapped_cycles<'a>(
    trapped: &[&'a str],
    adj: &FxHashMap<&'a str, Vec<&'a str>>,
) -> Vec<Vec<&'a str>> {
    let trapped_set: FxHashSet<&str> = trapped.iter().copied().collect();
    let mut visited = FxHashSet::default();
    let mut components = Vec::new();

    for &state in trapped {
        if visited.contains(state) {
            continue;
        }

        // BFS within trapped states
        let mut component = Vec::new();
        let mut queue = std::collections::VecDeque::new();
        visited.insert(state);
        queue.push_back(state);

        while let Some(current) = queue.pop_front() {
            component.push(current);
            if let Some(neighbors) = adj.get(current) {
                for &next in neighbors {
                    if trapped_set.contains(next) && visited.insert(next) {
                        queue.push_back(next);
                    }
                }
            }
        }

        if !component.is_empty() {
            components.push(component);
        }
    }

    components
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extract_enum::{extract_from_enum_def, extract_transitions, extract_guarded_transitions};

    fn variants(names: &[&str]) -> Vec<String> {
        names.iter().map(|s| s.to_string()).collect()
    }

    fn arms(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
        pairs.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect()
    }

    fn terminals(names: &[&str]) -> Vec<String> {
        names.iter().map(|s| s.to_string()).collect()
    }

    // ---- sink deadlocks ----

    #[test]
    fn test_deadlock_sink_state() {
        let mut sm = extract_from_enum_def("State", &variants(&["Idle", "Running", "Stuck"]));
        sm.add_transitions(extract_transitions(&arms(&[
            ("Idle", "Running"),
            ("Running", "Stuck"),
        ])));

        let deadlocks = check_deadlock(&sm, &terminals(&["Done"]));

        // "Stuck" is a sink (no outgoing) and not terminal
        let sinks: Vec<_> = deadlocks
            .iter()
            .filter(|d| matches!(&d.kind, DeadlockKind::Sink { .. }))
            .collect();
        assert_eq!(sinks.len(), 1);
        assert!(matches!(&sinks[0].kind, DeadlockKind::Sink { state } if state == "Stuck"));
        assert!(sinks[0].path.contains(&"Stuck".to_string()));
    }

    #[test]
    fn test_deadlock_terminal_not_flagged() {
        let mut sm = extract_from_enum_def("State", &variants(&["Idle", "Done"]));
        sm.add_transitions(extract_transitions(&arms(&[("Idle", "Done")])));

        let deadlocks = check_deadlock(&sm, &terminals(&["Done"]));

        // "Done" is terminal, should not be flagged
        let sinks: Vec<_> = deadlocks
            .iter()
            .filter(|d| matches!(&d.kind, DeadlockKind::Sink { .. }))
            .collect();
        assert!(sinks.is_empty());
    }

    // ---- trapped cycles ----

    #[test]
    fn test_deadlock_trapped_cycle() {
        let mut sm = extract_from_enum_def(
            "State",
            &variants(&["Init", "A", "B", "Done"]),
        );
        sm.add_transitions(extract_transitions(&arms(&[
            ("Init", "A"),
            ("A", "B"),
            ("B", "A"),
            // No path from A or B to Done
        ])));

        let deadlocks = check_deadlock(&sm, &terminals(&["Done"]));

        let cycles: Vec<_> = deadlocks
            .iter()
            .filter(|d| matches!(&d.kind, DeadlockKind::TrappedCycle { .. }))
            .collect();
        assert_eq!(cycles.len(), 1);
        if let DeadlockKind::TrappedCycle { cycle_states } = &cycles[0].kind {
            assert!(cycle_states.contains(&"A".to_string()));
            assert!(cycle_states.contains(&"B".to_string()));
        }
    }

    #[test]
    fn test_deadlock_cycle_with_escape_not_flagged() {
        let mut sm = extract_from_enum_def(
            "State",
            &variants(&["Init", "A", "B", "Done"]),
        );
        sm.add_transitions(extract_transitions(&arms(&[
            ("Init", "A"),
            ("A", "B"),
            ("B", "A"),
            ("B", "Done"), // Escape from cycle
        ])));

        let deadlocks = check_deadlock(&sm, &terminals(&["Done"]));

        let cycles: Vec<_> = deadlocks
            .iter()
            .filter(|d| matches!(&d.kind, DeadlockKind::TrappedCycle { .. }))
            .collect();
        assert!(cycles.is_empty(), "cycle with escape to terminal should not be flagged");
    }

    #[test]
    fn test_deadlock_self_loop_trapped() {
        let mut sm = extract_from_enum_def("State", &variants(&["Init", "Spin", "Done"]));
        sm.add_transitions(extract_transitions(&arms(&[
            ("Init", "Spin"),
            ("Spin", "Spin"), // Self-loop, no way to Done
        ])));

        let deadlocks = check_deadlock(&sm, &terminals(&["Done"]));

        let cycles: Vec<_> = deadlocks
            .iter()
            .filter(|d| matches!(&d.kind, DeadlockKind::TrappedCycle { .. }))
            .collect();
        assert_eq!(cycles.len(), 1);
        if let DeadlockKind::TrappedCycle { cycle_states } = &cycles[0].kind {
            assert!(cycle_states.contains(&"Spin".to_string()));
        }
    }

    // ---- all guards impossible ----

    #[test]
    fn test_deadlock_all_guards_impossible() {
        let mut sm = extract_from_enum_def("State", &variants(&["Idle", "A", "B"]));
        sm.add_transitions(extract_guarded_transitions(&[
            ("Idle".into(), "A".into(), Some("cond1".into())),
            ("Idle".into(), "B".into(), Some("cond2".into())),
        ]));

        let deadlocks = check_deadlock(&sm, &terminals(&["A", "B"]));

        let guarded: Vec<_> = deadlocks
            .iter()
            .filter(|d| matches!(&d.kind, DeadlockKind::AllGuardsImpossible { .. }))
            .collect();
        assert_eq!(guarded.len(), 1);
        if let DeadlockKind::AllGuardsImpossible { state, guards } = &guarded[0].kind {
            assert_eq!(state, "Idle");
            assert_eq!(guards.len(), 2);
        }
    }

    #[test]
    fn test_deadlock_mixed_guarded_unguarded_not_flagged() {
        let mut sm = extract_from_enum_def("State", &variants(&["Idle", "A", "B"]));
        sm.transitions.push(crate::extract_enum::StateTransition {
            from: "Idle".into(),
            to: "A".into(),
            guard: Some("maybe".into()),
        });
        sm.transitions.push(crate::extract_enum::StateTransition {
            from: "Idle".into(),
            to: "B".into(),
            guard: None, // Unguarded fallback
        });

        let deadlocks = check_deadlock(&sm, &terminals(&["A", "B"]));

        let guarded: Vec<_> = deadlocks
            .iter()
            .filter(|d| matches!(&d.kind, DeadlockKind::AllGuardsImpossible { .. }))
            .collect();
        assert!(guarded.is_empty(), "mixed guarded/unguarded should not be flagged");
    }

    // ---- edge cases ----

    #[test]
    fn test_deadlock_no_initial_state() {
        let mut sm = extract_from_enum_def("State", &variants(&["A", "B"]));
        sm.initial_state = None;

        let deadlocks = check_deadlock(&sm, &terminals(&["B"]));
        assert!(deadlocks.is_empty());
    }

    #[test]
    fn test_deadlock_empty_machine() {
        let sm = extract_from_enum_def("Empty", &[]);
        let deadlocks = check_deadlock(&sm, &[]);
        assert!(deadlocks.is_empty());
    }

    #[test]
    fn test_deadlock_healthy_machine_no_deadlocks() {
        let mut sm = extract_from_enum_def(
            "Connection",
            &variants(&["Connecting", "Connected", "Disconnecting", "Disconnected"]),
        );
        sm.add_transitions(extract_transitions(&arms(&[
            ("Connecting", "Connected"),
            ("Connected", "Disconnecting"),
            ("Disconnecting", "Disconnected"),
        ])));

        let deadlocks = check_deadlock(&sm, &terminals(&["Disconnected"]));

        // No trapped cycles, no impossible guards. Disconnected is terminal.
        let cycles: Vec<_> = deadlocks
            .iter()
            .filter(|d| matches!(&d.kind, DeadlockKind::TrappedCycle { .. }))
            .collect();
        assert!(cycles.is_empty());

        let guarded: Vec<_> = deadlocks
            .iter()
            .filter(|d| matches!(&d.kind, DeadlockKind::AllGuardsImpossible { .. }))
            .collect();
        assert!(guarded.is_empty());
    }

    #[test]
    fn test_deadlock_path_includes_initial() {
        let mut sm = extract_from_enum_def("State", &variants(&["Start", "Dead"]));
        sm.add_transitions(extract_transitions(&arms(&[("Start", "Dead")])));

        let deadlocks = check_deadlock(&sm, &terminals(&["Terminal"]));

        assert!(!deadlocks.is_empty());
        // Path should start from initial state
        assert_eq!(deadlocks[0].path[0], "Start");
    }

    #[test]
    fn test_deadlock_complex_protocol() {
        // Protocol with multiple paths:
        // Init -> Auth -> Ready -> Processing -> Done (happy path)
        // Init -> Auth -> Retry -> Auth (retry loop, can reach Done via Ready)
        // Init -> Auth -> Error (dead end, not terminal)
        let mut sm = extract_from_enum_def(
            "Protocol",
            &variants(&["Init", "Auth", "Ready", "Processing", "Done", "Retry", "Error"]),
        );
        sm.add_transitions(extract_transitions(&arms(&[
            ("Init", "Auth"),
            ("Auth", "Ready"),
            ("Auth", "Retry"),
            ("Auth", "Error"),
            ("Retry", "Auth"),
            ("Ready", "Processing"),
            ("Processing", "Done"),
        ])));

        let deadlocks = check_deadlock(&sm, &terminals(&["Done"]));

        // Error is a sink (non-terminal dead end)
        let sinks: Vec<_> = deadlocks
            .iter()
            .filter(|d| matches!(&d.kind, DeadlockKind::Sink { state } if state == "Error"))
            .collect();
        assert_eq!(sinks.len(), 1);

        // Retry -> Auth loop should NOT be flagged (can reach Done through Ready)
        let cycles: Vec<_> = deadlocks
            .iter()
            .filter(|d| matches!(&d.kind, DeadlockKind::TrappedCycle { .. }))
            .collect();
        assert!(cycles.is_empty());
    }
}
