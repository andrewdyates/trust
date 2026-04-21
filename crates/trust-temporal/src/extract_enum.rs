// trust-temporal/extract_enum.rs: Automatic state machine extraction from Rust enum definitions
//
// Extracts state machines from enum variant lists and match arm transition
// patterns. Detects dead states (no outgoing transitions) and unreachable
// states (no path from initial state). Generates TLA+ modules for model
// checking.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};
use std::fmt::Write;

use trust_types::VerifiableBody;

use crate::extract::extract_state_machines;

// tRust #683: Automatic state machine discovery from MIR (zero annotations).

/// Extract all enum-based state machines from a MIR function body.
///
/// This is the primary entry point for automatic state machine discovery.
/// Requires zero annotations -- detection is purely from MIR patterns:
/// - `Rvalue::Discriminant` reads identify enum locals
/// - `Terminator::SwitchInt` on discriminant values identifies match arms
/// - `Rvalue::Aggregate(Adt { .. })` assignments identify state transitions
///
/// Returns one `EnumStateMachine` per discovered enum state machine.
#[must_use]
pub(crate) fn extract_state_machine(body: &VerifiableBody) -> Vec<EnumStateMachine> {
    let machines = extract_state_machines(body);

    machines
        .into_iter()
        .map(|sm| {
            // Build name-to-variant map from the StateMachine states.
            // State names from extract.rs have format "EnumName::variant_N".
            let enum_name = sm
                .states
                .first()
                .and_then(|s| s.name.split("::").next())
                .unwrap_or("Unknown")
                .to_string();

            let states: Vec<String> = sm.states.iter().map(|s| s.name.clone()).collect();

            let transitions: Vec<StateTransition> = sm
                .transitions
                .iter()
                .map(|t| {
                    let from_name = sm
                        .state(t.from)
                        .map_or_else(|| format!("state_{}", t.from.0), |s| s.name.clone());
                    let to_name = sm
                        .state(t.to)
                        .map_or_else(|| format!("state_{}", t.to.0), |s| s.name.clone());
                    StateTransition {
                        from: from_name,
                        to: to_name,
                        guard: t.guard.clone(),
                    }
                })
                .collect();

            let initial_state = if states.is_empty() { None } else { Some(sm.initial.0) };

            EnumStateMachine {
                enum_name,
                states,
                transitions,
                initial_state,
            }
        })
        .collect()
}

/// A state machine extracted from an enum definition and its match arms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EnumStateMachine {
    /// Name of the enum type.
    pub enum_name: String,
    /// Variant names (states).
    pub states: Vec<String>,
    /// Transitions discovered from match arms.
    pub transitions: Vec<StateTransition>,
    /// Index into `states` of the initial state, if known.
    pub initial_state: Option<usize>,
}

/// A transition between two enum variants.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StateTransition {
    /// Source state name.
    pub from: String,
    /// Target state name.
    pub to: String,
    /// Optional guard condition.
    pub guard: Option<String>,
}

/// A state with no outgoing transitions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeadState {
    /// Name of the dead state.
    pub state: String,
}

/// A state unreachable from the initial state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UnreachableState {
    /// Name of the unreachable state.
    pub state: String,
}

/// Extract an `EnumStateMachine` from an enum definition.
///
/// `enum_name` is the type name. `variants` are the variant names.
/// The first variant is assumed to be the initial state.
#[must_use]
pub(crate) fn extract_from_enum_def(enum_name: &str, variants: &[String]) -> EnumStateMachine {
    let initial_state = if variants.is_empty() { None } else { Some(0) };

    EnumStateMachine {
        enum_name: enum_name.to_string(),
        states: variants.to_vec(),
        transitions: Vec::new(),
        initial_state,
    }
}

/// Extract transitions from match arm pairs `(from_variant, to_variant)`.
///
/// Each pair represents a match arm that transitions from one enum variant
/// to another (e.g., `State::Idle => state = State::Running`).
#[must_use]
pub(crate) fn extract_transitions(match_arms: &[(String, String)]) -> Vec<StateTransition> {
    match_arms
        .iter()
        .map(|(from, to)| StateTransition {
            from: from.clone(),
            to: to.clone(),
            guard: None,
        })
        .collect()
}

/// Extract transitions from match arm triples `(from_variant, to_variant, guard)`.
#[must_use]
pub(crate) fn extract_guarded_transitions(
    match_arms: &[(String, String, Option<String>)],
) -> Vec<StateTransition> {
    match_arms
        .iter()
        .map(|(from, to, guard)| StateTransition {
            from: from.clone(),
            to: to.clone(),
            guard: guard.clone(),
        })
        .collect()
}

impl EnumStateMachine {
    /// Add transitions to this state machine.
    pub(crate) fn add_transitions(&mut self, transitions: Vec<StateTransition>) {
        self.transitions.extend(transitions);
    }

    /// Detect dead states: states with no outgoing transitions.
    ///
    /// A dead state is a state that appears in `self.states` but has no
    /// transition where it is the `from` state.
    #[must_use]
    pub(crate) fn dead_states(&self) -> Vec<DeadState> {
        let has_outgoing: FxHashSet<&str> = self
            .transitions
            .iter()
            .map(|t| t.from.as_str())
            .collect();

        self.states
            .iter()
            .filter(|state| !has_outgoing.contains(state.as_str()))
            .map(|state| DeadState { state: state.clone() })
            .collect()
    }

    /// Detect unreachable states: states with no path from the initial state.
    ///
    /// Uses BFS from the initial state over the transition graph. States not
    /// visited are unreachable. Returns empty if no initial state is set.
    #[must_use]
    pub(crate) fn unreachable_states(&self) -> Vec<UnreachableState> {
        let Some(initial_idx) = self.initial_state else {
            return Vec::new();
        };
        let Some(initial_name) = self.states.get(initial_idx) else {
            return Vec::new();
        };

        // Build adjacency list: from -> [to]
        let mut adj: FxHashMap<&str, Vec<&str>> = FxHashMap::default();
        for t in &self.transitions {
            adj.entry(t.from.as_str()).or_default().push(t.to.as_str());
        }

        // BFS from initial
        let mut visited = FxHashSet::default();
        let mut queue = VecDeque::new();
        visited.insert(initial_name.as_str());
        queue.push_back(initial_name.as_str());

        while let Some(current) = queue.pop_front() {
            if let Some(neighbors) = adj.get(current) {
                for &next in neighbors {
                    if visited.insert(next) {
                        queue.push_back(next);
                    }
                }
            }
        }

        self.states
            .iter()
            .filter(|state| !visited.contains(state.as_str()))
            .map(|state| UnreachableState { state: state.clone() })
            .collect()
    }

    /// Generate a TLA+ module representing this state machine.
    ///
    /// The output is a self-contained TLA+ specification with:
    /// - A `State` set of all variant names
    /// - An `Init` predicate setting the initial state
    /// - A `Next` predicate with disjunction over all transitions
    /// - Type invariant and temporal properties
    #[must_use]
    pub(crate) fn to_tla_module(&self) -> String {
        let mut out = String::new();
        let module_name = &self.enum_name;

        // Module header
        let _ = writeln!(out, "---- MODULE {module_name} ----");
        out.push_str("EXTENDS Naturals\n\n");

        // Variables
        out.push_str("VARIABLE state\n\n");

        // State set
        out.push_str("States == {");
        let quoted: Vec<String> = self.states.iter().map(|s| format!("\"{s}\"")).collect();
        out.push_str(&quoted.join(", "));
        out.push_str("}\n\n");

        // Type invariant
        out.push_str("TypeInvariant == state \\in States\n\n");

        // Init
        if let Some(idx) = self.initial_state {
            if let Some(name) = self.states.get(idx) {
                let _ = write!(out, "Init == state = \"{name}\"\n\n");
            } else {
                out.push_str("Init == state \\in States\n\n");
            }
        } else {
            out.push_str("Init == state \\in States\n\n");
        }

        // Next: one action per transition
        if self.transitions.is_empty() {
            out.push_str("Next == UNCHANGED state\n\n");
        } else {
            let mut actions = Vec::new();
            for (i, t) in self.transitions.iter().enumerate() {
                let action_name = format!("Trans_{i}");
                let guard_clause = if let Some(guard) = &t.guard {
                    format!(" /\\ {guard}")
                } else {
                    String::new()
                };
                let action = format!(
                    "{action_name} == state = \"{}\" /\\ state' = \"{}\"{}",
                    t.from, t.to, guard_clause
                );
                out.push_str(&action);
                out.push('\n');
                actions.push(action_name);
            }
            out.push('\n');
            out.push_str("Next == ");
            out.push_str(&actions.join(" \\/ "));
            out.push_str("\n\n");
        }

        // Spec
        out.push_str("Spec == Init /\\ [][Next]_state\n\n");

        // Footer
        out.push_str("====\n");
        out
    }

    /// Convert this enum-based state machine into the crate's `StateMachine` type.
    ///
    /// Maps variant names to `StateId` based on their position in `self.states`.
    #[must_use]
    pub(crate) fn to_state_machine(&self) -> crate::StateMachine {
        let initial = crate::StateId(self.initial_state.unwrap_or(0));
        let mut builder = crate::StateMachineBuilder::new(initial);

        // Build name-to-index map
        let name_to_idx: FxHashMap<&str, usize> = self
            .states
            .iter()
            .enumerate()
            .map(|(i, name)| (name.as_str(), i))
            .collect();

        for (i, name) in self.states.iter().enumerate() {
            builder.push_state(crate::State::new(crate::StateId(i), name));
        }

        for t in &self.transitions {
            if let (Some(&from_idx), Some(&to_idx)) =
                (name_to_idx.get(t.from.as_str()), name_to_idx.get(t.to.as_str()))
            {
                let mut transition = crate::Transition::new(
                    crate::StateId(from_idx),
                    crate::StateId(to_idx),
                    format!("{}_to_{}", t.from, t.to),
                );
                if let Some(guard) = &t.guard {
                    transition = transition.with_guard(guard);
                }
                builder.push_transition(transition);
            }
        }

        builder.build()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn variants(names: &[&str]) -> Vec<String> {
        names.iter().map(|s| s.to_string()).collect()
    }

    fn arms(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
        pairs.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect()
    }

    // ---- extract_from_enum_def ----

    #[test]
    fn test_extract_from_enum_def_basic() {
        let sm = extract_from_enum_def("State", &variants(&["Idle", "Running", "Done"]));
        assert_eq!(sm.enum_name, "State");
        assert_eq!(sm.states.len(), 3);
        assert_eq!(sm.initial_state, Some(0));
        assert!(sm.transitions.is_empty());
    }

    #[test]
    fn test_extract_from_enum_def_empty() {
        let sm = extract_from_enum_def("Empty", &[]);
        assert!(sm.states.is_empty());
        assert_eq!(sm.initial_state, None);
    }

    #[test]
    fn test_extract_from_enum_def_single_variant() {
        let sm = extract_from_enum_def("Unit", &variants(&["Only"]));
        assert_eq!(sm.states.len(), 1);
        assert_eq!(sm.initial_state, Some(0));
    }

    // ---- extract_transitions ----

    #[test]
    fn test_extract_transitions_basic() {
        let transitions = extract_transitions(&arms(&[
            ("Idle", "Running"),
            ("Running", "Done"),
        ]));
        assert_eq!(transitions.len(), 2);
        assert_eq!(transitions[0].from, "Idle");
        assert_eq!(transitions[0].to, "Running");
        assert!(transitions[0].guard.is_none());
    }

    #[test]
    fn test_extract_transitions_empty() {
        let transitions = extract_transitions(&[]);
        assert!(transitions.is_empty());
    }

    #[test]
    fn test_extract_guarded_transitions() {
        let transitions = extract_guarded_transitions(&[
            ("Idle".into(), "Running".into(), Some("ready".into())),
            ("Running".into(), "Done".into(), None),
        ]);
        assert_eq!(transitions.len(), 2);
        assert_eq!(transitions[0].guard, Some("ready".into()));
        assert_eq!(transitions[1].guard, None);
    }

    // ---- dead_states ----

    #[test]
    fn test_dead_states_terminal_state_is_dead() {
        let mut sm = extract_from_enum_def("State", &variants(&["Idle", "Running", "Done"]));
        sm.add_transitions(extract_transitions(&arms(&[
            ("Idle", "Running"),
            ("Running", "Done"),
        ])));

        let dead = sm.dead_states();
        assert_eq!(dead.len(), 1);
        assert_eq!(dead[0].state, "Done");
    }

    #[test]
    fn test_dead_states_no_dead_in_cycle() {
        let mut sm = extract_from_enum_def("Mode", &variants(&["A", "B"]));
        sm.add_transitions(extract_transitions(&arms(&[("A", "B"), ("B", "A")])));

        let dead = sm.dead_states();
        assert!(dead.is_empty());
    }

    #[test]
    fn test_dead_states_all_dead_when_no_transitions() {
        let sm = extract_from_enum_def("State", &variants(&["X", "Y", "Z"]));
        let dead = sm.dead_states();
        assert_eq!(dead.len(), 3);
    }

    #[test]
    fn test_dead_states_self_loop_not_dead() {
        let mut sm = extract_from_enum_def("Loop", &variants(&["Spin"]));
        sm.add_transitions(extract_transitions(&arms(&[("Spin", "Spin")])));

        let dead = sm.dead_states();
        assert!(dead.is_empty());
    }

    // ---- unreachable_states ----

    #[test]
    fn test_unreachable_states_isolated_state() {
        let mut sm = extract_from_enum_def("State", &variants(&["Idle", "Running", "Orphan"]));
        sm.add_transitions(extract_transitions(&arms(&[
            ("Idle", "Running"),
            ("Running", "Idle"),
        ])));

        let unreachable = sm.unreachable_states();
        assert_eq!(unreachable.len(), 1);
        assert_eq!(unreachable[0].state, "Orphan");
    }

    #[test]
    fn test_unreachable_states_all_reachable() {
        let mut sm = extract_from_enum_def("State", &variants(&["A", "B", "C"]));
        sm.add_transitions(extract_transitions(&arms(&[
            ("A", "B"),
            ("B", "C"),
        ])));

        let unreachable = sm.unreachable_states();
        assert!(unreachable.is_empty());
    }

    #[test]
    fn test_unreachable_states_no_initial() {
        let mut sm = extract_from_enum_def("State", &variants(&["A", "B"]));
        sm.initial_state = None;
        sm.add_transitions(extract_transitions(&arms(&[("A", "B")])));

        // No initial state => no unreachable detection
        let unreachable = sm.unreachable_states();
        assert!(unreachable.is_empty());
    }

    #[test]
    fn test_unreachable_states_transitive_reachability() {
        let mut sm = extract_from_enum_def("Chain", &variants(&["A", "B", "C", "D"]));
        sm.add_transitions(extract_transitions(&arms(&[
            ("A", "B"),
            ("B", "C"),
            ("C", "D"),
        ])));

        let unreachable = sm.unreachable_states();
        assert!(unreachable.is_empty());
    }

    #[test]
    fn test_unreachable_states_multiple_unreachable() {
        let sm = extract_from_enum_def("State", &variants(&["Start", "Orphan1", "Orphan2"]));
        // No transitions at all -- Start is reachable (it's initial), others are not.

        let unreachable = sm.unreachable_states();
        assert_eq!(unreachable.len(), 2);
        let names: Vec<&str> = unreachable.iter().map(|u| u.state.as_str()).collect();
        assert!(names.contains(&"Orphan1"));
        assert!(names.contains(&"Orphan2"));
    }

    // ---- TLA+ generation ----

    #[test]
    fn test_tla_module_structure() {
        let mut sm = extract_from_enum_def("TrafficLight", &variants(&["Red", "Green", "Yellow"]));
        sm.add_transitions(extract_transitions(&arms(&[
            ("Red", "Green"),
            ("Green", "Yellow"),
            ("Yellow", "Red"),
        ])));

        let tla = sm.to_tla_module();

        assert!(tla.contains("---- MODULE TrafficLight ----"));
        assert!(tla.contains("VARIABLE state"));
        assert!(tla.contains("States == {\"Red\", \"Green\", \"Yellow\"}"));
        assert!(tla.contains("Init == state = \"Red\""));
        assert!(tla.contains("state = \"Red\" /\\ state' = \"Green\""));
        assert!(tla.contains("state = \"Green\" /\\ state' = \"Yellow\""));
        assert!(tla.contains("state = \"Yellow\" /\\ state' = \"Red\""));
        assert!(tla.contains("Spec == Init /\\ [][Next]_state"));
        assert!(tla.contains("===="));
    }

    #[test]
    fn test_tla_module_no_transitions() {
        let sm = extract_from_enum_def("Frozen", &variants(&["Only"]));
        let tla = sm.to_tla_module();

        assert!(tla.contains("Next == UNCHANGED state"));
    }

    #[test]
    fn test_tla_module_with_guards() {
        let mut sm = extract_from_enum_def("Guarded", &variants(&["A", "B"]));
        sm.add_transitions(extract_guarded_transitions(&[
            ("A".into(), "B".into(), Some("condition_met".into())),
        ]));

        let tla = sm.to_tla_module();
        assert!(tla.contains("condition_met"));
    }

    #[test]
    fn test_tla_module_no_initial_state() {
        let mut sm = extract_from_enum_def("NoInit", &variants(&["X", "Y"]));
        sm.initial_state = None;

        let tla = sm.to_tla_module();
        assert!(tla.contains("Init == state \\in States"));
    }

    // ---- to_state_machine ----

    #[test]
    fn test_to_state_machine_conversion() {
        let mut sm = extract_from_enum_def("Proto", &variants(&["Idle", "Active", "Done"]));
        sm.add_transitions(extract_transitions(&arms(&[
            ("Idle", "Active"),
            ("Active", "Done"),
        ])));

        let machine = sm.to_state_machine();
        assert_eq!(machine.states.len(), 3);
        assert_eq!(machine.transitions.len(), 2);
        assert_eq!(machine.initial, crate::StateId(0));

        // Verify state names
        assert_eq!(machine.state(crate::StateId(0)).unwrap().name, "Idle");
        assert_eq!(machine.state(crate::StateId(1)).unwrap().name, "Active");
        assert_eq!(machine.state(crate::StateId(2)).unwrap().name, "Done");

        // Verify transitions
        assert!(machine.transitions.iter().any(|t| t.from == crate::StateId(0)
            && t.to == crate::StateId(1)));
        assert!(machine.transitions.iter().any(|t| t.from == crate::StateId(1)
            && t.to == crate::StateId(2)));
    }

    #[test]
    fn test_to_state_machine_with_guard() {
        let mut sm = extract_from_enum_def("G", &variants(&["A", "B"]));
        sm.add_transitions(extract_guarded_transitions(&[
            ("A".into(), "B".into(), Some("ready".into())),
        ]));

        let machine = sm.to_state_machine();
        assert_eq!(machine.transitions.len(), 1);
        assert_eq!(machine.transitions[0].guard, Some("ready".into()));
    }

    // ---- integration: dead + unreachable detection ----

    #[test]
    fn test_combined_analysis_protocol_state_machine() {
        // Realistic protocol: Init -> Handshake -> Established -> Closing -> Closed
        // Plus an orphan Error state with no incoming transitions
        let mut sm = extract_from_enum_def(
            "Protocol",
            &variants(&["Init", "Handshake", "Established", "Closing", "Closed", "Error"]),
        );
        sm.add_transitions(extract_transitions(&arms(&[
            ("Init", "Handshake"),
            ("Handshake", "Established"),
            ("Established", "Closing"),
            ("Closing", "Closed"),
        ])));

        // Dead states: Closed (no outgoing) and Error (no outgoing)
        let dead = sm.dead_states();
        assert_eq!(dead.len(), 2);
        let dead_names: Vec<&str> = dead.iter().map(|d| d.state.as_str()).collect();
        assert!(dead_names.contains(&"Closed"));
        assert!(dead_names.contains(&"Error"));

        // Unreachable: Error (no incoming from reachable states)
        let unreachable = sm.unreachable_states();
        assert_eq!(unreachable.len(), 1);
        assert_eq!(unreachable[0].state, "Error");
    }

    // ---- extract_state_machine from MIR ----

    use trust_types::*;

    fn mir_enum_ty(name: &str) -> Ty {
        Ty::Adt { name: name.to_string(), fields: vec![] }
    }

    fn mir_assign(place: Place, rvalue: Rvalue) -> Statement {
        Statement::Assign { place, rvalue, span: SourceSpan::default() }
    }

    fn mir_discr_stmt(discr_local: usize, enum_local: usize) -> Statement {
        mir_assign(Place::local(discr_local), Rvalue::Discriminant(Place::local(enum_local)))
    }

    fn mir_variant_stmt(enum_local: usize, enum_name: &str, variant: usize) -> Statement {
        mir_assign(
            Place::local(enum_local),
            Rvalue::Aggregate(AggregateKind::Adt { name: enum_name.to_string(), variant }, vec![]),
        )
    }

    fn mir_block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts, terminator }
    }

    fn mir_switch(discr_local: usize, targets: &[(u128, usize)], otherwise: usize) -> Terminator {
        Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(discr_local)),
            targets: targets.iter().map(|(value, block)| (*value, BlockId(*block))).collect(),
            otherwise: BlockId(otherwise),
            span: SourceSpan::default(),
        }
    }

    fn mir_body(locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>) -> VerifiableBody {
        VerifiableBody { locals, blocks, arg_count: 0, return_ty: Ty::Unit }
    }

    #[test]
    fn test_extract_state_machine_from_mir_linear() {
        // A(0) -> B(1) -> C(2), C is dead
        let body = mir_body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: mir_enum_ty("State"), name: Some("state".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                mir_block(0, vec![mir_discr_stmt(2, 1)], mir_switch(2, &[(0, 1), (1, 2)], 3)),
                mir_block(1, vec![mir_variant_stmt(1, "State", 1)], Terminator::Return),
                mir_block(2, vec![mir_variant_stmt(1, "State", 2)], Terminator::Return),
                mir_block(3, vec![], Terminator::Return),
            ],
        );

        let machines = extract_state_machine(&body);
        assert_eq!(machines.len(), 1);

        let sm = &machines[0];
        assert_eq!(sm.enum_name, "State");
        assert!(!sm.states.is_empty());
        assert!(!sm.transitions.is_empty());

        // State 2 (variant_2) should be dead (no outgoing transitions)
        let dead = sm.dead_states();
        assert!(!dead.is_empty(), "terminal state should be dead");
    }

    #[test]
    fn test_extract_state_machine_from_mir_cycle() {
        // A(0) <-> B(1): fully connected cycle, no dead states
        let body = mir_body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: mir_enum_ty("Mode"), name: Some("mode".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                mir_block(0, vec![mir_discr_stmt(2, 1)], mir_switch(2, &[(0, 1), (1, 2)], 3)),
                mir_block(1, vec![mir_variant_stmt(1, "Mode", 1)], Terminator::Return),
                mir_block(2, vec![mir_variant_stmt(1, "Mode", 0)], Terminator::Return),
                mir_block(3, vec![], Terminator::Return),
            ],
        );

        let machines = extract_state_machine(&body);
        assert_eq!(machines.len(), 1);

        let sm = &machines[0];
        assert_eq!(sm.enum_name, "Mode");
        let dead = sm.dead_states();
        assert!(dead.is_empty(), "cycle has no dead states");
    }

    #[test]
    fn test_extract_state_machine_from_mir_empty() {
        let body = mir_body(
            vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            vec![mir_block(0, vec![], Terminator::Return)],
        );

        let machines = extract_state_machine(&body);
        assert!(machines.is_empty());
    }

    #[test]
    fn test_extract_state_machine_from_mir_tla_generation() {
        let body = mir_body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: mir_enum_ty("Traffic"), name: Some("t".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("d".into()) },
            ],
            vec![
                mir_block(
                    0,
                    vec![mir_discr_stmt(2, 1)],
                    mir_switch(2, &[(0, 1), (1, 2), (2, 3)], 4),
                ),
                mir_block(1, vec![mir_variant_stmt(1, "Traffic", 1)], Terminator::Return),
                mir_block(2, vec![mir_variant_stmt(1, "Traffic", 2)], Terminator::Return),
                mir_block(3, vec![mir_variant_stmt(1, "Traffic", 0)], Terminator::Return),
                mir_block(4, vec![], Terminator::Return),
            ],
        );

        let machines = extract_state_machine(&body);
        assert_eq!(machines.len(), 1);

        let sm = &machines[0];
        let tla = sm.to_tla_module();
        assert!(tla.contains(&format!("---- MODULE {} ----", sm.enum_name)));
        assert!(tla.contains("VARIABLE state"));
        assert!(tla.contains("Spec =="));
        assert!(tla.contains("===="));
    }

    #[test]
    fn test_extract_state_machine_from_mir_to_temporal() {
        // Verify the round-trip: MIR -> EnumStateMachine -> StateMachine
        let body = mir_body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: mir_enum_ty("Proto"), name: Some("p".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("d".into()) },
            ],
            vec![
                mir_block(0, vec![mir_discr_stmt(2, 1)], mir_switch(2, &[(0, 1), (1, 2)], 3)),
                mir_block(1, vec![mir_variant_stmt(1, "Proto", 1)], Terminator::Return),
                mir_block(2, vec![mir_variant_stmt(1, "Proto", 0)], Terminator::Return),
                mir_block(3, vec![], Terminator::Return),
            ],
        );

        let machines = extract_state_machine(&body);
        let sm = &machines[0];

        // Convert to temporal StateMachine
        let temporal_sm = sm.to_state_machine();
        assert_eq!(temporal_sm.states.len(), sm.states.len());
        assert_eq!(temporal_sm.transitions.len(), sm.transitions.len());

        // Verify deadlock freedom via tla2_bridge
        let is_free = crate::tla2_bridge::check_deadlock_freedom(&temporal_sm);
        assert!(is_free, "cycle should be deadlock-free");
    }
}
