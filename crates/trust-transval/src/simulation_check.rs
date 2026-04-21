// trust-transval/simulation_check.rs: Simulation relation checking (#262)
//
// Verifies that program transformations preserve observable behavior by checking
// forward simulation relations between source and target state spaces.
//
// References:
//   Milner. "An Algebraic Definition of Simulation" (1971).
//   Lynch, Vaandrager. "Forward and Backward Simulations" (1995).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

// ---------------------------------------------------------------------------
// State types
// ---------------------------------------------------------------------------

/// A program state identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct StateId(pub usize);

/// Observable action performed during a step.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Action {
    /// Internal (silent) step.
    Tau,
    /// Observable action with a label.
    Observable(String),
}

impl std::fmt::Display for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Tau => write!(f, "τ"),
            Self::Observable(s) => write!(f, "{s}"),
        }
    }
}

/// A single step in a state transition system.
#[derive(Debug, Clone)]
pub(crate) struct Step {
    pub from: StateId,
    pub action: Action,
    pub to: StateId,
}

/// A state transition system.
#[derive(Debug, Clone)]
pub(crate) struct TransitionSystem {
    pub initial: StateId,
    pub steps: Vec<Step>,
    pub states: FxHashSet<StateId>,
}

impl TransitionSystem {
    pub(crate) fn new(initial: StateId) -> Self {
        let mut states = FxHashSet::default();
        states.insert(initial);
        Self { initial, steps: Vec::new(), states }
    }

    pub(crate) fn add_step(&mut self, from: StateId, action: Action, to: StateId) {
        self.states.insert(from);
        self.states.insert(to);
        self.steps.push(Step { from, action, to });
    }

    /// Get all outgoing steps from a state.
    #[must_use]
    pub(crate) fn outgoing(&self, from: StateId) -> Vec<&Step> {
        self.steps.iter().filter(|s| s.from == from).collect()
    }
}

// ---------------------------------------------------------------------------
// Simulation relation
// ---------------------------------------------------------------------------

/// A simulation relation: maps source states to sets of target states.
#[derive(Debug, Clone, Default)]
pub(crate) struct SimulationRelation {
    /// source_state -> {target_states}
    mapping: FxHashMap<StateId, FxHashSet<StateId>>,
}

impl SimulationRelation {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Add a pair (source, target) to the relation.
    pub(crate) fn add(&mut self, source: StateId, target: StateId) {
        self.mapping.entry(source).or_default().insert(target);
    }

    /// Check if (source, target) is in the relation.
    #[must_use]
    pub(crate) fn contains(&self, source: StateId, target: StateId) -> bool {
        self.mapping.get(&source).is_some_and(|set| set.contains(&target))
    }

    /// Get all target states related to a source state.
    #[must_use]
    pub(crate) fn targets(&self, source: StateId) -> FxHashSet<StateId> {
        self.mapping.get(&source).cloned().unwrap_or_default()
    }

    /// Number of pairs in the relation.
    #[must_use]
    pub(crate) fn size(&self) -> usize {
        self.mapping.values().map(|s| s.len()).sum()
    }
}

// ---------------------------------------------------------------------------
// Simulation checker
// ---------------------------------------------------------------------------

/// Result of simulation checking.
#[derive(Debug, Clone)]
pub(crate) struct SimulationResult {
    /// Whether the simulation holds.
    pub holds: bool,
    /// Violations found (if any).
    pub violations: Vec<SimulationViolation>,
    /// Number of pairs checked.
    pub pairs_checked: usize,
}

/// A violation of the simulation relation.
#[derive(Debug, Clone)]
pub(crate) struct SimulationViolation {
    /// Source state where violation occurs.
    pub source_state: StateId,
    /// Source action that cannot be simulated.
    pub source_action: Action,
    /// Source successor state.
    pub source_successor: StateId,
    /// Target states that were checked.
    pub target_states: Vec<StateId>,
    /// Explanation of why simulation fails.
    pub reason: String,
}

/// Checks forward simulation between source and target transition systems.
pub(crate) struct SimulationChecker<'a> {
    source: &'a TransitionSystem,
    target: &'a TransitionSystem,
    relation: &'a SimulationRelation,
}

impl<'a> SimulationChecker<'a> {
    pub(crate) fn new(
        source: &'a TransitionSystem,
        target: &'a TransitionSystem,
        relation: &'a SimulationRelation,
    ) -> Self {
        Self { source, target, relation }
    }

    /// Check the forward simulation property.
    ///
    /// For every (s, t) in R and every source step s -a-> s':
    ///   there exists target step t -a-> t' such that (s', t') in R.
    pub(crate) fn check(&self) -> SimulationResult {
        let mut violations = Vec::new();
        let mut pairs_checked = 0;

        for (&source_state, target_states) in &self.relation.mapping {
            for &target_state in target_states {
                pairs_checked += 1;

                for source_step in self.source.outgoing(source_state) {
                    let target_steps = self.target.outgoing(target_state);

                    let can_simulate = match &source_step.action {
                        Action::Tau => {
                            // Tau steps: target can either match with tau or stay put
                            // (stuttering simulation)
                            self.relation.contains(source_step.to, target_state)
                                || target_steps.iter().any(|ts| {
                                    ts.action == Action::Tau
                                        && self.relation.contains(source_step.to, ts.to)
                                })
                        }
                        action => {
                            // Observable steps: target must match the action
                            target_steps.iter().any(|ts| {
                                ts.action == *action
                                    && self.relation.contains(source_step.to, ts.to)
                            })
                        }
                    };

                    if !can_simulate {
                        violations.push(SimulationViolation {
                            source_state,
                            source_action: source_step.action.clone(),
                            source_successor: source_step.to,
                            target_states: target_states.iter().copied().collect(),
                            reason: format!(
                                "no target step matching {} from target state {:?}",
                                source_step.action, target_state
                            ),
                        });
                    }
                }
            }
        }

        SimulationResult { holds: violations.is_empty(), violations, pairs_checked }
    }
}

/// Simulation witness: proof artifact showing that simulation holds.
#[derive(Debug, Clone)]
pub(crate) struct SimulationWitness {
    /// The simulation relation that was verified.
    pub relation: SimulationRelation,
    /// Number of source states.
    pub source_states: usize,
    /// Number of target states.
    pub target_states: usize,
    /// Number of pairs in the relation.
    pub relation_size: usize,
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn simple_source() -> TransitionSystem {
        let mut ts = TransitionSystem::new(StateId(0));
        ts.add_step(StateId(0), Action::Observable("read".into()), StateId(1));
        ts.add_step(StateId(1), Action::Observable("write".into()), StateId(2));
        ts
    }

    fn simple_target() -> TransitionSystem {
        let mut ts = TransitionSystem::new(StateId(10));
        ts.add_step(StateId(10), Action::Observable("read".into()), StateId(11));
        ts.add_step(StateId(11), Action::Observable("write".into()), StateId(12));
        ts
    }

    fn identity_relation() -> SimulationRelation {
        let mut r = SimulationRelation::new();
        r.add(StateId(0), StateId(10));
        r.add(StateId(1), StateId(11));
        r.add(StateId(2), StateId(12));
        r
    }

    #[test]
    fn test_simulation_holds() {
        let src = simple_source();
        let tgt = simple_target();
        let rel = identity_relation();
        let checker = SimulationChecker::new(&src, &tgt, &rel);
        let result = checker.check();
        assert!(result.holds);
        assert!(result.violations.is_empty());
        assert!(result.pairs_checked > 0);
    }

    #[test]
    fn test_simulation_violated_missing_action() {
        let src = simple_source();
        let mut tgt = TransitionSystem::new(StateId(10));
        tgt.add_step(StateId(10), Action::Observable("read".into()), StateId(11));
        // Missing the "write" step!
        let rel = identity_relation();
        let checker = SimulationChecker::new(&src, &tgt, &rel);
        let result = checker.check();
        assert!(!result.holds);
        assert!(!result.violations.is_empty());
    }

    #[test]
    fn test_simulation_violated_wrong_action() {
        let src = simple_source();
        let mut tgt = TransitionSystem::new(StateId(10));
        tgt.add_step(StateId(10), Action::Observable("read".into()), StateId(11));
        tgt.add_step(StateId(11), Action::Observable("close".into()), StateId(12)); // wrong action
        let rel = identity_relation();
        let checker = SimulationChecker::new(&src, &tgt, &rel);
        let result = checker.check();
        assert!(!result.holds);
    }

    #[test]
    fn test_tau_stuttering() {
        let mut src = TransitionSystem::new(StateId(0));
        src.add_step(StateId(0), Action::Tau, StateId(1));
        src.add_step(StateId(1), Action::Observable("done".into()), StateId(2));

        let mut tgt = TransitionSystem::new(StateId(10));
        tgt.add_step(StateId(10), Action::Observable("done".into()), StateId(11));

        let mut rel = SimulationRelation::new();
        rel.add(StateId(0), StateId(10));
        rel.add(StateId(1), StateId(10)); // tau stutter: s1 maps to same target
        rel.add(StateId(2), StateId(11));

        let checker = SimulationChecker::new(&src, &tgt, &rel);
        let result = checker.check();
        assert!(result.holds);
    }

    #[test]
    fn test_simulation_relation_basic() {
        let mut rel = SimulationRelation::new();
        rel.add(StateId(0), StateId(10));
        rel.add(StateId(0), StateId(11));
        assert!(rel.contains(StateId(0), StateId(10)));
        assert!(rel.contains(StateId(0), StateId(11)));
        assert!(!rel.contains(StateId(0), StateId(12)));
        assert_eq!(rel.size(), 2);
    }

    #[test]
    fn test_simulation_relation_targets() {
        let mut rel = SimulationRelation::new();
        rel.add(StateId(0), StateId(10));
        rel.add(StateId(0), StateId(11));
        let targets = rel.targets(StateId(0));
        assert_eq!(targets.len(), 2);
        assert!(targets.contains(&StateId(10)));
    }

    #[test]
    fn test_empty_relation() {
        let rel = SimulationRelation::new();
        assert_eq!(rel.size(), 0);
        assert!(rel.targets(StateId(0)).is_empty());
    }

    #[test]
    fn test_transition_system_outgoing() {
        let src = simple_source();
        assert_eq!(src.outgoing(StateId(0)).len(), 1);
        assert_eq!(src.outgoing(StateId(2)).len(), 0);
    }

    #[test]
    fn test_action_display() {
        assert_eq!(Action::Tau.to_string(), "τ");
        assert_eq!(Action::Observable("read".into()).to_string(), "read");
    }

    #[test]
    fn test_empty_systems_trivially_simulate() {
        let src = TransitionSystem::new(StateId(0));
        let tgt = TransitionSystem::new(StateId(10));
        let mut rel = SimulationRelation::new();
        rel.add(StateId(0), StateId(10));
        let checker = SimulationChecker::new(&src, &tgt, &rel);
        let result = checker.check();
        assert!(result.holds);
    }

    #[test]
    fn test_simulation_witness() {
        let rel = identity_relation();
        let witness = SimulationWitness {
            relation: rel.clone(),
            source_states: 3,
            target_states: 3,
            relation_size: rel.size(),
        };
        assert_eq!(witness.relation_size, 3);
    }

    #[test]
    fn test_pairs_checked_count() {
        let src = simple_source();
        let tgt = simple_target();
        let rel = identity_relation();
        let checker = SimulationChecker::new(&src, &tgt, &rel);
        let result = checker.check();
        assert_eq!(result.pairs_checked, 3); // 3 pairs in relation
    }
}
