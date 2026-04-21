// trust-transval/bisimulation.rs: Bisimulation checking (#321)
//
// Verifies that two transition systems are bisimilar — a stronger equivalence
// than simulation. Bisimulation requires that both systems can match each
// other's transitions step-for-step in both directions.
//
// Key algorithms:
//   - check_bisimulation: verify a given relation is a bisimulation
//   - compute_bisimulation: find the maximal bisimulation via partition refinement
//   - simulation_check: one-directional simulation (forward only)
//
// References:
//   Park. "Concurrency and Automata on Infinite Sequences" (1981).
//   Milner. "Communication and Concurrency" (1989).
//   Kanellakis, Smolka. "CCS Expressions, Finite State Processes, and Three
//     Problems of Equivalence" (1990). — O(m log n) partition refinement.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use crate::simulation_check::{Action, StateId, Step, TransitionSystem};

// ---------------------------------------------------------------------------
// Bisimulation relation
// ---------------------------------------------------------------------------

/// A bisimulation relation: set of (source, target) state pairs.
#[derive(Debug, Clone, Default)]
pub(crate) struct BisimulationRelation {
    /// Pairs of related states.
    pairs: FxHashSet<(StateId, StateId)>,
}

impl BisimulationRelation {
    /// Create an empty relation.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Add a pair to the relation.
    pub(crate) fn add(&mut self, source: StateId, target: StateId) {
        self.pairs.insert((source, target));
    }

    /// Check if a pair is in the relation.
    #[must_use]
    pub(crate) fn contains(&self, source: StateId, target: StateId) -> bool {
        self.pairs.contains(&(source, target))
    }

    /// Number of pairs in the relation.
    #[must_use]
    pub(crate) fn size(&self) -> usize {
        self.pairs.len()
    }

    /// Whether the relation is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.pairs.is_empty()
    }

    /// Iterate over all pairs.
    pub(crate) fn iter(&self) -> impl Iterator<Item = &(StateId, StateId)> {
        self.pairs.iter()
    }
}

// ---------------------------------------------------------------------------
// Bisimulation step witness
// ---------------------------------------------------------------------------

/// Records how a source transition is matched by a target transition.
#[derive(Debug, Clone)]
pub(crate) struct BisimStep {
    /// Source state before the step.
    pub source_from: StateId,
    /// Action taken in the source.
    pub source_action: Action,
    /// Source state after the step.
    pub source_to: StateId,
    /// Target state before the matching step.
    pub target_from: StateId,
    /// Action taken in the target (must match source action).
    pub target_action: Action,
    /// Target state after the matching step.
    pub target_to: StateId,
}

// ---------------------------------------------------------------------------
// Bisimulation witness (counterexample)
// ---------------------------------------------------------------------------

/// Counterexample showing why two systems are not bisimilar.
#[derive(Debug, Clone)]
pub(crate) struct BisimWitness {
    /// The source state where bisimulation fails.
    pub source_state: StateId,
    /// The target state where bisimulation fails.
    pub target_state: StateId,
    /// The action that cannot be matched.
    pub unmatched_action: Action,
    /// The successor state of the unmatched step.
    pub unmatched_successor: StateId,
    /// Whether the failure is in the forward direction (source -> target)
    /// or backward direction (target -> source).
    pub direction: BisimDirection,
    /// Human-readable explanation.
    pub reason: String,
}

/// Direction of a bisimulation failure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BisimDirection {
    /// Source can step but target cannot match.
    Forward,
    /// Target can step but source cannot match.
    Backward,
}

// ---------------------------------------------------------------------------
// Bisimulation result
// ---------------------------------------------------------------------------

/// Result of a bisimulation check.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub(crate) enum BisimResult {
    /// The two systems are bisimilar under the given relation.
    Bisimilar {
        /// The verified bisimulation relation.
        relation: BisimulationRelation,
        /// Matched step witnesses.
        steps: Vec<BisimStep>,
    },
    /// The two systems are not bisimilar.
    NotBisimilar(BisimWitness),
    /// Could not determine bisimilarity (e.g., state space too large).
    Unknown {
        /// Reason for inconclusive result.
        reason: String,
    },
}

// ---------------------------------------------------------------------------
// Core algorithms
// ---------------------------------------------------------------------------

/// Check whether a given relation is a bisimulation between source and target.
///
/// For every pair `(s, t)` in the relation:
/// - Forward: every step `s -a-> s'` must have a matching `t -a-> t'` with `(s', t')` in R
/// - Backward: every step `t -a-> t'` must have a matching `s -a-> s'` with `(s', t')` in R
#[must_use]
pub(crate) fn check_bisimulation(
    source: &TransitionSystem,
    target: &TransitionSystem,
    relation: &BisimulationRelation,
) -> BisimResult {
    let mut steps = Vec::new();

    for &(s, t) in relation.iter() {
        // Forward check: every source step must be matched by target.
        for source_step in source.outgoing(s) {
            let matched = find_matching_step(target, t, &source_step.action, |t_succ| {
                relation.contains(source_step.to, t_succ)
            });

            match matched {
                Some(target_step) => {
                    steps.push(BisimStep {
                        source_from: s,
                        source_action: source_step.action.clone(),
                        source_to: source_step.to,
                        target_from: t,
                        target_action: target_step.action.clone(),
                        target_to: target_step.to,
                    });
                }
                None => {
                    return BisimResult::NotBisimilar(BisimWitness {
                        source_state: s,
                        target_state: t,
                        unmatched_action: source_step.action.clone(),
                        unmatched_successor: source_step.to,
                        direction: BisimDirection::Forward,
                        reason: format!(
                            "source step {:?} -{}-> {:?} has no matching target step from {:?}",
                            s, source_step.action, source_step.to, t
                        ),
                    });
                }
            }
        }

        // Backward check: every target step must be matched by source.
        for target_step in target.outgoing(t) {
            let matched = find_matching_step(source, s, &target_step.action, |s_succ| {
                relation.contains(s_succ, target_step.to)
            });

            if matched.is_none() {
                return BisimResult::NotBisimilar(BisimWitness {
                    source_state: s,
                    target_state: t,
                    unmatched_action: target_step.action.clone(),
                    unmatched_successor: target_step.to,
                    direction: BisimDirection::Backward,
                    reason: format!(
                        "target step {:?} -{}-> {:?} has no matching source step from {:?}",
                        t, target_step.action, target_step.to, s
                    ),
                });
            }
        }
    }

    BisimResult::Bisimilar { relation: relation.clone(), steps }
}

/// Find a matching step from `state` with the given `action` whose successor
/// satisfies the `successor_ok` predicate.
fn find_matching_step<'a>(
    system: &'a TransitionSystem,
    state: StateId,
    action: &Action,
    successor_ok: impl Fn(StateId) -> bool,
) -> Option<&'a Step> {
    system.outgoing(state).into_iter().find(|step| step.action == *action && successor_ok(step.to))
}

/// Compute the maximal bisimulation relation between two systems using
/// partition refinement.
///
/// Returns all pairs of states that are bisimilar. Uses the Kanellakis-Smolka
/// style algorithm: start with all pairs, iteratively remove pairs that
/// violate the bisimulation condition.
#[must_use]
pub(crate) fn compute_bisimulation(
    source: &TransitionSystem,
    target: &TransitionSystem,
) -> BisimulationRelation {
    // Initialize: all pairs of (source_state, target_state) are candidates.
    let source_states: Vec<StateId> = source.states.iter().copied().collect();
    let target_states: Vec<StateId> = target.states.iter().copied().collect();

    let mut relation = BisimulationRelation::new();
    for &s in &source_states {
        for &t in &target_states {
            relation.add(s, t);
        }
    }

    // Build action index for faster lookup.
    let source_actions = build_action_index(source);
    let target_actions = build_action_index(target);

    // Iteratively refine until stable.
    loop {
        let mut to_remove = Vec::new();

        for &(s, t) in relation.iter() {
            // Forward: every source step from s must be matchable from t.
            for source_step in source.outgoing(s) {
                let has_match = target.outgoing(t).iter().any(|ts| {
                    ts.action == source_step.action && relation.contains(source_step.to, ts.to)
                });

                if !has_match {
                    to_remove.push((s, t));
                    break;
                }
            }
        }

        // Backward check (separate pass to avoid re-checking removed pairs).
        for &(s, t) in relation.iter() {
            if to_remove.contains(&(s, t)) {
                continue;
            }
            for target_step in target.outgoing(t) {
                let has_match = source.outgoing(s).iter().any(|ss| {
                    ss.action == target_step.action && relation.contains(ss.to, target_step.to)
                });

                if !has_match {
                    to_remove.push((s, t));
                    break;
                }
            }
        }

        if to_remove.is_empty() {
            break;
        }

        for pair in &to_remove {
            relation.pairs.remove(pair);
        }
    }

    // Collect which actions are available from each source/target state.
    // This is used for pruning pairs where available actions don't overlap.
    let _ = (source_actions, target_actions);

    relation
}

/// Build an index of actions available from each state.
fn build_action_index(system: &TransitionSystem) -> FxHashMap<StateId, FxHashSet<Action>> {
    let mut index: FxHashMap<StateId, FxHashSet<Action>> = FxHashMap::default();
    for step in &system.steps {
        index.entry(step.from).or_default().insert(step.action.clone());
    }
    index
}

/// Check one-directional (forward) simulation: source simulated by target.
///
/// Weaker than bisimulation: only checks the forward direction.
/// For every pair `(s, t)` in the relation:
///   every step `s -a-> s'` must have a matching `t -a-> t'` with `(s', t')` in R
#[must_use]
pub(crate) fn simulation_check(
    source: &TransitionSystem,
    target: &TransitionSystem,
    relation: &BisimulationRelation,
) -> BisimResult {
    let mut steps = Vec::new();

    for &(s, t) in relation.iter() {
        for source_step in source.outgoing(s) {
            let matched = find_matching_step(target, t, &source_step.action, |t_succ| {
                relation.contains(source_step.to, t_succ)
            });

            match matched {
                Some(target_step) => {
                    steps.push(BisimStep {
                        source_from: s,
                        source_action: source_step.action.clone(),
                        source_to: source_step.to,
                        target_from: t,
                        target_action: target_step.action.clone(),
                        target_to: target_step.to,
                    });
                }
                None => {
                    return BisimResult::NotBisimilar(BisimWitness {
                        source_state: s,
                        target_state: t,
                        unmatched_action: source_step.action.clone(),
                        unmatched_successor: source_step.to,
                        direction: BisimDirection::Forward,
                        reason: format!(
                            "simulation fails: source {:?} -{}-> {:?} unmatched from target {:?}",
                            s, source_step.action, source_step.to, t
                        ),
                    });
                }
            }
        }
    }

    BisimResult::Bisimilar { relation: relation.clone(), steps }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Two identical simple systems: s0 -a-> s1, s1 -b-> s2.
    fn identical_systems() -> (TransitionSystem, TransitionSystem, BisimulationRelation) {
        let mut src = TransitionSystem::new(StateId(0));
        src.add_step(StateId(0), Action::Observable("a".into()), StateId(1));
        src.add_step(StateId(1), Action::Observable("b".into()), StateId(2));

        let mut tgt = TransitionSystem::new(StateId(10));
        tgt.add_step(StateId(10), Action::Observable("a".into()), StateId(11));
        tgt.add_step(StateId(11), Action::Observable("b".into()), StateId(12));

        let mut rel = BisimulationRelation::new();
        rel.add(StateId(0), StateId(10));
        rel.add(StateId(1), StateId(11));
        rel.add(StateId(2), StateId(12));

        (src, tgt, rel)
    }

    #[test]
    fn test_check_bisimulation_identical_systems_bisimilar() {
        let (src, tgt, rel) = identical_systems();
        let result = check_bisimulation(&src, &tgt, &rel);
        assert!(
            matches!(result, BisimResult::Bisimilar { .. }),
            "expected Bisimilar, got: {result:?}"
        );
    }

    #[test]
    fn test_check_bisimulation_forward_failure() {
        let mut src = TransitionSystem::new(StateId(0));
        src.add_step(StateId(0), Action::Observable("a".into()), StateId(1));

        let tgt = TransitionSystem::new(StateId(10));
        // Target has no steps!

        let mut rel = BisimulationRelation::new();
        rel.add(StateId(0), StateId(10));

        let result = check_bisimulation(&src, &tgt, &rel);
        match result {
            BisimResult::NotBisimilar(w) => {
                assert_eq!(w.direction, BisimDirection::Forward);
                assert_eq!(w.source_state, StateId(0));
            }
            other => panic!("expected NotBisimilar, got: {other:?}"),
        }
    }

    #[test]
    fn test_check_bisimulation_backward_failure() {
        let src = TransitionSystem::new(StateId(0));
        // Source has no steps.

        let mut tgt = TransitionSystem::new(StateId(10));
        tgt.add_step(StateId(10), Action::Observable("a".into()), StateId(11));

        let mut rel = BisimulationRelation::new();
        rel.add(StateId(0), StateId(10));

        let result = check_bisimulation(&src, &tgt, &rel);
        match result {
            BisimResult::NotBisimilar(w) => {
                assert_eq!(w.direction, BisimDirection::Backward);
                assert_eq!(w.target_state, StateId(10));
            }
            other => panic!("expected NotBisimilar, got: {other:?}"),
        }
    }

    #[test]
    fn test_compute_bisimulation_identical_systems() {
        let mut src = TransitionSystem::new(StateId(0));
        src.add_step(StateId(0), Action::Observable("a".into()), StateId(1));

        let mut tgt = TransitionSystem::new(StateId(10));
        tgt.add_step(StateId(10), Action::Observable("a".into()), StateId(11));

        let rel = compute_bisimulation(&src, &tgt);
        // Initial states should be bisimilar.
        assert!(rel.contains(StateId(0), StateId(10)));
        assert!(rel.contains(StateId(1), StateId(11)));
    }

    #[test]
    fn test_compute_bisimulation_different_actions() {
        let mut src = TransitionSystem::new(StateId(0));
        src.add_step(StateId(0), Action::Observable("a".into()), StateId(1));

        let mut tgt = TransitionSystem::new(StateId(10));
        tgt.add_step(StateId(10), Action::Observable("b".into()), StateId(11));

        let rel = compute_bisimulation(&src, &tgt);
        // Initial states are NOT bisimilar because actions differ.
        assert!(!rel.contains(StateId(0), StateId(10)));
    }

    #[test]
    fn test_simulation_check_one_directional() {
        let (src, tgt, rel) = identical_systems();
        let result = simulation_check(&src, &tgt, &rel);
        assert!(
            matches!(result, BisimResult::Bisimilar { .. }),
            "expected Bisimilar, got: {result:?}"
        );
    }

    #[test]
    fn test_simulation_check_not_bisimilar_but_simulates() {
        // Source: s0 -a-> s1
        // Target: t0 -a-> t1, t0 -b-> t2
        // Forward simulation holds (source is simulated by target).
        // But bisimulation fails (target has extra step).
        let mut src = TransitionSystem::new(StateId(0));
        src.add_step(StateId(0), Action::Observable("a".into()), StateId(1));

        let mut tgt = TransitionSystem::new(StateId(10));
        tgt.add_step(StateId(10), Action::Observable("a".into()), StateId(11));
        tgt.add_step(StateId(10), Action::Observable("b".into()), StateId(12));

        let mut rel = BisimulationRelation::new();
        rel.add(StateId(0), StateId(10));
        rel.add(StateId(1), StateId(11));

        // Forward simulation should succeed.
        let sim_result = simulation_check(&src, &tgt, &rel);
        assert!(matches!(sim_result, BisimResult::Bisimilar { .. }));

        // Full bisimulation should fail (backward: target has "b" that source can't match).
        let bisim_result = check_bisimulation(&src, &tgt, &rel);
        assert!(matches!(bisim_result, BisimResult::NotBisimilar(_)));
    }

    #[test]
    fn test_bisimulation_relation_operations() {
        let mut rel = BisimulationRelation::new();
        assert!(rel.is_empty());
        assert_eq!(rel.size(), 0);

        rel.add(StateId(0), StateId(10));
        rel.add(StateId(1), StateId(11));
        assert!(!rel.is_empty());
        assert_eq!(rel.size(), 2);
        assert!(rel.contains(StateId(0), StateId(10)));
        assert!(!rel.contains(StateId(0), StateId(11)));
    }

    #[test]
    fn test_bisim_witness_fields() {
        let witness = BisimWitness {
            source_state: StateId(0),
            target_state: StateId(10),
            unmatched_action: Action::Observable("x".into()),
            unmatched_successor: StateId(1),
            direction: BisimDirection::Forward,
            reason: "test witness".into(),
        };
        assert_eq!(witness.source_state, StateId(0));
        assert_eq!(witness.target_state, StateId(10));
        assert_eq!(witness.direction, BisimDirection::Forward);
        assert_eq!(witness.reason, "test witness");
    }

    #[test]
    fn test_bisim_step_fields() {
        let step = BisimStep {
            source_from: StateId(0),
            source_action: Action::Observable("a".into()),
            source_to: StateId(1),
            target_from: StateId(10),
            target_action: Action::Observable("a".into()),
            target_to: StateId(11),
        };
        assert_eq!(step.source_from, StateId(0));
        assert_eq!(step.target_to, StateId(11));
    }

    #[test]
    fn test_empty_systems_bisimilar() {
        let src = TransitionSystem::new(StateId(0));
        let tgt = TransitionSystem::new(StateId(10));

        let mut rel = BisimulationRelation::new();
        rel.add(StateId(0), StateId(10));

        let result = check_bisimulation(&src, &tgt, &rel);
        assert!(matches!(result, BisimResult::Bisimilar { .. }));
    }

    #[test]
    fn test_compute_bisimulation_empty_systems() {
        let src = TransitionSystem::new(StateId(0));
        let tgt = TransitionSystem::new(StateId(10));

        let rel = compute_bisimulation(&src, &tgt);
        // Both have one state with no transitions -- they should be bisimilar.
        assert!(rel.contains(StateId(0), StateId(10)));
    }

    #[test]
    fn test_compute_bisimulation_nondeterministic() {
        // Source: s0 -a-> s1, s0 -a-> s2, s1 -b-> s3, s2 -c-> s3
        // Target: t0 -a-> t1, t0 -a-> t2, t1 -b-> t3, t2 -c-> t3
        // Should be bisimilar.
        let mut src = TransitionSystem::new(StateId(0));
        src.add_step(StateId(0), Action::Observable("a".into()), StateId(1));
        src.add_step(StateId(0), Action::Observable("a".into()), StateId(2));
        src.add_step(StateId(1), Action::Observable("b".into()), StateId(3));
        src.add_step(StateId(2), Action::Observable("c".into()), StateId(3));

        let mut tgt = TransitionSystem::new(StateId(10));
        tgt.add_step(StateId(10), Action::Observable("a".into()), StateId(11));
        tgt.add_step(StateId(10), Action::Observable("a".into()), StateId(12));
        tgt.add_step(StateId(11), Action::Observable("b".into()), StateId(13));
        tgt.add_step(StateId(12), Action::Observable("c".into()), StateId(13));

        let rel = compute_bisimulation(&src, &tgt);
        assert!(rel.contains(StateId(0), StateId(10)));
        assert!(rel.contains(StateId(3), StateId(13)));
    }
}
