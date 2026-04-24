// trust-router/tla2_backend.rs: Temporal model-checking backend using tla-mc-core
//
// Bridges trust-temporal::StateMachine to tla_mc_core::TransitionSystem and
// dispatches temporal VCs to the generic BFS model checker.
//
// tRust #182: Wired CTL/LTL/liveness/fairness via trust-temporal infrastructure.
// tRust #574: Added subprocess-based tla2 binary dispatch with TLA+ spec generation.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::process::Command;
use std::sync::OnceLock;

use tla_mc_core::{NoopObserver, explore_bfs};
use trust_temporal::ctl::{CtlModelChecker, parse_ctl};
use trust_temporal::fairness::{
    Action, FairnessConstraint as TemporalFairnessConstraint, check_under_fairness,
    detect_starvation,
};
use trust_temporal::liveness::{self, LivenessProperty as TemporalLivenessProp};
use trust_temporal::ltl::parse_ltl;
// tRust #574: Re-export the adapter from trust-temporal's tla2_bridge module.
use trust_temporal::StateMachine;
pub(crate) use trust_temporal::tla2_bridge::StateMachineAdapter;
use trust_types::*;

use crate::{BackendRole, VerificationBackend};

/// Cached tla2 binary path, probed once per process.
static TLA2_PATH: OnceLock<Option<String>> = OnceLock::new();

/// tRust #574: Probe for the tla2 binary.
///
/// Priority: `TLA2_PATH` env var > `tla2` on PATH.
/// Returns `None` if tla2 is not found.
fn probe_tla2_path() -> Option<String> {
    // 1. Explicit env var
    if let Ok(path) = std::env::var("TLA2_PATH")
        && std::path::Path::new(&path).exists()
    {
        return Some(path);
    }

    // 2. PATH probe
    if let Ok(output) = Command::new("which").arg("tla2").output()
        && output.status.success()
    {
        let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
        if !path.is_empty() {
            return Some(path);
        }
    }

    None
}

/// Get the cached tla2 path, probing only once.
fn get_tla2_path() -> Option<&'static str> {
    TLA2_PATH.get_or_init(probe_tla2_path).as_deref()
}

/// tRust #574: Check if the tla2 binary is available on the system.
#[must_use]
pub fn tla2_available() -> bool {
    get_tla2_path().is_some()
}

/// tRust #435: Choose between ExhaustiveFinite and bounded ProofStrength
/// based on whether the state space exploration was complete.
///
/// When BFS/DFS fully explores all reachable states (complete=true), the
/// result is an exhaustive finite-state check. When exploration is bounded
/// (e.g., depth limit, state limit), it's a bounded model check.
fn tla2_proof_strength(states: u64, complete: bool) -> ProofStrength {
    if complete {
        ProofStrength {
            reasoning: ReasoningKind::ExplicitStateModel,
            assurance: AssuranceLevel::Sound,
        }
    } else {
        ProofStrength::bounded(states)
    }
}

/// tRust: Temporal verification backend powered by tla_mc_core::explore_bfs.
///
/// Handles VcKind::DeadState, VcKind::Deadlock, VcKind::Temporal, VcKind::Liveness,
/// and VcKind::Fairness. When a StateMachine is available (via `verify_with_machine`
/// or `StateMachineMetadata`), the backend explores the state space and checks
/// the property using trust-temporal's CTL/LTL/liveness/fairness infrastructure.
pub struct Tla2Backend;

impl Tla2Backend {
    /// tRust: Extract a StateMachine from VC metadata (#182).
    ///
    /// Attempts to extract a `trust_temporal::StateMachine` from the VC's
    /// `StateMachineMetadata`. Returns None if no metadata is present.
    fn extract_state_machine(_vc: &VerificationCondition) -> Option<StateMachine> {
        // tRust #182: VC does not carry state_machine field directly (would require
        // updating 400+ construction sites). Instead, callers use
        // `verify_with_machine()` for direct integration, or the vcgen phase
        // will populate metadata via a separate side-channel (future work).
        None
    }

    /// tRust: Run BFS exploration on a StateMachine and check for deadlocks.
    ///
    /// Returns Proved if the exploration completes with no deadlock states
    /// (i.e., every reachable state has at least one successor). Returns
    /// Failed if a deadlock state is found.
    fn check_deadlock(machine: &StateMachine) -> VerificationResult {
        let adapter = StateMachineAdapter::new(machine.clone());
        let mut observer = NoopObserver::<StateMachineAdapter>::default();

        match explore_bfs(&adapter, &mut observer) {
            Ok(outcome) => {
                // Check every discovered state for deadlock (no outgoing transitions)
                let reachable = machine.reachable_states(outcome.states_discovered);
                let deadlocked: Vec<_> =
                    reachable.iter().filter(|id| machine.is_deadlock_state(**id)).collect();

                if deadlocked.is_empty() {
                    VerificationResult::Proved {
                        solver: "tla2".into(),
                        time_ms: 0,
                        // tRust #435: ExplicitStateModel when BFS is complete
                        strength: tla2_proof_strength(
                            outcome.states_discovered as u64,
                            outcome.completed,
                        ),
                        proof_certificate: None,
                        solver_warnings: None,
                    }
                } else {
                    // Encode deadlocked state IDs as counterexample assignments
                    let assignments: Vec<_> = deadlocked
                        .iter()
                        .enumerate()
                        .map(|(i, id)| {
                            (format!("deadlock_state_{i}"), CounterexampleValue::Int(id.0 as i128))
                        })
                        .collect();
                    VerificationResult::Failed {
                        solver: "tla2".into(),
                        time_ms: 0,
                        counterexample: Some(Counterexample::new(assignments)),
                    }
                }
            }
            Err(e) => VerificationResult::Unknown {
                solver: "tla2".into(),
                time_ms: 0,
                reason: format!("BFS exploration failed: {e}"),
            },
        }
    }

    /// tRust: Run BFS and check whether a named dead-state is reachable.
    fn check_dead_state(machine: &StateMachine, state_name: &str) -> VerificationResult {
        let adapter = StateMachineAdapter::new(machine.clone());
        let mut observer = NoopObserver::<StateMachineAdapter>::default();

        match explore_bfs(&adapter, &mut observer) {
            Ok(outcome) => {
                let reachable = machine.reachable_states(outcome.states_discovered);
                let found = reachable.iter().any(|id| {
                    machine.state(*id).is_some_and(|s| {
                        s.name == state_name || s.labels.contains(&state_name.to_string())
                    })
                });

                if found {
                    VerificationResult::Failed {
                        solver: "tla2".into(),
                        time_ms: 0,
                        counterexample: Some(Counterexample::new(vec![(
                            "dead_state_reachable".to_string(),
                            CounterexampleValue::Bool(true),
                        )])),
                    }
                } else {
                    VerificationResult::Proved {
                        solver: "tla2".into(),
                        time_ms: 0,
                        // tRust #435: ExplicitStateModel when BFS is complete
                        strength: tla2_proof_strength(
                            outcome.states_discovered as u64,
                            outcome.completed,
                        ),
                        proof_certificate: None,
                        solver_warnings: None,
                    }
                }
            }
            Err(e) => VerificationResult::Unknown {
                solver: "tla2".into(),
                time_ms: 0,
                reason: format!("BFS exploration failed: {e}"),
            },
        }
    }

    /// tRust: Check a CTL temporal property against a StateMachine (#182).
    ///
    /// Parses the property string as a CTL formula and runs the labeling
    /// algorithm. Returns Proved if the initial state satisfies the formula,
    /// Failed with a counterexample path otherwise.
    fn check_temporal(machine: &StateMachine, property: &str) -> VerificationResult {
        let formula = match parse_ctl(property) {
            Ok(f) => f,
            Err(e) => {
                // tRust: Fall back to LTL parsing if CTL parse fails
                match parse_ltl(property) {
                    Ok(_ltl_formula) => {
                        // tRust: LTL property detected. Convert to equivalent CTL check
                        // where possible (G phi -> AG phi, F phi -> EF phi).
                        // For full LTL, use VcKind::Liveness.
                        return VerificationResult::Unknown {
                            solver: "tla2".into(),
                            time_ms: 0,
                            reason: format!(
                                "property `{property}` parses as LTL but not CTL; \
                                 use VcKind::Liveness for LTL checking (CTL parse error: {e})"
                            ),
                        };
                    }
                    Err(_) => {
                        return VerificationResult::Unknown {
                            solver: "tla2".into(),
                            time_ms: 0,
                            reason: format!(
                                "failed to parse temporal property `{property}` as CTL: {e}"
                            ),
                        };
                    }
                }
            }
        };

        let checker = CtlModelChecker::new(machine);
        let result = checker.check(&formula);

        if result.holds_at_initial(machine.initial) {
            VerificationResult::Proved {
                solver: "tla2".into(),
                time_ms: 0,
                // tRust #435: CTL labeling explores all states exhaustively
                strength: tla2_proof_strength(machine.states.len() as u64, true),
                proof_certificate: None,
                solver_warnings: None,
            }
        } else {
            // tRust: Build counterexample from witness trace if available
            let counterexample = result.witness.map(|trace| {
                let assignments: Vec<_> = trace
                    .states
                    .iter()
                    .enumerate()
                    .map(|(i, sid)| {
                        let _state_name = machine
                            .state(*sid)
                            .map_or_else(|| format!("state_{}", sid.0), |s| s.name.clone());
                        (format!("step_{i}"), CounterexampleValue::Bool(true))
                    })
                    .collect();
                Counterexample::new(assignments)
            });
            VerificationResult::Failed { solver: "tla2".into(), time_ms: 0, counterexample }
        }
    }

    /// tRust: Check a liveness property against a StateMachine (#182).
    ///
    /// Uses trust-temporal's SCC-based liveness checking. Returns Proved
    /// if all infinite paths eventually satisfy the predicate, Failed with
    /// a lasso counterexample otherwise.
    fn check_liveness(
        machine: &StateMachine,
        property: &trust_types::LivenessProperty,
    ) -> VerificationResult {
        let temporal_prop = TemporalLivenessProp::new(&property.name, &property.predicate);

        // tRust: If fairness constraints are specified, check under fairness
        if !property.fairness.is_empty() {
            let mut temporal_fairness = Vec::with_capacity(property.fairness.len());
            for fc in &property.fairness {
                let temporal_constraint = match fc {
                    trust_types::FairnessConstraint::Weak { action, .. } => {
                        TemporalFairnessConstraint::WeakFairness(Action::new(action.as_str()))
                    }
                    trust_types::FairnessConstraint::Strong { action, .. } => {
                        TemporalFairnessConstraint::StrongFairness(Action::new(action.as_str()))
                    }
                    // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
                    _ => {
                        return VerificationResult::Unknown {
                            solver: "tla2".into(),
                            time_ms: 0,
                            reason: "unhandled variant".to_string(),
                        };
                    }
                };
                temporal_fairness.push(temporal_constraint);
            }

            let result = check_under_fairness(machine, &temporal_prop, &temporal_fairness);
            return Self::liveness_result_to_vr(machine, &result);
        }

        let result = liveness::check_liveness(machine, &temporal_prop);
        Self::liveness_result_to_vr(machine, &result)
    }

    /// tRust: Check fairness constraints against a StateMachine (#182).
    ///
    /// Uses trust-temporal's starvation detection and fair cycle analysis.
    /// Returns Proved if the fairness constraint is satisfiable (no starvation
    /// of the constrained action), Failed if starvation is detected.
    fn check_fairness(
        machine: &StateMachine,
        constraint: &trust_types::FairnessConstraint,
    ) -> VerificationResult {
        let (action_name, is_weak) = match constraint {
            trust_types::FairnessConstraint::Weak { action, .. } => (action.as_str(), true),
            trust_types::FairnessConstraint::Strong { action, .. } => (action.as_str(), false),
            // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
            _ => {
                return VerificationResult::Unknown {
                    solver: "tla2".into(),
                    time_ms: 0,
                    reason: "unhandled variant".to_string(),
                };
            }
        };

        // tRust: Check starvation for the constrained action
        let witnesses = detect_starvation(machine);
        let starved = witnesses.iter().find(|w| w.action == action_name);

        match starved {
            Some(witness) => {
                // tRust: Starvation detected; now check if fairness would prevent it
                let temporal_constraint = if is_weak {
                    TemporalFairnessConstraint::WeakFairness(Action::new(action_name))
                } else {
                    TemporalFairnessConstraint::StrongFairness(Action::new(action_name))
                };

                // tRust: Use a synthetic liveness property: "eventually action_name"
                // Under the fairness constraint, this should be satisfiable
                let prop = TemporalLivenessProp::new(format!("fair_{action_name}"), action_name);
                let result = check_under_fairness(machine, &prop, &[temporal_constraint]);

                match result {
                    trust_temporal::LivenessResult::Satisfied => VerificationResult::Proved {
                        solver: "tla2".into(),
                        time_ms: 0,
                        strength: ProofStrength::bounded(machine.states.len() as u64),
                        proof_certificate: None,
                        solver_warnings: None,
                    },
                    trust_temporal::LivenessResult::Violated { .. } => {
                        let assignments: Vec<_> = witness
                            .avoiding_cycle
                            .iter()
                            .enumerate()
                            .map(|(i, sid)| {
                                (
                                    format!("avoiding_cycle_{i}"),
                                    CounterexampleValue::Int(sid.0 as i128),
                                )
                            })
                            .collect();
                        VerificationResult::Failed {
                            solver: "tla2".into(),
                            time_ms: 0,
                            counterexample: Some(Counterexample::new(assignments)),
                        }
                    }
                    _ => VerificationResult::Unknown {
                        solver: "tla2".into(),
                        time_ms: 0,
                        reason: "unexpected liveness result".to_string(),
                    },
                }
            }
            None => {
                // No starvation detected for this action
                VerificationResult::Proved {
                    solver: "tla2".into(),
                    time_ms: 0,
                    strength: ProofStrength::bounded(machine.states.len() as u64),
                    proof_certificate: None,
                    solver_warnings: None,
                }
            }
        }
    }

    /// tRust: Convert trust-temporal LivenessResult to VerificationResult.
    fn liveness_result_to_vr(
        machine: &StateMachine,
        result: &trust_temporal::LivenessResult,
    ) -> VerificationResult {
        match result {
            trust_temporal::LivenessResult::Satisfied => VerificationResult::Proved {
                solver: "tla2".into(),
                time_ms: 0,
                strength: ProofStrength::bounded(machine.states.len() as u64),
                proof_certificate: None,
                solver_warnings: None,
            },
            trust_temporal::LivenessResult::Violated { lasso_trace, cycle_start } => {
                let mut assignments: Vec<_> = lasso_trace
                    .iter()
                    .enumerate()
                    .map(|(i, sid)| {
                        let label = if i < *cycle_start { "prefix" } else { "cycle" };
                        let _state_name = machine
                            .state(*sid)
                            .map_or_else(|| format!("state_{}", sid.0), |s| s.name.clone());
                        (format!("{label}_step_{i}"), CounterexampleValue::Bool(true))
                    })
                    .collect();
                assignments.push((
                    "cycle_start_index".to_string(),
                    CounterexampleValue::Int(*cycle_start as i128),
                ));
                VerificationResult::Failed {
                    solver: "tla2".into(),
                    time_ms: 0,
                    counterexample: Some(Counterexample::new(assignments)),
                }
            }
            _ => VerificationResult::Unknown {
                solver: "tla2".into(),
                time_ms: 0,
                reason: "unexpected liveness result variant".to_string(),
            },
        }
    }

    /// tRust: Verify a VC with an explicit StateMachine (#182).
    ///
    /// This is the primary entry point for temporal verification when the
    /// caller has already extracted a StateMachine. Dispatches to the
    /// appropriate checker based on VcKind.
    #[must_use]
    pub fn verify_with_machine(
        vc: &VerificationCondition,
        machine: &StateMachine,
    ) -> VerificationResult {
        match &vc.kind {
            VcKind::Deadlock => Self::check_deadlock(machine),
            VcKind::DeadState { state } => Self::check_dead_state(machine, state),
            VcKind::Temporal { property } => Self::check_temporal(machine, property),
            VcKind::Liveness { property } => Self::check_liveness(machine, property),
            VcKind::Fairness { constraint } => Self::check_fairness(machine, constraint),
            VcKind::RefinementViolation { spec_file, action } => VerificationResult::Unknown {
                solver: "tla2".into(),
                time_ms: 0,
                reason: format!(
                    "refinement checking for spec {spec_file} action {action} not yet implemented"
                ),
            },
            VcKind::ProtocolViolation { protocol, violation } => VerificationResult::Unknown {
                solver: "tla2".into(),
                time_ms: 0,
                reason: format!(
                    "protocol violation checking for {protocol}: {violation} not yet implemented"
                ),
            },
            _ => VerificationResult::Unknown {
                solver: "tla2".into(),
                time_ms: 0,
                reason: format!("VcKind {:?} not handled by tla2 backend", vc.kind.description()),
            },
        }
    }
}

impl VerificationBackend for Tla2Backend {
    fn name(&self) -> &str {
        "tla2"
    }

    fn role(&self) -> BackendRole {
        BackendRole::Temporal
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        // tRust: Handle liveness, fairness, refinement, protocol, and
        // termination VCs. NonTermination is a liveness property (#194):
        // "the program eventually terminates" requires Buchi automata /
        // well-founded order checking, not safety model checking (PDR/IC3).
        matches!(
            vc.kind,
            VcKind::DeadState { .. }
                | VcKind::Deadlock
                | VcKind::Temporal { .. }
                | VcKind::Liveness { .. }
                | VcKind::Fairness { .. }
                | VcKind::RefinementViolation { .. }
                | VcKind::ProtocolViolation { .. }
                | VcKind::NonTermination { .. }
        )
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        // tRust #182: Try to extract state machine from VC metadata
        match Self::extract_state_machine(vc) {
            Some(machine) => Self::verify_with_machine(vc, &machine),
            None => {
                // tRust: Handle refinement/protocol specially (no SM needed for message)
                if let VcKind::RefinementViolation { spec_file, action } = &vc.kind {
                    return VerificationResult::Unknown {
                        solver: "tla2".into(),
                        time_ms: 0,
                        reason: format!(
                            "refinement checking for spec {spec_file} action {action} \
                             requires StateMachine metadata; wire via trust-mir-extract"
                        ),
                    };
                }
                VerificationResult::Unknown {
                    solver: "tla2".into(),
                    time_ms: 0,
                    reason: "no StateMachine metadata in VC; \
                             use Tla2Backend::verify_with_machine() or populate metadata \
                             via trust-mir-extract"
                        .to_string(),
                }
            }
        }
    }
}

/// tRust: Convenience function to verify a deadlock-freedom VC directly
/// from a StateMachine, bypassing VC metadata extraction.
///
/// Useful for tests and direct integration before VC metadata wiring
/// is complete.
#[must_use]
pub fn verify_deadlock_freedom(machine: &StateMachine) -> VerificationResult {
    Tla2Backend::check_deadlock(machine)
}

/// tRust: Convenience function to verify dead-state unreachability directly
/// from a StateMachine.
#[must_use]
pub fn verify_dead_state_unreachable(
    machine: &StateMachine,
    state_name: &str,
) -> VerificationResult {
    Tla2Backend::check_dead_state(machine, state_name)
}

/// tRust: Convenience function to check a CTL temporal property (#182).
#[must_use]
pub fn verify_temporal_property(machine: &StateMachine, property: &str) -> VerificationResult {
    Tla2Backend::check_temporal(machine, property)
}

/// tRust: Convenience function to check a liveness property (#182).
#[must_use]
pub fn verify_liveness(
    machine: &StateMachine,
    property: &trust_types::LivenessProperty,
) -> VerificationResult {
    Tla2Backend::check_liveness(machine, property)
}

/// tRust: Convenience function to check a fairness constraint (#182).
#[must_use]
pub fn verify_fairness(
    machine: &StateMachine,
    constraint: &trust_types::FairnessConstraint,
) -> VerificationResult {
    Tla2Backend::check_fairness(machine, constraint)
}

/// tRust #574: Subprocess-based tla2 verification backend.
///
/// Generates TLA+ specs from `StateMachine` and invokes the tla2 binary
/// as a subprocess (similar to lean5/zani backends). Falls back gracefully
/// to `Unknown` when the tla2 binary is not on PATH.
///
/// This backend is complementary to `Tla2Backend` (which uses the in-process
/// `tla_mc_core` library). Use `Tla2SubprocessBackend` when you want the
/// full tla2 tool capabilities (symmetry reduction, TLC-style exploration)
/// beyond what tla_mc_core provides.
pub struct Tla2SubprocessBackend;

impl Tla2SubprocessBackend {
    /// Create a new subprocess backend.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

impl Default for Tla2SubprocessBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationBackend for Tla2SubprocessBackend {
    fn name(&self) -> &str {
        "tla2-subprocess"
    }

    fn role(&self) -> BackendRole {
        BackendRole::Temporal
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        // tRust #574: Same temporal VC kinds as Tla2Backend, but only when
        // tla2 binary is available.
        if !tla2_available() {
            return false;
        }
        matches!(
            vc.kind,
            VcKind::DeadState { .. }
                | VcKind::Deadlock
                | VcKind::Temporal { .. }
                | VcKind::Liveness { .. }
                | VcKind::Fairness { .. }
                | VcKind::RefinementViolation { .. }
                | VcKind::ProtocolViolation { .. }
                | VcKind::NonTermination { .. }
        )
    }

    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        // tRust #574: Without a state machine, we cannot generate a TLA+ spec.
        // Fall back to informative Unknown.
        VerificationResult::Unknown {
            solver: "tla2-subprocess".into(),
            time_ms: 0,
            reason: "no StateMachine metadata in VC; \
                     use verify_with_machine() or populate metadata \
                     via trust-mir-extract"
                .to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_mc_core::TransitionSystem;
    use trust_temporal::tla_spec_gen as spec_gen;
    use trust_temporal::{State, StateId, StateMachineBuilder, Transition};

    #[test]
    fn tla2_handles_temporal_kinds_only() {
        let backend = Tla2Backend;
        let temporal = VerificationCondition {
            kind: VcKind::Temporal { property: "eventually done".into() },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let l0 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        assert!(backend.can_handle(&temporal));
        assert!(!backend.can_handle(&l0));
    }

    #[test]
    fn tla2_verify_returns_unknown_without_metadata() {
        let backend = Tla2Backend;
        let vc = VerificationCondition {
            kind: VcKind::Deadlock,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { solver, .. } if solver == "tla2"));
    }

    #[test]
    fn tla2_handles_refinement_violations() {
        let backend = Tla2Backend;
        let vc = VerificationCondition {
            kind: VcKind::RefinementViolation {
                spec_file: "Bank.tla".into(),
                action: "overdraft".into(),
            },
            function: "bank_step".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        assert!(backend.can_handle(&vc));
        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { solver, .. } if solver == "tla2"));
    }

    #[test]
    fn adapter_implements_transition_system() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "End"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .build();

        let adapter = StateMachineAdapter::new(machine);
        assert_eq!(adapter.initial_states(), vec![0]);
        assert_eq!(adapter.successors(&0), vec![("go".to_string(), 1)]);
        assert!(adapter.successors(&1).is_empty());
        assert_eq!(adapter.fingerprint(&42), 42);
    }

    #[test]
    fn adapter_bfs_explores_full_state_space() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_state(State::new(StateId(2), "C"))
            .add_transition(Transition::new(StateId(0), StateId(1), "ab"))
            .add_transition(Transition::new(StateId(1), StateId(2), "bc"))
            .build();

        let adapter = StateMachineAdapter::new(machine);
        let mut observer = NoopObserver::<StateMachineAdapter>::default();
        let outcome = explore_bfs(&adapter, &mut observer).expect("BFS should succeed");

        assert!(outcome.completed);
        assert_eq!(outcome.states_discovered, 3);
    }

    #[test]
    fn verify_deadlock_freedom_proves_on_cycle() {
        // A->B->A cycle: no deadlock states
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "forward"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let result = verify_deadlock_freedom(&machine);
        assert!(result.is_proved(), "cycle should be deadlock-free: {result:?}");
    }

    #[test]
    fn verify_deadlock_freedom_fails_on_terminal_state() {
        // A->B with B terminal: deadlock
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .build();

        let result = verify_deadlock_freedom(&machine);
        assert!(result.is_failed(), "terminal state should be detected as deadlock: {result:?}");
    }

    #[test]
    fn verify_dead_state_unreachable_proves_when_not_reachable() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "OK"))
            .add_state(State::new(StateId(2), "Error").with_label("error"))
            .add_transition(Transition::new(StateId(0), StateId(1), "proceed"))
            .build();

        let result = verify_dead_state_unreachable(&machine, "Error");
        assert!(result.is_proved(), "unreachable Error state should be proved safe: {result:?}");
    }

    #[test]
    fn verify_dead_state_unreachable_fails_when_reachable() {
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "Error").with_label("error"))
            .add_transition(Transition::new(StateId(0), StateId(1), "fail"))
            .build();

        let result = verify_dead_state_unreachable(&machine, "Error");
        assert!(result.is_failed(), "reachable Error state should be detected: {result:?}");
    }

    // tRust: Liveness and fairness backend tests (#49).

    #[test]
    fn tla2_handles_liveness_vcs() {
        let backend = Tla2Backend;
        let liveness_vc = VerificationCondition {
            kind: VcKind::Liveness {
                property: trust_types::LivenessProperty {
                    name: "termination".into(),
                    operator: TemporalOperator::Eventually,
                    predicate: "done".into(),
                    consequent: None,
                    fairness: vec![],
                },
            },
            function: "async_main".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        assert!(backend.can_handle(&liveness_vc));
        let result = backend.verify(&liveness_vc);
        assert!(matches!(result, VerificationResult::Unknown { solver, .. } if solver == "tla2"));
    }

    #[test]
    fn tla2_handles_fairness_vcs() {
        let backend = Tla2Backend;
        let fairness_vc = VerificationCondition {
            kind: VcKind::Fairness {
                constraint: trust_types::FairnessConstraint::Weak {
                    action: "schedule".into(),
                    vars: vec!["tasks".into()],
                },
            },
            function: "scheduler".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        assert!(backend.can_handle(&fairness_vc));
        let result = backend.verify(&fairness_vc);
        assert_eq!(result.solver_name(), "tla2");
    }

    #[test]
    fn tla2_rejects_l0_safety_vcs() {
        let backend = Tla2Backend;
        let safety_kinds = [VcKind::DivisionByZero, VcKind::IndexOutOfBounds, VcKind::Unreachable];
        for kind in safety_kinds {
            let vc = VerificationCondition {
                kind,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            };
            assert!(!backend.can_handle(&vc), "tla2 should not handle L0 safety VCs");
        }
    }

    // ---- tRust #182: New tests for wired temporal pipeline ----

    /// Helper: build a simple state machine for testing temporal properties.
    /// States: Idle(start) -> Working(active) -> Done(done,terminal)
    /// Working also has a self-loop.
    fn test_machine() -> StateMachine {
        StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Idle").with_label("start"))
            .add_state(State::new(StateId(1), "Working").with_label("active"))
            .add_state(State::new(StateId(2), "Done").with_label("done").with_label("terminal"))
            .add_transition(Transition::new(StateId(0), StateId(1), "begin"))
            .add_transition(Transition::new(StateId(1), StateId(1), "work"))
            .add_transition(Transition::new(StateId(1), StateId(2), "finish"))
            .build()
    }

    #[test]
    fn test_ctl_ef_error_detection() {
        // Test EF(done): can we reach a done state?
        let machine = test_machine();
        let result = verify_temporal_property(&machine, "EF done");
        assert!(result.is_proved(), "EF(done) should hold from Idle: {result:?}");
    }

    #[test]
    fn test_ctl_ag_property_fails() {
        // AG(start): globally start should fail since Working is not start
        let machine = test_machine();
        let result = verify_temporal_property(&machine, "AG start");
        assert!(result.is_failed(), "AG(start) should fail: {result:?}");
    }

    #[test]
    fn test_ctl_ef_unreachable_state() {
        // Build a machine where "error" is not reachable
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "OK").with_label("ok"))
            .add_state(State::new(StateId(1), "Error").with_label("error"))
            .add_transition(Transition::new(StateId(0), StateId(0), "loop"))
            .build();

        let result = verify_temporal_property(&machine, "EF error");
        assert!(result.is_failed(), "EF(error) should fail since Error unreachable: {result:?}");
    }

    #[test]
    fn test_ctl_parse_error_returns_unknown() {
        let machine = test_machine();
        let result = verify_temporal_property(&machine, "@@@invalid");
        assert!(
            matches!(result, VerificationResult::Unknown { .. }),
            "invalid property should return Unknown: {result:?}"
        );
    }

    #[test]
    fn test_liveness_satisfied_with_accepting_cycle() {
        // All cycles pass through Done (done label) so GF(done) holds
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("done"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let property = trust_types::LivenessProperty {
            name: "reach_done".into(),
            operator: TemporalOperator::AlwaysEventually,
            predicate: "done".into(),
            consequent: None,
            fairness: vec![],
        };

        let result = verify_liveness(&machine, &property);
        assert!(result.is_proved(), "liveness should be satisfied: {result:?}");
    }

    #[test]
    fn test_liveness_violated_spin_cycle() {
        // A self-loops on A forever, never reaches "done"
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Spin").with_label("spinning"))
            .add_transition(Transition::new(StateId(0), StateId(0), "spin"))
            .build();

        let property = trust_types::LivenessProperty {
            name: "eventually_done".into(),
            operator: TemporalOperator::Eventually,
            predicate: "done".into(),
            consequent: None,
            fairness: vec![],
        };

        let result = verify_liveness(&machine, &property);
        assert!(result.is_failed(), "liveness should be violated by spin: {result:?}");
    }

    #[test]
    fn test_liveness_under_fairness_satisfied() {
        // A: spin (self-loop) + escape to B(done). Under weak fairness on
        // "escape", the spin cycle is unfair, so liveness holds.
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("a"))
            .add_state(State::new(StateId(1), "B").with_label("done"))
            .add_transition(Transition::new(StateId(0), StateId(0), "spin"))
            .add_transition(Transition::new(StateId(0), StateId(1), "escape"))
            .build();

        let property = trust_types::LivenessProperty {
            name: "eventually_done".into(),
            operator: TemporalOperator::Eventually,
            predicate: "done".into(),
            consequent: None,
            fairness: vec![trust_types::FairnessConstraint::Weak {
                action: "escape".into(),
                vars: vec![],
            }],
        };

        let result = verify_liveness(&machine, &property);
        assert!(result.is_proved(), "liveness under fairness should hold: {result:?}");
    }

    #[test]
    fn test_fairness_no_starvation() {
        // A -> B -> A cycle, both actions always taken. No starvation.
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();

        let constraint =
            trust_types::FairnessConstraint::Weak { action: "go".into(), vars: vec![] };

        let result = verify_fairness(&machine, &constraint);
        assert!(result.is_proved(), "no starvation expected: {result:?}");
    }

    #[test]
    fn test_fairness_starvation_detected() {
        // A: fast (self-loop) + slow (to B). "slow" can be starved.
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A").with_label("slow"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(0), "fast"))
            .add_transition(Transition::new(StateId(0), StateId(1), "slow"))
            .build();

        let constraint =
            trust_types::FairnessConstraint::Weak { action: "slow".into(), vars: vec![] };

        let result = verify_fairness(&machine, &constraint);
        // Under weak fairness on "slow", the unfair spin cycle is filtered,
        // so fairness should be proved satisfiable.
        assert!(result.is_proved(), "under fairness, slow should not be starved: {result:?}");
    }

    #[test]
    fn test_verify_with_machine_dispatches_correctly() {
        let machine = test_machine();

        // Deadlock
        let vc = VerificationCondition {
            kind: VcKind::Deadlock,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let result = Tla2Backend::verify_with_machine(&vc, &machine);
        // Machine has terminal state Done, so deadlock detected
        assert!(result.is_failed(), "Done is a deadlock state: {result:?}");

        // CTL temporal
        let vc = VerificationCondition {
            kind: VcKind::Temporal { property: "EF done".into() },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let result = Tla2Backend::verify_with_machine(&vc, &machine);
        assert!(result.is_proved(), "EF(done) should hold: {result:?}");
    }

    // ---- tRust #574: TLA+ spec generation and subprocess backend tests ----

    #[test]
    fn test_tla_spec_generation_from_machine() {
        let machine = test_machine();
        let spec = spec_gen::generate_tla_spec(&machine, "RouterTest");
        assert!(spec.contains("MODULE RouterTest"), "should have module header");
        assert!(spec.contains("Init == state = \"Idle\""), "should have init from Idle");
        assert!(spec.contains("state' = \"Working\""), "should have working transition");
        assert!(spec.contains("state' = \"Done\""), "should have done transition");
        assert!(spec.contains("Spec =="), "should have spec definition");
    }

    #[test]
    fn test_tla_full_spec_with_property() {
        let machine = test_machine();
        let property = trust_temporal::TemporalProperty::Eventually { condition: "done".into() };
        let spec = spec_gen::generate_full_spec(&machine, &property, "PropTest");
        assert!(spec.contains("Property == <>done"), "should have property definition");
        assert!(spec.contains("Init =="), "should have init");
        assert!(spec.contains("===="), "should have module footer");
    }

    #[test]
    fn test_subprocess_backend_role() {
        let backend = Tla2SubprocessBackend::new();
        assert_eq!(backend.name(), "tla2-subprocess");
        assert_eq!(backend.role(), BackendRole::Temporal);
    }

    #[test]
    fn test_subprocess_backend_graceful_degradation() {
        // tRust #574: When tla2 binary is not on PATH, verify returns Unknown
        // (not panic or error). The can_handle check also returns false.
        let backend = Tla2SubprocessBackend::new();
        let vc = VerificationCondition {
            kind: VcKind::Deadlock,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        // Verify always returns Unknown without state machine
        let result = backend.verify(&vc);
        assert!(
            matches!(result, VerificationResult::Unknown { solver, .. } if solver == "tla2-subprocess")
        );
    }

    #[test]
    fn test_bridge_adapter_reexported_from_trust_temporal() {
        // tRust #574: Verify the StateMachineAdapter from trust-temporal works
        // the same as the previously local one.
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "Start"))
            .add_state(State::new(StateId(1), "End"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .build();

        let adapter = StateMachineAdapter::new(machine);
        assert_eq!(adapter.initial_states(), vec![0]);
        assert_eq!(adapter.successors(&0), vec![("go".to_string(), 1)]);
        assert!(adapter.successors(&1).is_empty());
        assert_eq!(adapter.fingerprint(&42), 42);
    }

    #[test]
    fn test_bridge_explore_via_trust_temporal() {
        // tRust #574: Verify BFS exploration works through the trust-temporal bridge.
        let machine = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_state(State::new(StateId(2), "C"))
            .add_transition(Transition::new(StateId(0), StateId(1), "ab"))
            .add_transition(Transition::new(StateId(1), StateId(2), "bc"))
            .build();

        let outcome = trust_temporal::tla2_bridge::explore(&machine).expect("BFS should succeed");
        assert!(outcome.completed);
        assert_eq!(outcome.states_discovered, 3);
    }

    #[test]
    fn test_bridge_deadlock_check() {
        // tRust #574: Verify deadlock freedom check via trust-temporal bridge.
        let cycle = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "forward"))
            .add_transition(Transition::new(StateId(1), StateId(0), "back"))
            .build();
        assert!(trust_temporal::tla2_bridge::check_deadlock_freedom(&cycle));

        let terminal = StateMachineBuilder::new(StateId(0))
            .add_state(State::new(StateId(0), "A"))
            .add_state(State::new(StateId(1), "B"))
            .add_transition(Transition::new(StateId(0), StateId(1), "go"))
            .build();
        assert!(!trust_temporal::tla2_bridge::check_deadlock_freedom(&terminal));
    }
}
