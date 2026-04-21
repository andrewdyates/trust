// trust-temporal/discovery.rs: Automatic state machine discovery from MIR
//
// tRust #683: End-to-end pipeline that:
//   1. Extracts all enum-based state machines from a VerifiableBody's MIR
//   2. Runs dead-state, unreachable-state, and deadlock-freedom analysis
//   3. Produces structured diagnostics for each discovered machine
//   4. Generates TLA+ specs for model checking dispatch
//
// Zero annotations required -- the discovery is fully automatic from MIR
// patterns (discriminant reads + SwitchInt + aggregate assignments).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::extract::extract_state_machines;
use crate::tla2_bridge;
use crate::{StateId, StateMachine};
use trust_types::fx::FxHashSet;

/// Result of automatic state machine discovery for a single function body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DiscoveryReport {
    /// Name of the function that was analyzed.
    pub function_name: String,
    /// Individual analysis results, one per discovered state machine.
    pub machines: Vec<MachineAnalysis>,
}

/// Analysis result for a single discovered state machine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MachineAnalysis {
    /// The discovered state machine.
    pub machine: StateMachine,
    /// Name of the enum type this machine was extracted from.
    pub enum_name: String,
    /// Dead states: reachable states with no outgoing transitions.
    pub dead_states: Vec<String>,
    /// Unreachable states: states with no path from the initial state.
    pub unreachable_states: Vec<String>,
    /// Whether the machine is deadlock-free (every reachable state has a successor).
    pub deadlock_free: bool,
    /// Number of states discovered by BFS exploration.
    pub states_explored: usize,
    /// Generated TLA+ module for external model checking.
    pub tla_spec: String,
}

/// Diagnostic emitted by the discovery pipeline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Diagnostic {
    /// Severity level.
    pub level: DiagnosticLevel,
    /// Human-readable message.
    pub message: String,
    /// Enum name that this diagnostic relates to.
    pub enum_name: String,
    /// Optional list of affected state names.
    pub affected_states: Vec<String>,
}

/// Severity of a discovery diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DiagnosticLevel {
    /// Informational: state machine discovered, deadlock-freedom proved.
    Info,
    /// Warning: dead states or unreachable states found.
    Warning,
    /// Error: deadlock detected in a connected state machine.
    Error,
}

/// Discover all enum-based state machines in a function body and analyze them.
///
/// This is the primary entry point for automatic state machine discovery.
/// It requires zero annotations -- detection is purely from MIR patterns:
/// - `Rvalue::Discriminant` reads
/// - `Terminator::SwitchInt` on discriminant values
/// - `Rvalue::Aggregate(Adt { .. })` assignments to the same local
///
/// Returns `None` if no state machines are found.
#[must_use]
pub(crate) fn discover_state_machines(
    body: &VerifiableBody,
    function_name: &str,
) -> Option<DiscoveryReport> {
    let machines = extract_state_machines(body);

    if machines.is_empty() {
        return None;
    }

    let analyses: Vec<MachineAnalysis> = machines
        .into_iter()
        .map(|machine| analyze_machine(body, machine))
        .collect();

    Some(DiscoveryReport {
        function_name: function_name.to_string(),
        machines: analyses,
    })
}

/// Discover state machines and produce compiler diagnostics.
///
/// Convenience wrapper over `discover_state_machines` that flattens the
/// analysis into a list of diagnostics suitable for emission.
#[must_use]
pub(crate) fn discover_and_diagnose(
    body: &VerifiableBody,
    function_name: &str,
) -> Vec<Diagnostic> {
    let Some(report) = discover_state_machines(body, function_name) else {
        return Vec::new();
    };

    let mut diagnostics = Vec::new();

    for analysis in &report.machines {
        // Info: machine discovered
        diagnostics.push(Diagnostic {
            level: DiagnosticLevel::Info,
            message: format!(
                "discovered state machine `{}` with {} states and {} transitions",
                analysis.enum_name,
                analysis.machine.states.len(),
                analysis.machine.transitions.len(),
            ),
            enum_name: analysis.enum_name.clone(),
            affected_states: Vec::new(),
        });

        // Warning: dead states
        if !analysis.dead_states.is_empty() {
            diagnostics.push(Diagnostic {
                level: DiagnosticLevel::Warning,
                message: format!(
                    "state machine `{}` has dead states (no outgoing transitions): {}",
                    analysis.enum_name,
                    analysis.dead_states.join(", "),
                ),
                enum_name: analysis.enum_name.clone(),
                affected_states: analysis.dead_states.clone(),
            });
        }

        // Warning: unreachable states
        if !analysis.unreachable_states.is_empty() {
            diagnostics.push(Diagnostic {
                level: DiagnosticLevel::Warning,
                message: format!(
                    "state machine `{}` has unreachable states (no path from initial): {}",
                    analysis.enum_name,
                    analysis.unreachable_states.join(", "),
                ),
                enum_name: analysis.enum_name.clone(),
                affected_states: analysis.unreachable_states.clone(),
            });
        }

        // Info or Error: deadlock freedom
        if analysis.deadlock_free {
            diagnostics.push(Diagnostic {
                level: DiagnosticLevel::Info,
                message: format!(
                    "state machine `{}` is deadlock-free ({} states explored)",
                    analysis.enum_name, analysis.states_explored,
                ),
                enum_name: analysis.enum_name.clone(),
                affected_states: Vec::new(),
            });
        } else {
            diagnostics.push(Diagnostic {
                level: DiagnosticLevel::Error,
                message: format!(
                    "state machine `{}` has deadlock states ({} states explored)",
                    analysis.enum_name, analysis.states_explored,
                ),
                enum_name: analysis.enum_name.clone(),
                affected_states: analysis.dead_states.clone(),
            });
        }
    }

    diagnostics
}

/// Generate verification conditions from discovered state machines.
///
/// For each discovered machine, produces VCs for:
/// - `VcKind::Deadlock`: deadlock-freedom check
/// - `VcKind::DeadState { state }`: one per dead state found
///
/// These VCs can be dispatched through the standard `trust-router`.
#[must_use]
pub(crate) fn generate_vcs(
    body: &VerifiableBody,
    function_name: &str,
    location: &SourceSpan,
) -> Vec<(VerificationCondition, StateMachine)> {
    let Some(report) = discover_state_machines(body, function_name) else {
        return Vec::new();
    };

    let mut vcs = Vec::new();

    for analysis in &report.machines {
        // Deadlock-freedom VC
        vcs.push((
            VerificationCondition {
                kind: VcKind::Deadlock,
                function: function_name.to_string(),
                location: location.clone(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            analysis.machine.clone(),
        ));

        // Dead-state VCs
        for dead in &analysis.dead_states {
            vcs.push((
                VerificationCondition {
                    kind: VcKind::DeadState {
                        state: dead.clone(),
                    },
                    function: function_name.to_string(),
                    location: location.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                analysis.machine.clone(),
            ));
        }
    }

    vcs
}

/// Analyze a single extracted state machine.
fn analyze_machine(body: &VerifiableBody, machine: StateMachine) -> MachineAnalysis {
    // Determine enum name from the first state's name (format: "EnumName::variant_N")
    let enum_name = machine
        .states
        .first()
        .and_then(|s| s.name.split("::").next())
        .unwrap_or("Unknown")
        .to_string();

    // Dead states: reachable states with no outgoing transitions
    let dead_states = find_dead_states(&machine);

    // Unreachable states: states not reachable from initial via BFS
    let unreachable_states = find_unreachable_states(&machine);

    // Deadlock freedom via tla_mc_core BFS
    let (deadlock_free, states_explored) = check_deadlock_freedom_bfs(&machine);

    // Generate TLA+ spec
    let tla_spec = crate::tla_spec_gen::generate_tla_spec(&machine, &enum_name);

    // Try to get better names from the body's local declarations
    let dead_names = resolve_state_names(body, &enum_name, &dead_states);
    let unreachable_names = resolve_state_names(body, &enum_name, &unreachable_states);

    MachineAnalysis {
        machine,
        enum_name,
        dead_states: dead_names,
        unreachable_states: unreachable_names,
        deadlock_free,
        states_explored,
        tla_spec,
    }
}

/// Find dead states (reachable states with no outgoing transitions).
fn find_dead_states(machine: &StateMachine) -> Vec<StateId> {
    machine
        .states
        .iter()
        .filter(|s| machine.is_deadlock_state(s.id))
        .map(|s| s.id)
        .collect()
}

/// Find unreachable states (states with no path from initial).
fn find_unreachable_states(machine: &StateMachine) -> Vec<StateId> {
    // Use bounded reachability with a generous depth
    let max_depth = machine.states.len().saturating_mul(2);
    let reachable = machine.reachable_states(max_depth);
    let reachable_set: FxHashSet<StateId> = reachable.into_iter().collect();

    machine
        .states
        .iter()
        .filter(|s| !reachable_set.contains(&s.id))
        .map(|s| s.id)
        .collect()
}

/// Check deadlock freedom via tla_mc_core BFS exploration.
///
/// Returns (is_deadlock_free, states_explored).
fn check_deadlock_freedom_bfs(machine: &StateMachine) -> (bool, usize) {
    match tla2_bridge::explore(machine) {
        Ok(outcome) => {
            let reachable = machine.reachable_states(outcome.states_discovered);
            let has_deadlock = reachable.iter().any(|id| machine.is_deadlock_state(*id));
            (!has_deadlock, outcome.states_discovered)
        }
        Err(_) => (false, 0),
    }
}

/// Resolve state IDs to human-readable names.
fn resolve_state_names(
    _body: &VerifiableBody,
    _enum_name: &str,
    state_ids: &[StateId],
) -> Vec<String> {
    // State names are already embedded in the StateMachine states.
    // For now, return the variant index representation.
    state_ids
        .iter()
        .map(|id| format!("variant_{}", id.0))
        .collect()
}

impl DiscoveryReport {
    /// Total number of state machines discovered.
    #[must_use]
    pub(crate) fn machine_count(&self) -> usize {
        self.machines.len()
    }

    /// Whether any machine has dead states.
    #[must_use]
    pub(crate) fn has_dead_states(&self) -> bool {
        self.machines.iter().any(|m| !m.dead_states.is_empty())
    }

    /// Whether any machine has unreachable states.
    #[must_use]
    pub(crate) fn has_unreachable_states(&self) -> bool {
        self.machines.iter().any(|m| !m.unreachable_states.is_empty())
    }

    /// Whether all machines are deadlock-free.
    #[must_use]
    pub(crate) fn all_deadlock_free(&self) -> bool {
        self.machines.iter().all(|m| m.deadlock_free)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn enum_ty(name: &str) -> Ty {
        Ty::Adt { name: name.to_string(), fields: vec![] }
    }

    fn assign(place: Place, rvalue: Rvalue) -> Statement {
        Statement::Assign { place, rvalue, span: SourceSpan::default() }
    }

    fn discr_stmt(discr_local: usize, enum_local: usize) -> Statement {
        assign(Place::local(discr_local), Rvalue::Discriminant(Place::local(enum_local)))
    }

    fn variant_stmt(enum_local: usize, enum_name: &str, variant: usize) -> Statement {
        assign(
            Place::local(enum_local),
            Rvalue::Aggregate(AggregateKind::Adt { name: enum_name.to_string(), variant }, vec![]),
        )
    }

    fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts, terminator }
    }

    fn switch(discr_local: usize, targets: &[(u128, usize)], otherwise: usize) -> Terminator {
        Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(discr_local)),
            targets: targets.iter().map(|(value, block)| (*value, BlockId(*block))).collect(),
            otherwise: BlockId(otherwise),
            span: SourceSpan::default(),
        }
    }

    fn body(locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>) -> VerifiableBody {
        VerifiableBody { locals, blocks, arg_count: 0, return_ty: Ty::Unit }
    }

    // ---- discover_state_machines ----

    #[test]
    fn test_discover_linear_state_machine() {
        // State: A(0) -> B(1) -> C(2), C is dead
        let b = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("State"), name: Some("state".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1), (1, 2)], 3)),
                block(1, vec![variant_stmt(1, "State", 1)], Terminator::Return),
                block(2, vec![variant_stmt(1, "State", 2)], Terminator::Return),
                block(3, vec![], Terminator::Return),
            ],
        );

        let report = discover_state_machines(&b, "test_fn").expect("should discover");
        assert_eq!(report.machine_count(), 1);
        assert_eq!(report.function_name, "test_fn");

        let analysis = &report.machines[0];
        assert_eq!(analysis.enum_name, "State");
        assert!(!analysis.dead_states.is_empty(), "variant_2 should be dead");
        assert!(!analysis.deadlock_free, "has terminal state");
        assert!(analysis.states_explored > 0);
        assert!(analysis.tla_spec.contains("MODULE State"));
    }

    #[test]
    fn test_discover_cyclic_state_machine() {
        // A(0) <-> B(1): fully connected cycle, no dead states
        let b = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("Mode"), name: Some("mode".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1), (1, 2)], 3)),
                block(1, vec![variant_stmt(1, "Mode", 1)], Terminator::Return),
                block(2, vec![variant_stmt(1, "Mode", 0)], Terminator::Return),
                block(3, vec![], Terminator::Return),
            ],
        );

        let report = discover_state_machines(&b, "cycle_fn").expect("should discover");
        let analysis = &report.machines[0];
        assert!(analysis.dead_states.is_empty(), "cycle has no dead states");
        assert!(analysis.deadlock_free, "cycle is deadlock-free");
    }

    #[test]
    fn test_discover_no_state_machine_returns_none() {
        let b = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            vec![block(
                0,
                vec![assign(Place::local(1), Rvalue::Use(Operand::Constant(ConstValue::Uint(42, 64))))],
                Terminator::Return,
            )],
        );

        assert!(discover_state_machines(&b, "no_sm").is_none());
    }

    // ---- discover_and_diagnose ----

    #[test]
    fn test_diagnose_dead_state_warning() {
        let b = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("Proto"), name: Some("proto".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1), (1, 2)], 3)),
                block(1, vec![variant_stmt(1, "Proto", 1)], Terminator::Return),
                block(2, vec![variant_stmt(1, "Proto", 2)], Terminator::Return),
                block(3, vec![], Terminator::Return),
            ],
        );

        let diagnostics = discover_and_diagnose(&b, "proto_fn");
        assert!(!diagnostics.is_empty());

        // Should have Info (discovered), Warning (dead states), Error (deadlock)
        assert!(diagnostics.iter().any(|d| d.level == DiagnosticLevel::Info
            && d.message.contains("discovered")));
        assert!(diagnostics.iter().any(|d| d.level == DiagnosticLevel::Warning
            && d.message.contains("dead states")));
        assert!(diagnostics.iter().any(|d| d.level == DiagnosticLevel::Error
            && d.message.contains("deadlock")));
    }

    #[test]
    fn test_diagnose_deadlock_free_cycle() {
        let b = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("Ping"), name: Some("ping".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1), (1, 2)], 3)),
                block(1, vec![variant_stmt(1, "Ping", 1)], Terminator::Return),
                block(2, vec![variant_stmt(1, "Ping", 0)], Terminator::Return),
                block(3, vec![], Terminator::Return),
            ],
        );

        let diagnostics = discover_and_diagnose(&b, "ping_fn");
        assert!(diagnostics.iter().any(|d| d.level == DiagnosticLevel::Info
            && d.message.contains("deadlock-free")));
        assert!(!diagnostics.iter().any(|d| d.level == DiagnosticLevel::Error));
    }

    #[test]
    fn test_diagnose_no_state_machines() {
        let b = body(
            vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            vec![block(0, vec![], Terminator::Return)],
        );

        let diagnostics = discover_and_diagnose(&b, "empty_fn");
        assert!(diagnostics.is_empty());
    }

    // ---- generate_vcs ----

    #[test]
    fn test_generate_vcs_deadlock_and_dead_state() {
        let b = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("Conn"), name: Some("conn".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1), (1, 2)], 3)),
                block(1, vec![variant_stmt(1, "Conn", 1)], Terminator::Return),
                block(2, vec![variant_stmt(1, "Conn", 2)], Terminator::Return),
                block(3, vec![], Terminator::Return),
            ],
        );

        let span = SourceSpan::default();
        let vcs = generate_vcs(&b, "conn_fn", &span);

        // Should have at least 1 Deadlock VC
        assert!(vcs.iter().any(|(vc, _)| matches!(vc.kind, VcKind::Deadlock)));

        // Should have DeadState VCs for terminal states
        let dead_state_vcs: Vec<_> = vcs
            .iter()
            .filter(|(vc, _)| matches!(vc.kind, VcKind::DeadState { .. }))
            .collect();
        assert!(!dead_state_vcs.is_empty(), "should generate DeadState VCs");

        // All VCs should have function name set
        for (vc, _) in &vcs {
            assert_eq!(vc.function, "conn_fn");
        }
    }

    #[test]
    fn test_generate_vcs_no_state_machine() {
        let b = body(
            vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            vec![block(0, vec![], Terminator::Return)],
        );

        let vcs = generate_vcs(&b, "empty_fn", &SourceSpan::default());
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_generate_vcs_cycle_has_deadlock_vc_only() {
        let b = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("Toggle"), name: Some("toggle".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1), (1, 2)], 3)),
                block(1, vec![variant_stmt(1, "Toggle", 1)], Terminator::Return),
                block(2, vec![variant_stmt(1, "Toggle", 0)], Terminator::Return),
                block(3, vec![], Terminator::Return),
            ],
        );

        let vcs = generate_vcs(&b, "toggle_fn", &SourceSpan::default());
        // Cycle has no dead states, so only the Deadlock VC
        assert!(vcs.iter().any(|(vc, _)| matches!(vc.kind, VcKind::Deadlock)));
        // No DeadState VCs for a fully-connected cycle
        let dead_state_count = vcs
            .iter()
            .filter(|(vc, _)| matches!(vc.kind, VcKind::DeadState { .. }))
            .count();
        assert_eq!(dead_state_count, 0, "cycle should have no dead state VCs");
    }

    // ---- DiscoveryReport methods ----

    #[test]
    fn test_report_aggregation_methods() {
        let b = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("S"), name: Some("s".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("d".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1), (1, 2)], 3)),
                block(1, vec![variant_stmt(1, "S", 1)], Terminator::Return),
                block(2, vec![variant_stmt(1, "S", 0)], Terminator::Return),
                block(3, vec![], Terminator::Return),
            ],
        );

        let report = discover_state_machines(&b, "test").expect("should discover");
        assert_eq!(report.machine_count(), 1);
        assert!(!report.has_dead_states()); // cycle: no dead states
        assert!(!report.has_unreachable_states()); // both reachable
        assert!(report.all_deadlock_free()); // cycle is deadlock-free
    }

    // ---- VCs dispatch through tla2_backend ----

    #[test]
    fn test_vcs_verify_through_tla2_backend() {
        use crate::tla2_bridge;

        // Build a linear state machine: A -> B (B is dead/deadlock)
        let b = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("Linear"), name: Some("linear".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1)], 2)),
                block(1, vec![variant_stmt(1, "Linear", 1)], Terminator::Return),
                block(2, vec![], Terminator::Return),
            ],
        );

        let vcs = generate_vcs(&b, "linear_fn", &SourceSpan::default());
        assert!(!vcs.is_empty());

        // Verify each VC using tla2_bridge directly
        for (vc, machine) in &vcs {
            match &vc.kind {
                VcKind::Deadlock => {
                    let is_free = tla2_bridge::check_deadlock_freedom(machine);
                    assert!(!is_free, "linear machine has terminal state B");
                }
                VcKind::DeadState { state } => {
                    // The dead state should be reachable
                    let deadlocks = tla2_bridge::find_deadlock_states(machine);
                    assert!(
                        !deadlocks.is_empty(),
                        "dead state {state} should be detected"
                    );
                }
                _ => {}
            }
        }
    }

    #[test]
    fn test_vcs_verify_cycle_deadlock_free() {
        use crate::tla2_bridge;

        let b = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("Cycle"), name: Some("cycle".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1), (1, 2)], 3)),
                block(1, vec![variant_stmt(1, "Cycle", 1)], Terminator::Return),
                block(2, vec![variant_stmt(1, "Cycle", 0)], Terminator::Return),
                block(3, vec![], Terminator::Return),
            ],
        );

        let vcs = generate_vcs(&b, "cycle_fn", &SourceSpan::default());
        // Only Deadlock VC for a cycle (no dead states)
        assert_eq!(vcs.len(), 1);

        let (vc, machine) = &vcs[0];
        assert!(matches!(vc.kind, VcKind::Deadlock));
        assert!(tla2_bridge::check_deadlock_freedom(machine));
    }

    // ---- TLA+ spec generation ----

    #[test]
    fn test_tla_spec_in_analysis() {
        let b = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("Protocol"), name: Some("p".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("d".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1), (1, 2), (2, 3)], 4)),
                block(1, vec![variant_stmt(1, "Protocol", 1)], Terminator::Return),
                block(2, vec![variant_stmt(1, "Protocol", 2)], Terminator::Return),
                block(3, vec![], Terminator::Return),
                block(4, vec![], Terminator::Return),
            ],
        );

        let report = discover_state_machines(&b, "proto_fn").expect("should discover");
        let tla = &report.machines[0].tla_spec;

        assert!(tla.contains("MODULE Protocol"));
        assert!(tla.contains("VARIABLE state"));
        assert!(tla.contains("Spec =="));
        assert!(tla.contains("===="));
    }
}
