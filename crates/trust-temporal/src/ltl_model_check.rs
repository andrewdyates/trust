// trust-temporal/ltl_model_check.rs: LTL model checking over finite traces
//
// Evaluates LTL formulas over finite execution traces using finite-trace
// semantics (FLTL). Provides both batch checking (`check_trace`) and
// incremental online monitoring (`monitor`), plus a simplified automaton
// construction for monitoring and shortest-counterexample extraction.
//
// References:
//   Bauer, Leucker, Schallhart. "Runtime Verification for LTL and TLTL"
//     (ACM TOSEM, 2011). Finite-trace semantics and 3-valued monitoring.
//   Barringer, Goldberg, Havelund, Sen. "Rule-Based Runtime Verification"
//     (VMCAI 2004). Online monitoring approach.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::fmt;

// ---------------------------------------------------------------------------
// LTL Formula AST (finite-trace variant)
// ---------------------------------------------------------------------------

/// An LTL formula for finite-trace model checking.
///
/// This type includes the `Release` operator (dual of `Until`) which is
/// needed for complete finite-trace semantics. For conversion from the
/// parser-oriented `crate::ltl::LtlFormula`, see [`from_parsed_ltl`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LtlFormula {
    /// Atomic proposition: evaluated against `TraceState` truth values.
    Atom(String),
    /// Negation: !phi.
    Not(Box<LtlFormula>),
    /// Conjunction: phi /\ psi.
    And(Box<LtlFormula>, Box<LtlFormula>),
    /// Disjunction: phi \/ psi.
    Or(Box<LtlFormula>, Box<LtlFormula>),
    /// Next: X phi (phi holds at the next position in the trace).
    Next(Box<LtlFormula>),
    /// Until: phi U psi (phi holds until psi becomes true).
    Until(Box<LtlFormula>, Box<LtlFormula>),
    /// Eventually: F phi (psi holds at some future position).
    Eventually(Box<LtlFormula>),
    /// Always: G phi (phi holds at all remaining positions).
    Always(Box<LtlFormula>),
    /// Release: phi R psi (psi holds until and including when phi first holds,
    /// or psi holds forever if phi never holds). Dual of Until.
    Release(Box<LtlFormula>, Box<LtlFormula>),
}

impl fmt::Display for LtlFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LtlFormula::Atom(name) => write!(f, "{name}"),
            LtlFormula::Not(inner) => write!(f, "!({inner})"),
            LtlFormula::And(l, r) => write!(f, "({l} && {r})"),
            LtlFormula::Or(l, r) => write!(f, "({l} || {r})"),
            LtlFormula::Next(inner) => write!(f, "X({inner})"),
            LtlFormula::Until(l, r) => write!(f, "({l} U {r})"),
            LtlFormula::Eventually(inner) => write!(f, "F({inner})"),
            LtlFormula::Always(inner) => write!(f, "G({inner})"),
            LtlFormula::Release(l, r) => write!(f, "({l} R {r})"),
        }
    }
}

/// Convert from the parser-oriented `crate::ltl::LtlFormula` to the
/// model-checking formula. `Implies(l, r)` is desugared to `Or(!l, r)`.
#[must_use]
pub(crate) fn from_parsed_ltl(formula: &crate::ltl::LtlFormula) -> LtlFormula {
    use crate::ltl::LtlFormula as P;
    match formula {
        P::Atomic(name) => LtlFormula::Atom(name.clone()),
        P::Not(inner) => LtlFormula::Not(Box::new(from_parsed_ltl(inner))),
        P::And(l, r) => LtlFormula::And(Box::new(from_parsed_ltl(l)), Box::new(from_parsed_ltl(r))),
        P::Or(l, r) => LtlFormula::Or(Box::new(from_parsed_ltl(l)), Box::new(from_parsed_ltl(r))),
        P::Next(inner) => LtlFormula::Next(Box::new(from_parsed_ltl(inner))),
        P::Until(l, r) => {
            LtlFormula::Until(Box::new(from_parsed_ltl(l)), Box::new(from_parsed_ltl(r)))
        }
        P::Eventually(inner) => LtlFormula::Eventually(Box::new(from_parsed_ltl(inner))),
        P::Always(inner) => LtlFormula::Always(Box::new(from_parsed_ltl(inner))),
        P::Implies(l, r) => {
            // phi -> psi  =  !phi \/ psi
            LtlFormula::Or(
                Box::new(LtlFormula::Not(Box::new(from_parsed_ltl(l)))),
                Box::new(from_parsed_ltl(r)),
            )
        }
    }
}

// ---------------------------------------------------------------------------
// Trace State
// ---------------------------------------------------------------------------

/// A single state in a finite execution trace.
///
/// Maps atomic proposition names to truth values. Propositions absent
/// from the map are treated as false.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraceState {
    values: FxHashMap<String, bool>,
}

impl TraceState {
    /// Create a new trace state from an iterator of `(name, value)` pairs.
    #[must_use]
    pub fn new(props: impl IntoIterator<Item = (String, bool)>) -> Self {
        Self { values: props.into_iter().collect() }
    }

    /// Create a trace state where the given propositions are true,
    /// all others are false.
    #[must_use]
    pub fn from_true_props(props: &[&str]) -> Self {
        Self {
            values: props.iter().map(|p| ((*p).to_string(), true)).collect(),
        }
    }

    /// Query the truth value of an atomic proposition. Missing = false.
    #[must_use]
    pub fn get(&self, prop: &str) -> bool {
        self.values.get(prop).copied().unwrap_or(false)
    }
}

// ---------------------------------------------------------------------------
// Model Check Result
// ---------------------------------------------------------------------------

/// Result of checking an LTL formula over a finite trace.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ModelCheckResult {
    /// The trace satisfies the formula.
    Satisfied,
    /// The trace violates the formula. The `usize` is the earliest
    /// position at which the violation is detected.
    Violated(usize),
    /// Insufficient information to determine satisfaction (e.g., the trace
    /// is too short for `Next` at the final position).
    Unknown,
}

impl fmt::Display for ModelCheckResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ModelCheckResult::Satisfied => write!(f, "satisfied"),
            ModelCheckResult::Violated(pos) => write!(f, "violated at position {pos}"),
            ModelCheckResult::Unknown => write!(f, "unknown (inconclusive)"),
        }
    }
}

// ---------------------------------------------------------------------------
// Batch trace checking
// ---------------------------------------------------------------------------

/// Evaluate an LTL formula over a finite trace using FLTL semantics.
///
/// Finite-trace LTL interprets:
/// - `Next` at the last position as false (no next state).
/// - `Always` as holding at all remaining positions in the trace.
/// - `Eventually` as holding at some position in the remaining trace.
/// - `Until` and `Release` follow standard semantics bounded by trace length.
///
/// Returns `Satisfied` if the formula holds at position 0, `Violated(pos)`
/// with the earliest violation position if it does not, or `Unknown` if
/// the trace is empty.
#[must_use]
pub fn check_trace(formula: &LtlFormula, trace: &[TraceState]) -> ModelCheckResult {
    if trace.is_empty() {
        return ModelCheckResult::Unknown;
    }

    // Build a table: sat[i] = true iff formula holds at position i.
    // We evaluate from the end of the trace backward.
    let satisfied = eval_at(formula, trace, 0);
    if satisfied {
        ModelCheckResult::Satisfied
    } else {
        // Find earliest violation position
        let pos = find_earliest_violation(formula, trace);
        ModelCheckResult::Violated(pos)
    }
}

/// Evaluate whether `formula` holds at position `pos` in `trace`.
fn eval_at(formula: &LtlFormula, trace: &[TraceState], pos: usize) -> bool {
    if pos >= trace.len() {
        // Past end of trace: only Always is vacuously true
        return matches!(formula, LtlFormula::Always(_) | LtlFormula::Release(_, _));
    }

    match formula {
        LtlFormula::Atom(name) => trace[pos].get(name),

        LtlFormula::Not(inner) => !eval_at(inner, trace, pos),

        LtlFormula::And(l, r) => eval_at(l, trace, pos) && eval_at(r, trace, pos),

        LtlFormula::Or(l, r) => eval_at(l, trace, pos) || eval_at(r, trace, pos),

        LtlFormula::Next(inner) => {
            if pos + 1 >= trace.len() {
                false // No next state: Next is false at end of finite trace
            } else {
                eval_at(inner, trace, pos + 1)
            }
        }

        LtlFormula::Until(phi, psi) => {
            // phi U psi: exists j >= pos s.t. psi holds at j and phi holds at all k in [pos, j)
            for j in pos..trace.len() {
                if eval_at(psi, trace, j) {
                    // Check phi holds at all positions before j
                    let phi_holds = (pos..j).all(|k| eval_at(phi, trace, k));
                    if phi_holds {
                        return true;
                    }
                }
            }
            false
        }

        LtlFormula::Eventually(inner) => {
            // F phi = true U phi
            (pos..trace.len()).any(|j| eval_at(inner, trace, j))
        }

        LtlFormula::Always(inner) => {
            // G phi: phi holds at all positions from pos to end
            (pos..trace.len()).all(|j| eval_at(inner, trace, j))
        }

        LtlFormula::Release(phi, psi) => {
            // phi R psi: psi holds at all positions until and including when
            // phi first holds, or psi holds forever.
            // Formally: forall j >= pos. (psi holds at j) or (exists k in [pos,j) s.t. phi holds at k)
            for j in pos..trace.len() {
                if !eval_at(psi, trace, j) {
                    // psi failed at j; phi must have held at some k < j
                    let phi_held = (pos..j).any(|k| eval_at(phi, trace, k));
                    if !phi_held {
                        return false;
                    }
                    return true;
                }
                if eval_at(phi, trace, j) {
                    // phi holds and psi holds here too (checked above)
                    return true;
                }
            }
            // psi held at all positions, phi never held: Release is satisfied
            true
        }
    }
}

/// Find the earliest position where the formula is violated.
fn find_earliest_violation(formula: &LtlFormula, trace: &[TraceState]) -> usize {
    for pos in 0..trace.len() {
        if !eval_at(formula, trace, pos) {
            return pos;
        }
    }
    // Should not happen if check_trace determined violation at pos 0
    0
}

// ---------------------------------------------------------------------------
// Incremental online monitoring
// ---------------------------------------------------------------------------

/// State for incremental online LTL monitoring.
///
/// The monitor processes trace states one at a time and maintains an
/// internal obligation list. After each step, it reports whether the
/// formula is definitively satisfied, violated, or still pending.
#[derive(Debug, Clone)]
pub struct MonitorState {
    formula: LtlFormula,
    trace: Vec<TraceState>,
    result: MonitorVerdict,
}

/// Three-valued monitoring verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MonitorVerdict {
    /// Formula is definitively satisfied regardless of future states.
    Satisfied,
    /// Formula is definitively violated; no future extension can fix it.
    Violated,
    /// Verdict is still pending; more states needed.
    Pending,
}

impl fmt::Display for MonitorVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MonitorVerdict::Satisfied => write!(f, "satisfied"),
            MonitorVerdict::Violated => write!(f, "violated"),
            MonitorVerdict::Pending => write!(f, "pending"),
        }
    }
}

/// Create a new online monitor for the given LTL formula.
#[must_use]
pub fn monitor(formula: &LtlFormula) -> MonitorState {
    MonitorState {
        formula: formula.clone(),
        trace: Vec::new(),
        result: MonitorVerdict::Pending,
    }
}

impl MonitorState {
    /// Feed the next trace state to the monitor and return the updated verdict.
    pub fn step(&mut self, state: TraceState) -> MonitorVerdict {
        if self.result != MonitorVerdict::Pending {
            return self.result;
        }

        self.trace.push(state);
        self.result = self.evaluate_verdict();
        self.result
    }

    /// Current verdict.
    #[must_use]
    pub fn verdict(&self) -> MonitorVerdict {
        self.result
    }

    /// Number of trace states processed so far.
    #[must_use]
    pub fn trace_len(&self) -> usize {
        self.trace.len()
    }

    /// Evaluate the three-valued verdict for the current trace prefix.
    ///
    /// A formula is definitively satisfied if it holds now and no future
    /// extension can invalidate it. It is definitively violated if no
    /// future extension can make it hold.
    fn evaluate_verdict(&self) -> MonitorVerdict {
        let holds_now = eval_at(&self.formula, &self.trace, 0);

        // Check if the formula is definitively determined
        if is_definitive_sat(&self.formula, &self.trace) {
            return MonitorVerdict::Satisfied;
        }
        if is_definitive_viol(&self.formula, &self.trace) {
            return MonitorVerdict::Violated;
        }

        // For safety properties (Always), violation is definitive
        if !holds_now
            && let LtlFormula::Always(_) = &self.formula {
                return MonitorVerdict::Violated;
            }

        // For liveness (Eventually), satisfaction is definitive
        if holds_now
            && let LtlFormula::Eventually(_) = &self.formula {
                return MonitorVerdict::Satisfied;
            }

        MonitorVerdict::Pending
    }
}

/// Check if formula satisfaction is definitive (no future extension can change it).
fn is_definitive_sat(formula: &LtlFormula, trace: &[TraceState]) -> bool {
    match formula {
        LtlFormula::Atom(_) | LtlFormula::Not(_) | LtlFormula::And(_, _) | LtlFormula::Or(_, _) => {
            // Propositional formulas are definitive at the current position
            // only if the trace is length 1 (single state, no temporal operators)
            if !has_temporal_operator(formula) {
                eval_at(formula, trace, 0)
            } else {
                false
            }
        }
        LtlFormula::Eventually(inner) => {
            // F phi: satisfied definitively once phi holds at some position
            (0..trace.len()).any(|j| eval_at(inner, trace, j))
        }
        LtlFormula::Until(_, _) => {
            // phi U psi: once psi holds (with phi holding before), definitive
            eval_at(formula, trace, 0)
        }
        _ => false,
    }
}

/// Check if formula violation is definitive (no future extension can fix it).
fn is_definitive_viol(formula: &LtlFormula, trace: &[TraceState]) -> bool {
    match formula {
        LtlFormula::Always(inner) => {
            // G phi: violated definitively once phi fails at any position
            (0..trace.len()).any(|j| !eval_at(inner, trace, j))
        }
        LtlFormula::Atom(_) | LtlFormula::Not(_) | LtlFormula::And(_, _) | LtlFormula::Or(_, _) => {
            if !has_temporal_operator(formula) {
                !eval_at(formula, trace, 0)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Check whether a formula contains any temporal operator.
fn has_temporal_operator(formula: &LtlFormula) -> bool {
    match formula {
        LtlFormula::Atom(_) => false,
        LtlFormula::Not(inner) => has_temporal_operator(inner),
        LtlFormula::And(l, r) | LtlFormula::Or(l, r) => {
            has_temporal_operator(l) || has_temporal_operator(r)
        }
        LtlFormula::Next(_)
        | LtlFormula::Until(_, _)
        | LtlFormula::Eventually(_)
        | LtlFormula::Always(_)
        | LtlFormula::Release(_, _) => true,
    }
}

// ---------------------------------------------------------------------------
// Monitoring automaton (simplified)
// ---------------------------------------------------------------------------

/// A simplified monitoring automaton state.
///
/// This is a basic representation for LTL-to-automaton conversion
/// suitable for finite-trace monitoring. Each automaton state tracks
/// which subformulas need to hold now and which obligations carry forward.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AutomatonState {
    /// Unique identifier for this automaton state.
    pub id: usize,
    /// Subformulas that must hold at the current trace position.
    pub current_obligations: Vec<LtlFormula>,
    /// Whether this state is accepting.
    pub accepting: bool,
}

/// A simplified monitoring automaton.
#[derive(Debug, Clone)]
pub struct MonitoringAutomaton {
    /// States of the automaton.
    pub states: Vec<AutomatonState>,
    /// Transitions: `(from_id, to_id)` pairs. Each transition is taken
    /// when the current trace state satisfies the `current_obligations`
    /// of the source state.
    pub transitions: Vec<(usize, usize)>,
    /// Initial state ID.
    pub initial: usize,
}

/// Convert an LTL formula to a simplified monitoring automaton.
///
/// This produces a basic two-state or three-state automaton suitable for
/// online monitoring of common patterns (safety, liveness, until).
/// Full Buchi/co-Buchi construction is not yet implemented.
#[must_use]
pub fn ltl_to_automaton(formula: &LtlFormula) -> MonitoringAutomaton {
    match formula {
        LtlFormula::Always(inner) => {
            // G(phi): monitor state checks phi at each step.
            // Two states: monitoring (0, accepting) and violated (1, not accepting).
            MonitoringAutomaton {
                states: vec![
                    AutomatonState {
                        id: 0,
                        current_obligations: vec![*inner.clone()],
                        accepting: true,
                    },
                    AutomatonState {
                        id: 1,
                        current_obligations: vec![],
                        accepting: false,
                    },
                ],
                transitions: vec![
                    (0, 0), // phi holds -> stay in monitoring
                    (0, 1), // phi fails -> move to violated
                    (1, 1), // absorbing violated state
                ],
                initial: 0,
            }
        }
        LtlFormula::Eventually(inner) => {
            // F(phi): monitor until phi holds.
            // Two states: waiting (0, not accepting) and satisfied (1, accepting).
            MonitoringAutomaton {
                states: vec![
                    AutomatonState {
                        id: 0,
                        current_obligations: vec![LtlFormula::Not(inner.clone())],
                        accepting: false,
                    },
                    AutomatonState {
                        id: 1,
                        current_obligations: vec![],
                        accepting: true,
                    },
                ],
                transitions: vec![
                    (0, 0), // phi not yet -> stay waiting
                    (0, 1), // phi holds -> move to satisfied
                    (1, 1), // absorbing satisfied state
                ],
                initial: 0,
            }
        }
        LtlFormula::Until(phi, psi) => {
            // phi U psi: three states - monitoring (0), satisfied (1), violated (2)
            MonitoringAutomaton {
                states: vec![
                    AutomatonState {
                        id: 0,
                        current_obligations: vec![
                            LtlFormula::Or(
                                Box::new(*psi.clone()),
                                phi.clone(),
                            ),
                        ],
                        accepting: false,
                    },
                    AutomatonState {
                        id: 1,
                        current_obligations: vec![],
                        accepting: true,
                    },
                    AutomatonState {
                        id: 2,
                        current_obligations: vec![],
                        accepting: false,
                    },
                ],
                transitions: vec![
                    (0, 1), // psi holds -> satisfied
                    (0, 0), // phi holds, psi not yet -> continue
                    (0, 2), // neither -> violated
                    (1, 1), // absorbing
                    (2, 2), // absorbing
                ],
                initial: 0,
            }
        }
        // Default: single-state automaton that checks the formula directly
        _ => MonitoringAutomaton {
            states: vec![AutomatonState {
                id: 0,
                current_obligations: vec![formula.clone()],
                accepting: true,
            }],
            transitions: vec![(0, 0)],
            initial: 0,
        },
    }
}

// ---------------------------------------------------------------------------
// Counterexample prefix
// ---------------------------------------------------------------------------

/// Find the shortest prefix of the trace that demonstrates a violation
/// of the formula.
///
/// Returns `None` if the full trace satisfies the formula.
/// Otherwise returns the shortest prefix `trace[0..=k]` such that the
/// formula is violated and no shorter prefix would demonstrate the violation.
#[must_use]
pub fn counterexample_prefix<'a>(
    formula: &LtlFormula,
    trace: &'a [TraceState],
) -> Option<&'a [TraceState]> {
    if trace.is_empty() {
        return None;
    }

    // Check if the full trace satisfies the formula
    if eval_at(formula, trace, 0) {
        return None;
    }

    // Find the shortest prefix that already shows the violation
    for len in 1..=trace.len() {
        let prefix = &trace[..len];
        if !eval_at(formula, prefix, 0) {
            return Some(prefix);
        }
    }

    // Full trace is the counterexample
    Some(trace)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn state(props: &[&str]) -> TraceState {
        TraceState::from_true_props(props)
    }

    fn atom(name: &str) -> LtlFormula {
        LtlFormula::Atom(name.to_string())
    }

    // ---- check_trace tests ----

    #[test]
    fn test_check_trace_atom_satisfied() {
        let trace = vec![state(&["p"]), state(&["p"]), state(&["q"])];
        let result = check_trace(&atom("p"), &trace);
        assert_eq!(result, ModelCheckResult::Satisfied);
    }

    #[test]
    fn test_check_trace_atom_violated() {
        let trace = vec![state(&["q"]), state(&["p"])];
        let result = check_trace(&atom("p"), &trace);
        assert_eq!(result, ModelCheckResult::Violated(0));
    }

    #[test]
    fn test_check_trace_empty_unknown() {
        let result = check_trace(&atom("p"), &[]);
        assert_eq!(result, ModelCheckResult::Unknown);
    }

    #[test]
    fn test_check_trace_always_satisfied() {
        let trace = vec![state(&["safe"]), state(&["safe"]), state(&["safe"])];
        let formula = LtlFormula::Always(Box::new(atom("safe")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Satisfied);
    }

    #[test]
    fn test_check_trace_always_violated() {
        let trace = vec![state(&["safe"]), state(&[]), state(&["safe"])];
        let formula = LtlFormula::Always(Box::new(atom("safe")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Violated(0));
    }

    #[test]
    fn test_check_trace_eventually_satisfied() {
        let trace = vec![state(&[]), state(&[]), state(&["goal"])];
        let formula = LtlFormula::Eventually(Box::new(atom("goal")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Satisfied);
    }

    #[test]
    fn test_check_trace_eventually_violated() {
        let trace = vec![state(&[]), state(&[]), state(&[])];
        let formula = LtlFormula::Eventually(Box::new(atom("goal")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Violated(0));
    }

    #[test]
    fn test_check_trace_next_satisfied() {
        let trace = vec![state(&[]), state(&["ready"])];
        let formula = LtlFormula::Next(Box::new(atom("ready")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Satisfied);
    }

    #[test]
    fn test_check_trace_next_at_end_violated() {
        // Next at the last position: no next state -> false
        let trace = vec![state(&["p"])];
        let formula = LtlFormula::Next(Box::new(atom("p")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Violated(0));
    }

    #[test]
    fn test_check_trace_until_satisfied() {
        let trace = vec![state(&["waiting"]), state(&["waiting"]), state(&["done"])];
        let formula = LtlFormula::Until(Box::new(atom("waiting")), Box::new(atom("done")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Satisfied);
    }

    #[test]
    fn test_check_trace_until_violated() {
        // waiting holds but done never comes
        let trace = vec![state(&["waiting"]), state(&["waiting"]), state(&["waiting"])];
        let formula = LtlFormula::Until(Box::new(atom("waiting")), Box::new(atom("done")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Violated(0));
    }

    #[test]
    fn test_check_trace_release_satisfied() {
        // p R q: q holds forever (p never holds) -> satisfied
        let trace = vec![state(&["q"]), state(&["q"]), state(&["q"])];
        let formula = LtlFormula::Release(Box::new(atom("p")), Box::new(atom("q")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Satisfied);
    }

    #[test]
    fn test_check_trace_release_with_trigger() {
        // p R q: q holds, then p triggers release at position 1
        let trace = vec![state(&["q"]), state(&["p", "q"]), state(&[])];
        let formula = LtlFormula::Release(Box::new(atom("p")), Box::new(atom("q")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Satisfied);
    }

    #[test]
    fn test_check_trace_release_violated() {
        // p R q: q fails before p holds -> violated
        let trace = vec![state(&["q"]), state(&[]), state(&["p"])];
        let formula = LtlFormula::Release(Box::new(atom("p")), Box::new(atom("q")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Violated(0));
    }

    #[test]
    fn test_check_trace_conjunction() {
        let trace = vec![state(&["a", "b"])];
        let formula = LtlFormula::And(Box::new(atom("a")), Box::new(atom("b")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Satisfied);
    }

    #[test]
    fn test_check_trace_disjunction() {
        let trace = vec![state(&["a"])];
        let formula = LtlFormula::Or(Box::new(atom("a")), Box::new(atom("b")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Satisfied);
    }

    #[test]
    fn test_check_trace_negation() {
        let trace = vec![state(&[])];
        let formula = LtlFormula::Not(Box::new(atom("error")));
        let result = check_trace(&formula, &trace);
        assert_eq!(result, ModelCheckResult::Satisfied);
    }

    // ---- monitor tests ----

    #[test]
    fn test_monitor_always_violated() {
        let formula = LtlFormula::Always(Box::new(atom("safe")));
        let mut mon = monitor(&formula);
        assert_eq!(mon.step(state(&["safe"])), MonitorVerdict::Pending);
        assert_eq!(mon.step(state(&[])), MonitorVerdict::Violated);
        // Once violated, stays violated
        assert_eq!(mon.step(state(&["safe"])), MonitorVerdict::Violated);
    }

    #[test]
    fn test_monitor_eventually_satisfied() {
        let formula = LtlFormula::Eventually(Box::new(atom("goal")));
        let mut mon = monitor(&formula);
        assert_eq!(mon.step(state(&[])), MonitorVerdict::Pending);
        assert_eq!(mon.step(state(&["goal"])), MonitorVerdict::Satisfied);
        // Once satisfied, stays satisfied
        assert_eq!(mon.step(state(&[])), MonitorVerdict::Satisfied);
    }

    #[test]
    fn test_monitor_pending_when_incomplete() {
        let formula = LtlFormula::Eventually(Box::new(atom("goal")));
        let mut mon = monitor(&formula);
        assert_eq!(mon.step(state(&[])), MonitorVerdict::Pending);
        assert_eq!(mon.step(state(&[])), MonitorVerdict::Pending);
        assert_eq!(mon.verdict(), MonitorVerdict::Pending);
        assert_eq!(mon.trace_len(), 2);
    }

    // ---- ltl_to_automaton tests ----

    #[test]
    fn test_automaton_always_structure() {
        let formula = LtlFormula::Always(Box::new(atom("safe")));
        let aut = ltl_to_automaton(&formula);
        assert_eq!(aut.states.len(), 2);
        assert_eq!(aut.initial, 0);
        assert!(aut.states[0].accepting);
        assert!(!aut.states[1].accepting);
    }

    #[test]
    fn test_automaton_eventually_structure() {
        let formula = LtlFormula::Eventually(Box::new(atom("goal")));
        let aut = ltl_to_automaton(&formula);
        assert_eq!(aut.states.len(), 2);
        assert!(!aut.states[0].accepting);
        assert!(aut.states[1].accepting);
    }

    #[test]
    fn test_automaton_until_structure() {
        let formula = LtlFormula::Until(Box::new(atom("p")), Box::new(atom("q")));
        let aut = ltl_to_automaton(&formula);
        assert_eq!(aut.states.len(), 3);
        assert!(aut.states[1].accepting); // satisfied state
        assert!(!aut.states[2].accepting); // violated state
    }

    // ---- counterexample_prefix tests ----

    #[test]
    fn test_counterexample_prefix_none_when_satisfied() {
        let trace = vec![state(&["safe"]), state(&["safe"])];
        let formula = LtlFormula::Always(Box::new(atom("safe")));
        assert!(counterexample_prefix(&formula, &trace).is_none());
    }

    #[test]
    fn test_counterexample_prefix_shortest() {
        let trace = vec![state(&["safe"]), state(&[]), state(&["safe"])];
        let formula = LtlFormula::Always(Box::new(atom("safe")));
        let prefix = counterexample_prefix(&formula, &trace).expect("should find counterexample");
        // Shortest prefix showing violation: first two states
        assert_eq!(prefix.len(), 2);
    }

    #[test]
    fn test_counterexample_prefix_immediate() {
        let trace = vec![state(&[]), state(&["p"])];
        let formula = atom("p");
        let prefix = counterexample_prefix(&formula, &trace).expect("should find counterexample");
        assert_eq!(prefix.len(), 1);
    }

    // ---- from_parsed_ltl tests ----

    #[test]
    fn test_from_parsed_ltl_implies_desugared() {
        use crate::ltl::LtlFormula as P;
        let parsed = P::Implies(
            Box::new(P::Atomic("request".into())),
            Box::new(P::Atomic("response".into())),
        );
        let mc_formula = from_parsed_ltl(&parsed);
        // Should be Or(Not(request), response)
        assert_eq!(
            mc_formula,
            LtlFormula::Or(
                Box::new(LtlFormula::Not(Box::new(atom("request")))),
                Box::new(atom("response")),
            )
        );
    }

    #[test]
    fn test_from_parsed_ltl_roundtrip() {
        use crate::ltl::LtlFormula as P;
        let parsed = P::Always(Box::new(P::Eventually(Box::new(P::Atomic("alive".into())))));
        let mc = from_parsed_ltl(&parsed);
        assert_eq!(
            mc,
            LtlFormula::Always(Box::new(LtlFormula::Eventually(Box::new(atom("alive")))))
        );
    }

    // ---- display tests ----

    #[test]
    fn test_display_formula() {
        let f = LtlFormula::Release(Box::new(atom("p")), Box::new(atom("q")));
        assert_eq!(f.to_string(), "(p R q)");
    }

    #[test]
    fn test_display_model_check_result() {
        assert_eq!(ModelCheckResult::Satisfied.to_string(), "satisfied");
        assert_eq!(ModelCheckResult::Violated(3).to_string(), "violated at position 3");
        assert_eq!(ModelCheckResult::Unknown.to_string(), "unknown (inconclusive)");
    }
}
