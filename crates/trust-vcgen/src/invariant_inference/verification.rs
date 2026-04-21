// Invariant verification: initiation and consecution checks.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;

use trust_types::*;

use crate::abstract_interp::{self, AbstractDomain, Interval, IntervalDomain};
use crate::loop_analysis::LoopInfo;

use super::InvariantCandidate;

/// Result of verifying a candidate invariant against a loop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum InvariantStatus {
    /// Invariant passes both initiation and consecution checks.
    Verified,
    /// Invariant does not hold at loop entry (initiation check failed).
    InitFailed,
    /// Invariant holds at entry but is not preserved by the loop body (consecution failed).
    ConsecutionFailed,
    /// Could not determine status (e.g., solver timeout or unsupported formula).
    Unknown,
}

/// Verify a candidate invariant against a loop.
///
/// Checks two conditions:
/// 1. **Initiation**: The invariant holds when the loop is first entered.
///    Evaluates the invariant under the initial abstract state (pre-loop assignments).
/// 2. **Consecution**: If the invariant holds at the loop header, it still holds
///    after executing the loop body once.
///
/// Uses abstract interpretation (interval domain) for both checks.
#[must_use]
pub(crate) fn verify_invariant(
    candidate: &InvariantCandidate,
    loop_info: &LoopInfo,
    func: &VerifiableFunction,
) -> InvariantStatus {
    // Build initial abstract state from pre-loop assignments.
    let init_state = build_pre_loop_state(func, loop_info);

    // Check initiation: does the invariant hold under the initial state?
    if !eval_formula_in_state(&candidate.expression, &init_state) {
        return InvariantStatus::InitFailed;
    }

    // Check consecution: assuming invariant holds at header, does it hold after body?
    let header_state = build_header_state(func, loop_info, &candidate.expression);

    // Apply transfer functions for all statements in loop body blocks.
    let post_state = apply_loop_body(func, loop_info, &header_state);

    // Check if invariant still holds in post-state.
    if !eval_formula_in_state(&candidate.expression, &post_state) {
        return InvariantStatus::ConsecutionFailed;
    }

    InvariantStatus::Verified
}

/// Build an abstract state representing variable values before the loop.
fn build_pre_loop_state(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> IntervalDomain {
    let mut state = IntervalDomain::top();

    for block in &func.body.blocks {
        if block.id.0 >= loop_info.header.0 {
            break;
        }
        for stmt in &block.stmts {
            state = abstract_interp::transfer_function(stmt, func, &state);
        }
    }

    state
}

/// Build a state at the loop header that respects the invariant's constraints.
fn build_header_state(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    invariant: &Formula,
) -> IntervalDomain {
    let mut state = build_pre_loop_state(func, loop_info);
    apply_formula_constraint(&mut state, invariant);
    state
}

/// Narrow a state based on a formula constraint.
fn apply_formula_constraint(state: &mut IntervalDomain, formula: &Formula) {
    match formula {
        Formula::Ge(lhs, rhs) => {
            if let (Formula::Var(name, _), Formula::Int(c)) = (lhs.as_ref(), rhs.as_ref()) {
                let current = state.get(name);
                let narrowed = current.meet(&Interval::new(*c, i128::MAX));
                if !narrowed.is_bottom() {
                    state.set(name.clone(), narrowed);
                }
            }
        }
        Formula::Le(lhs, rhs) => {
            if let (Formula::Var(name, _), Formula::Int(c)) = (lhs.as_ref(), rhs.as_ref()) {
                let current = state.get(name);
                let narrowed = current.meet(&Interval::new(i128::MIN, *c));
                if !narrowed.is_bottom() {
                    state.set(name.clone(), narrowed);
                }
            }
            if let (Formula::Int(c), Formula::Var(name, _)) = (lhs.as_ref(), rhs.as_ref()) {
                let current = state.get(name);
                let narrowed = current.meet(&Interval::new(*c, i128::MAX));
                if !narrowed.is_bottom() {
                    state.set(name.clone(), narrowed);
                }
            }
        }
        Formula::Lt(lhs, rhs) => {
            if let (Formula::Var(name, _), Formula::Int(c)) = (lhs.as_ref(), rhs.as_ref())
                && let Some(upper) = c.checked_sub(1) {
                    let current = state.get(name);
                    let narrowed = current.meet(&Interval::new(i128::MIN, upper));
                    if !narrowed.is_bottom() {
                        state.set(name.clone(), narrowed);
                    }
                }
        }
        Formula::And(parts) => {
            for part in parts {
                apply_formula_constraint(state, part);
            }
        }
        _ => {}
    }
}

/// Apply the loop body's transfer functions to an abstract state.
fn apply_loop_body(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    state: &IntervalDomain,
) -> IntervalDomain {
    let body_set: FxHashSet<usize> = loop_info.body_blocks.iter().map(|b| b.0).collect();
    let mut current = state.clone();

    for block in &func.body.blocks {
        if !body_set.contains(&block.id.0) {
            continue;
        }
        if block.id == loop_info.header {
            continue;
        }
        for stmt in &block.stmts {
            current = abstract_interp::transfer_function(stmt, func, &current);
        }
    }

    current
}

/// Evaluate whether a formula is satisfied by an abstract state.
///
/// Conservative: returns true if the interval analysis cannot disprove it.
pub(super) fn eval_formula_in_state(formula: &Formula, state: &IntervalDomain) -> bool {
    match formula {
        Formula::Ge(lhs, rhs) => {
            if let (Formula::Var(name, _), Formula::Int(c)) = (lhs.as_ref(), rhs.as_ref()) {
                let interval = state.get(name);
                return !interval.is_bottom() && interval.hi >= *c;
            }
            true
        }
        Formula::Le(lhs, rhs) => {
            if let (Formula::Var(name, _), Formula::Int(c)) = (lhs.as_ref(), rhs.as_ref()) {
                let interval = state.get(name);
                return !interval.is_bottom() && interval.lo <= *c;
            }
            if let (Formula::Int(c), Formula::Var(name, _)) = (lhs.as_ref(), rhs.as_ref()) {
                let interval = state.get(name);
                return !interval.is_bottom() && interval.hi >= *c;
            }
            true
        }
        Formula::Lt(lhs, rhs) => {
            if let (Formula::Var(name, _), Formula::Int(c)) = (lhs.as_ref(), rhs.as_ref()) {
                let interval = state.get(name);
                return !interval.is_bottom() && interval.lo < *c;
            }
            true
        }
        Formula::And(parts) => parts.iter().all(|p| eval_formula_in_state(p, state)),
        Formula::Or(parts) => parts.iter().any(|p| eval_formula_in_state(p, state)),
        Formula::Bool(b) => *b,
        _ => true,
    }
}
