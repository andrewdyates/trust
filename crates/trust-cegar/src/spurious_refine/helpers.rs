// trust-cegar: Helper functions for counterexample analysis
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{BasicBlock, Counterexample, CounterexampleValue, Formula};

use crate::predicate::{CmpOp, Predicate};

/// Check if a counterexample's values contradict a predicate.
pub(crate) fn cex_contradicts_predicate(cex: &Counterexample, pred: &Predicate) -> bool {
    match pred {
        Predicate::Comparison { lhs, op, rhs } => {
            let lhs_val = cex_lookup_int(cex, lhs);
            let rhs_val = cex_lookup_int(cex, rhs);
            match (lhs_val, rhs_val) {
                (Some(l), Some(r)) => {
                    let holds = match op {
                        CmpOp::Lt => l < r,
                        CmpOp::Le => l <= r,
                        CmpOp::Gt => l > r,
                        CmpOp::Ge => l >= r,
                        CmpOp::Eq => l == r,
                        CmpOp::Ne => l != r,
                    };
                    !holds
                }
                _ => false,
            }
        }
        Predicate::Range { var, lo, hi } => {
            if let Some(val) = cex_lookup_int(cex, var) {
                val < *lo || val > *hi
            } else {
                false
            }
        }
        Predicate::NonNull(_) | Predicate::Custom(_) => false,
    }
}

/// Look up an integer value in the counterexample, or parse as a literal.
pub(crate) fn cex_lookup_int(cex: &Counterexample, name: &str) -> Option<i128> {
    for (var, val) in &cex.assignments {
        if var == name {
            return match val {
                CounterexampleValue::Int(n) => Some(*n),
                CounterexampleValue::Uint(n) => i128::try_from(*n).ok(),
                CounterexampleValue::Bool(b) => Some(i128::from(*b)),
                _ => None,
            };
        }
    }
    name.parse::<i128>().ok()
}

/// Convert a counterexample value to a formula equality constraint.
pub(crate) fn cex_value_to_formula(name: &str, value: &CounterexampleValue) -> Option<Formula> {
    let var = Formula::Var(name.to_string(), trust_types::Sort::Int);
    let val_formula = match value {
        CounterexampleValue::Int(n) => Formula::Int(*n),
        CounterexampleValue::Uint(n) => i128::try_from(*n).ok().map(Formula::Int)?,
        CounterexampleValue::Bool(b) => Formula::Bool(*b),
        _ => return None,
    };
    Some(Formula::Eq(Box::new(var), Box::new(val_formula)))
}

/// Extract a constraint formula from a block's terminator.
pub(crate) fn block_constraint_formula(block: &BasicBlock) -> Option<Formula> {
    if let trust_types::Terminator::Assert { cond, expected, .. } = &block.terminator
        && let Some(cond_formula) = operand_to_formula(cond)
    {
        let constraint =
            if *expected { cond_formula } else { Formula::Not(Box::new(cond_formula)) };
        return Some(constraint);
    }
    None
}

/// Convert an operand to a formula.
fn operand_to_formula(operand: &trust_types::Operand) -> Option<Formula> {
    match operand {
        trust_types::Operand::Copy(place) | trust_types::Operand::Move(place) => {
            if place.projections.is_empty() {
                Some(Formula::Var(format!("_local{}", place.local), trust_types::Sort::Int))
            } else {
                None
            }
        }
        trust_types::Operand::Constant(cv) => match cv {
            trust_types::ConstValue::Bool(b) => Some(Formula::Bool(*b)),
            trust_types::ConstValue::Int(n) => Some(Formula::Int(*n)),
            trust_types::ConstValue::Uint(n, _) => i128::try_from(*n).ok().map(Formula::Int),
            _ => None,
        },
        _ => None,
    }
}

/// Build a path formula from a counterexample and block constraints.
pub(crate) fn build_cex_path_formula(cex: &Counterexample, blocks: &[BasicBlock]) -> Formula {
    let mut conjuncts = Vec::new();

    for (name, value) in &cex.assignments {
        if let Some(f) = cex_value_to_formula(name, value) {
            conjuncts.push(f);
        }
    }

    for block in blocks {
        if let Some(f) = block_constraint_formula(block) {
            conjuncts.push(f);
        }
    }

    match conjuncts.len() {
        0 => Formula::Bool(true),
        1 => conjuncts.into_iter().next().expect("checked len == 1"),
        _ => Formula::And(conjuncts),
    }
}

/// Check if a formula is trivially unsatisfiable.
///
/// Conservative: only detects `false`, `And([..., false, ...])`, and
/// direct contradictions `p /\ !p`.
pub(crate) fn is_trivially_unsat(formula: &Formula) -> bool {
    match formula {
        Formula::Bool(false) => true,
        Formula::And(conjuncts) => {
            // Any conjunct being false makes the whole thing unsat.
            if conjuncts.contains(&Formula::Bool(false)) {
                return true;
            }
            // Check for p /\ !p.
            for c in conjuncts {
                if let Formula::Not(inner) = c
                    && conjuncts.contains(inner)
                {
                    return true;
                }
            }
            false
        }
        Formula::Not(inner) => **inner == Formula::Bool(true),
        _ => false,
    }
}

/// Find the block index that contributes an unsatisfiable constraint.
pub(crate) fn find_unsat_block(cex: &Counterexample, blocks: &[BasicBlock]) -> usize {
    for (i, block) in blocks.iter().enumerate() {
        if let Some(f) = block_constraint_formula(block)
            && is_trivially_unsat(&f)
        {
            return i;
        }
    }
    // Default: split at the midpoint of assignments.
    cex.assignments.len() / 2
}

/// Collect all labels from path formulas for an unsat core.
pub(crate) fn collect_core_labels(
    path_a: &[(String, Formula)],
    path_b: &[(String, Formula)],
) -> Vec<String> {
    path_a.iter().chain(path_b.iter()).map(|(label, _)| label.clone()).collect()
}
