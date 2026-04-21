// trust-cegar: IC3 structural satisfiability checking
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::Formula;

use super::types::Cube;

/// Result of a satisfiability check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatResult {
    /// The formula is satisfiable. Contains a satisfying assignment (cube).
    Sat(Option<Cube>),
    /// The formula is unsatisfiable.
    Unsat,
}

/// Check satisfiability of a formula using structural analysis.
///
/// This implements a conservative SAT check without invoking an external solver:
/// - Returns `Unsat` when the formula simplifies to `false`.
/// - Returns `Sat` when the formula simplifies to `true` or is a non-trivial
///   conjunction/disjunction that can be evaluated.
/// - For formulas that cannot be decided structurally, returns `Sat(None)` as
///   a conservative over-approximation (treats unknown as satisfiable).
///
/// The key correctness property: if this returns `Unsat`, the formula is truly
/// unsatisfiable. It may return `Sat` for unsatisfiable formulas (conservative).
///
/// # Approximation hierarchy (#376)
///
/// `Unsat` -- **reliable**: the formula is definitively unsatisfiable.
/// `Sat(Some(model))` -- **reliable**: the formula is satisfiable with the given model.
/// `Sat(None)` -- **unknown**: structural analysis could not decide. Treated as
///   satisfiable for soundness (over-approximation), but the formula may actually
///   be unsatisfiable. All IC3 operations that depend on a SAT result must handle
///   this case conservatively.
///
/// **Limitation (#376):** Uses structural analysis only, not full SMT queries.
/// This limits IC3 to trivial/boolean-simplifiable formulas. When z4 SMT
/// integration is complete, all call sites will gain full SMT-level reasoning.
pub(crate) fn structural_sat_check(formula: &Formula) -> SatResult {
    match simplify_formula(formula) {
        Formula::Bool(false) => SatResult::Unsat,
        Formula::Bool(true) => SatResult::Sat(None),
        ref simplified => {
            // Check for obvious contradictions in conjunctions.
            if let Some(conjuncts) = flatten_and(simplified)
                && has_contradiction(&conjuncts)
            {
                return SatResult::Unsat;
            }
            // Conservative: treat non-trivial formulas as satisfiable.
            SatResult::Sat(None)
        }
    }
}

/// Simplify a formula by evaluating boolean constants.
pub(super) fn simplify_formula(formula: &Formula) -> Formula {
    match formula {
        Formula::Bool(b) => Formula::Bool(*b),
        Formula::Not(inner) => {
            let s = simplify_formula(inner);
            match s {
                Formula::Bool(b) => Formula::Bool(!b),
                other => Formula::Not(Box::new(other)),
            }
        }
        Formula::And(children) => {
            let simplified: Vec<Formula> = children.iter().map(simplify_formula).collect();
            // Short-circuit: any false makes the whole conjunction false.
            if simplified.contains(&Formula::Bool(false)) {
                return Formula::Bool(false);
            }
            // Remove trivially-true conjuncts.
            let non_trivial: Vec<Formula> =
                simplified.into_iter().filter(|f| *f != Formula::Bool(true)).collect();
            match non_trivial.len() {
                0 => Formula::Bool(true),
                1 => non_trivial.into_iter().next().expect("checked len == 1"),
                _ => Formula::And(non_trivial),
            }
        }
        Formula::Or(children) => {
            let simplified: Vec<Formula> = children.iter().map(simplify_formula).collect();
            // Short-circuit: any true makes the whole disjunction true.
            if simplified.contains(&Formula::Bool(true)) {
                return Formula::Bool(true);
            }
            // Remove trivially-false disjuncts.
            let non_trivial: Vec<Formula> =
                simplified.into_iter().filter(|f| *f != Formula::Bool(false)).collect();
            match non_trivial.len() {
                0 => Formula::Bool(false),
                1 => non_trivial.into_iter().next().expect("checked len == 1"),
                _ => Formula::Or(non_trivial),
            }
        }
        Formula::Implies(a, b) => {
            let sa = simplify_formula(a);
            let sb = simplify_formula(b);
            match (&sa, &sb) {
                (Formula::Bool(false), _) => Formula::Bool(true),
                (_, Formula::Bool(true)) => Formula::Bool(true),
                (Formula::Bool(true), _) => sb,
                _ => Formula::Implies(Box::new(sa), Box::new(sb)),
            }
        }
        // All other formulas are returned as-is.
        other => other.clone(),
    }
}

/// Flatten a conjunction into a list of conjuncts.
fn flatten_and(formula: &Formula) -> Option<Vec<&Formula>> {
    match formula {
        Formula::And(children) => {
            let mut result = Vec::new();
            for c in children {
                if let Some(inner) = flatten_and(c) {
                    result.extend(inner);
                } else {
                    result.push(c);
                }
            }
            Some(result)
        }
        _ => None,
    }
}

/// Check if a list of conjuncts contains a direct contradiction (p and !p).
fn has_contradiction(conjuncts: &[&Formula]) -> bool {
    for (i, a) in conjuncts.iter().enumerate() {
        for b in conjuncts.iter().skip(i + 1) {
            if is_negation_of(a, b) {
                return true;
            }
        }
    }
    false
}

/// Check if two formulas are negations of each other.
fn is_negation_of(a: &Formula, b: &Formula) -> bool {
    match (a, b) {
        (Formula::Not(inner), other) | (other, Formula::Not(inner)) => **inner == *other,
        _ => false,
    }
}
