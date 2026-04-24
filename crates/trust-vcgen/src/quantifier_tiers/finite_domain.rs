// trust-vcgen/quantifier_tiers/finite_domain.rs: Tier 1 finite-domain detection and unrolling
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort};

// ---------------------------------------------------------------------------
// Tier 1: Finite-domain detection and unrolling
// ---------------------------------------------------------------------------

/// Try to extract a finite domain for the first binding from the formula body.
///
/// Recognises patterns like:
///   `Implies(And([Le(lo, var), Lt(var, hi)]), body)` -- from forall(i, lo..hi, ...)
///   `And([Le(lo, var), Lt(var, hi), body])` -- from exists(i, lo..hi, ...)
///
/// Returns `Some(vec![lo..hi])` if the range is statically known and within `max`.
pub(super) fn detect_finite_domain(
    bindings: &[(trust_types::Symbol, Sort)],
    body: &Formula,
    max: usize,
) -> Option<Vec<i128>> {
    if bindings.is_empty() {
        return None;
    }
    let var_name = &bindings[0].0;

    // Pattern 1: Forall desugaring -- Implies(range_guard, inner_body)
    if let Formula::Implies(guard, _) = body
        && let Some(range) = extract_range_from_guard(guard, var_name.as_str())
    {
        return range_to_domain(range.0, range.1, max);
    }

    // Pattern 2: Exists desugaring -- And([range_guard_parts..., body])
    if let Formula::And(clauses) = body
        && let Some(range) = extract_range_from_and_clauses(clauses, var_name.as_str())
    {
        return range_to_domain(range.0, range.1, max);
    }

    None
}

/// Extract (lo, hi) from a guard formula that constrains `var_name`.
fn extract_range_from_guard(guard: &Formula, var_name: &str) -> Option<(i128, i128)> {
    if let Formula::And(parts) = guard {
        return extract_range_parts(parts, var_name);
    }
    None
}

/// Extract (lo, hi) from the clauses of an And list, flattening nested Ands.
fn extract_range_from_and_clauses(clauses: &[Formula], var_name: &str) -> Option<(i128, i128)> {
    let mut flat: Vec<&Formula> = Vec::new();
    for clause in clauses {
        flatten_and_refs(clause, &mut flat);
    }
    extract_range_parts_refs(&flat, var_name)
}

/// Flatten And formulas into a flat list of references.
fn flatten_and_refs<'a>(f: &'a Formula, out: &mut Vec<&'a Formula>) {
    match f {
        Formula::And(cs) => {
            for c in cs {
                flatten_and_refs(c, out);
            }
        }
        other => out.push(other),
    }
}

/// Extract (lo, hi) from a flat list of bound constraint references.
fn extract_range_parts_refs(parts: &[&Formula], var_name: &str) -> Option<(i128, i128)> {
    let mut lo = None;
    let mut hi = None;

    for part in parts {
        extract_bound_from_atom(part, var_name, &mut lo, &mut hi);
    }

    match (lo, hi) {
        (Some(l), Some(h)) if l < h => Some((l, h)),
        _ => None,
    }
}

/// Extract (lo, hi) from a pair of bound constraints on `var_name`.
fn extract_range_parts(parts: &[Formula], var_name: &str) -> Option<(i128, i128)> {
    let refs: Vec<&Formula> = parts.iter().collect();
    extract_range_parts_refs(&refs, var_name)
}

/// Extract a bound from a single atomic formula.
fn extract_bound_from_atom(
    part: &Formula,
    var_name: &str,
    lo: &mut Option<i128>,
    hi: &mut Option<i128>,
) {
    match part {
        // Le(lo_val, var) -- lo_val <= var
        Formula::Le(a, b) => {
            if is_var(b, var_name)
                && let Some(val) = as_const(a)
            {
                *lo = Some(val);
            }
            // Le(var, hi_val) -- var <= hi_val (inclusive upper bound)
            if is_var(a, var_name)
                && let Some(val) = as_const(b)
            {
                *hi = Some(val + 1); // convert inclusive to exclusive
            }
        }
        // Lt(var, hi_val) -- var < hi_val
        Formula::Lt(a, b) => {
            if is_var(a, var_name)
                && let Some(val) = as_const(b)
            {
                *hi = Some(val);
            }
            // Lt(lo_val, var) -- lo_val < var
            if is_var(b, var_name)
                && let Some(val) = as_const(a)
            {
                *lo = Some(val + 1);
            }
        }
        // Ge(var, lo_val) -- var >= lo_val
        Formula::Ge(a, b) => {
            if is_var(a, var_name)
                && let Some(val) = as_const(b)
            {
                *lo = Some(val);
            }
            if is_var(b, var_name)
                && let Some(val) = as_const(a)
            {
                *hi = Some(val + 1);
            }
        }
        // Gt(var, lo_val) -- var > lo_val
        Formula::Gt(a, b) => {
            if is_var(a, var_name)
                && let Some(val) = as_const(b)
            {
                *lo = Some(val + 1);
            }
            if is_var(b, var_name)
                && let Some(val) = as_const(a)
            {
                *hi = Some(val);
            }
        }
        _ => {}
    }
}

/// Check whether a formula is `Var(name, _)`.
pub(super) fn is_var(f: &Formula, name: &str) -> bool {
    matches!(f, Formula::Var(n, _) if n == name)
}

/// If a formula is a constant integer, return its value.
pub(super) fn as_const(f: &Formula) -> Option<i128> {
    match f {
        Formula::Int(n) => Some(*n),
        _ => None,
    }
}

/// Convert a `[lo, hi)` range to a domain vector if within `max`.
fn range_to_domain(lo: i128, hi: i128, max: usize) -> Option<Vec<i128>> {
    let count = hi.saturating_sub(lo);
    if count <= 0 || count as usize > max {
        return None;
    }
    Some((lo..hi).collect())
}

/// Substitute all occurrences of `Var(var_name, _)` with `replacement` in `formula`.
#[must_use]
pub fn substitute(formula: &Formula, var_name: &str, replacement: &Formula) -> Formula {
    match formula {
        Formula::Var(name, _) if name == var_name => replacement.clone(),
        Formula::Var(..) | Formula::Bool(_) | Formula::Int(_) | Formula::BitVec { .. } => {
            formula.clone()
        }
        Formula::Not(inner) => Formula::Not(Box::new(substitute(inner, var_name, replacement))),
        Formula::And(cs) => {
            Formula::And(cs.iter().map(|c| substitute(c, var_name, replacement)).collect())
        }
        Formula::Or(cs) => {
            Formula::Or(cs.iter().map(|c| substitute(c, var_name, replacement)).collect())
        }
        Formula::Implies(a, b) => Formula::Implies(
            Box::new(substitute(a, var_name, replacement)),
            Box::new(substitute(b, var_name, replacement)),
        ),
        Formula::Eq(a, b) => Formula::Eq(
            Box::new(substitute(a, var_name, replacement)),
            Box::new(substitute(b, var_name, replacement)),
        ),
        Formula::Lt(a, b) => Formula::Lt(
            Box::new(substitute(a, var_name, replacement)),
            Box::new(substitute(b, var_name, replacement)),
        ),
        Formula::Le(a, b) => Formula::Le(
            Box::new(substitute(a, var_name, replacement)),
            Box::new(substitute(b, var_name, replacement)),
        ),
        Formula::Gt(a, b) => Formula::Gt(
            Box::new(substitute(a, var_name, replacement)),
            Box::new(substitute(b, var_name, replacement)),
        ),
        Formula::Ge(a, b) => Formula::Ge(
            Box::new(substitute(a, var_name, replacement)),
            Box::new(substitute(b, var_name, replacement)),
        ),
        Formula::Add(a, b) => Formula::Add(
            Box::new(substitute(a, var_name, replacement)),
            Box::new(substitute(b, var_name, replacement)),
        ),
        Formula::Sub(a, b) => Formula::Sub(
            Box::new(substitute(a, var_name, replacement)),
            Box::new(substitute(b, var_name, replacement)),
        ),
        Formula::Mul(a, b) => Formula::Mul(
            Box::new(substitute(a, var_name, replacement)),
            Box::new(substitute(b, var_name, replacement)),
        ),
        Formula::Div(a, b) => Formula::Div(
            Box::new(substitute(a, var_name, replacement)),
            Box::new(substitute(b, var_name, replacement)),
        ),
        Formula::Rem(a, b) => Formula::Rem(
            Box::new(substitute(a, var_name, replacement)),
            Box::new(substitute(b, var_name, replacement)),
        ),
        Formula::Neg(inner) => Formula::Neg(Box::new(substitute(inner, var_name, replacement))),
        Formula::Ite(c, t, e) => Formula::Ite(
            Box::new(substitute(c, var_name, replacement)),
            Box::new(substitute(t, var_name, replacement)),
            Box::new(substitute(e, var_name, replacement)),
        ),
        Formula::Select(a, i) => Formula::Select(
            Box::new(substitute(a, var_name, replacement)),
            Box::new(substitute(i, var_name, replacement)),
        ),
        Formula::Store(a, i, v) => Formula::Store(
            Box::new(substitute(a, var_name, replacement)),
            Box::new(substitute(i, var_name, replacement)),
            Box::new(substitute(v, var_name, replacement)),
        ),
        // Quantifiers: do NOT substitute if the var is rebound.
        Formula::Forall(bindings, body) => {
            if bindings.iter().any(|(n, _)| n == var_name) {
                formula.clone()
            } else {
                Formula::Forall(bindings.clone(), Box::new(substitute(body, var_name, replacement)))
            }
        }
        Formula::Exists(bindings, body) => {
            if bindings.iter().any(|(n, _)| n == var_name) {
                formula.clone()
            } else {
                Formula::Exists(bindings.clone(), Box::new(substitute(body, var_name, replacement)))
            }
        }
        // Bitvector operations -- pass through (no variables inside width params)
        _ => formula.clone(),
    }
}

/// Unroll `forall([binding], body)` over a finite domain.
pub(super) fn unroll_forall(
    bindings: &[(trust_types::Symbol, Sort)],
    body: &Formula,
    domain: &[i128],
) -> Formula {
    if bindings.is_empty() || domain.is_empty() {
        return Formula::Bool(true);
    }

    let var_name = &bindings[0].0;
    let remaining_bindings = &bindings[1..];

    let conjuncts: Vec<Formula> = domain
        .iter()
        .map(|&val| {
            let replaced = substitute(body, var_name.as_str(), &Formula::Int(val));
            if remaining_bindings.is_empty() {
                replaced
            } else {
                Formula::Forall(remaining_bindings.to_vec(), Box::new(replaced))
            }
        })
        .collect();

    if conjuncts.len() == 1 {
        conjuncts.into_iter().next().unwrap_or(Formula::Bool(true))
    } else {
        Formula::And(conjuncts)
    }
}

/// Unroll `exists([binding], body)` over a finite domain.
pub(super) fn unroll_exists(
    bindings: &[(trust_types::Symbol, Sort)],
    body: &Formula,
    domain: &[i128],
) -> Formula {
    if bindings.is_empty() || domain.is_empty() {
        return Formula::Bool(false);
    }

    let var_name = &bindings[0].0;
    let remaining_bindings = &bindings[1..];

    let disjuncts: Vec<Formula> = domain
        .iter()
        .map(|&val| {
            let replaced = substitute(body, var_name.as_str(), &Formula::Int(val));
            if remaining_bindings.is_empty() {
                replaced
            } else {
                Formula::Exists(remaining_bindings.to_vec(), Box::new(replaced))
            }
        })
        .collect();

    if disjuncts.len() == 1 {
        disjuncts.into_iter().next().unwrap_or(Formula::Bool(false))
    } else {
        Formula::Or(disjuncts)
    }
}
