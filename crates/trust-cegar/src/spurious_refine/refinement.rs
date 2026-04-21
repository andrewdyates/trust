// trust-cegar: Refinement strategy implementations
//
// Implements the four refinement strategies: predicate, trace, interpolant,
// and Rust-semantic refinement.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

use trust_types::{Counterexample, CounterexampleValue, Formula};

use crate::error::CegarError;
use crate::interpolation::{UnsatCore, craig_interpolant};
use crate::predicate::{CmpOp, Predicate};
use crate::rust_abstraction::RustAbstractionDomain;

/// Predicate refinement: extract predicates from counterexample values.
///
/// Generates boundary predicates (x >= 0, x == val) and pairwise
/// comparisons between integer variables in the counterexample.
pub(crate) fn predicate_refine(
    cex: &Counterexample,
    existing: &[Predicate],
) -> Vec<Predicate> {
    let existing_set: BTreeSet<&Predicate> = existing.iter().collect();
    let mut new_preds = Vec::new();

    for (name, value) in &cex.assignments {
        match value {
            CounterexampleValue::Int(n) => {
                let ge_zero = Predicate::comparison(name, CmpOp::Ge, "0");
                if !existing_set.contains(&ge_zero) {
                    new_preds.push(ge_zero);
                }
                let eq_val = Predicate::comparison(name, CmpOp::Eq, n.to_string());
                if !existing_set.contains(&eq_val) {
                    new_preds.push(eq_val);
                }
                if *n < 0 {
                    let lt_zero = Predicate::comparison(name, CmpOp::Lt, "0");
                    if !existing_set.contains(&lt_zero) {
                        new_preds.push(lt_zero);
                    }
                }
            }
            CounterexampleValue::Uint(n) => {
                let eq_val = Predicate::comparison(name, CmpOp::Eq, n.to_string());
                if !existing_set.contains(&eq_val) {
                    new_preds.push(eq_val);
                }
                if *n == 0 {
                    let eq_zero = Predicate::comparison(name, CmpOp::Eq, "0");
                    if !existing_set.contains(&eq_zero) {
                        new_preds.push(eq_zero);
                    }
                } else {
                    let gt_zero = Predicate::comparison(name, CmpOp::Gt, "0");
                    if !existing_set.contains(&gt_zero) {
                        new_preds.push(gt_zero);
                    }
                }
            }
            CounterexampleValue::Bool(b) => {
                let val = if *b { "1" } else { "0" };
                let pred = Predicate::comparison(name, CmpOp::Eq, val);
                if !existing_set.contains(&pred) {
                    new_preds.push(pred);
                }
            }
            _ => {}
        }
    }

    // Pairwise comparisons between integer variables.
    let int_vars: Vec<(&String, i128)> = cex
        .assignments
        .iter()
        .filter_map(|(name, val)| match val {
            CounterexampleValue::Int(n) => Some((name, *n)),
            CounterexampleValue::Uint(n) => i128::try_from(*n).ok().map(|v| (name, v)),
            _ => None,
        })
        .collect();

    for i in 0..int_vars.len() {
        for j in (i + 1)..int_vars.len() {
            let (a_name, a_val) = &int_vars[i];
            let (b_name, b_val) = &int_vars[j];
            let op = if a_val < b_val {
                CmpOp::Lt
            } else if a_val == b_val {
                CmpOp::Eq
            } else {
                CmpOp::Gt
            };
            let pred = Predicate::comparison(*a_name, op, *b_name);
            if !existing_set.contains(&pred) {
                new_preds.push(pred);
            }
        }
    }

    new_preds
}

/// Trace refinement: walk the counterexample trace and extract predicates
/// at each step where the abstract state is imprecise.
///
/// More targeted than predicate refinement: focuses on the exact program
/// points that contribute to the spurious path.
pub(crate) fn trace_refine(
    cex: &Counterexample,
    existing: &[Predicate],
) -> Vec<Predicate> {
    let existing_set: BTreeSet<&Predicate> = existing.iter().collect();
    let mut new_preds = Vec::new();

    // For each variable in the counterexample, generate predicates that
    // capture its relationship to other variables and to boundary values.
    // This is a step-by-step analysis of the trace.
    for (i, (name, value)) in cex.assignments.iter().enumerate() {
        match value {
            CounterexampleValue::Int(n) => {
                // At this trace step, the variable has value n.
                // Generate predicates that constrain this step.
                let eq = Predicate::comparison(name, CmpOp::Eq, n.to_string());
                if !existing_set.contains(&eq) {
                    new_preds.push(eq);
                }

                // Range predicates based on sign.
                if *n >= 0 {
                    let ge_zero = Predicate::comparison(name, CmpOp::Ge, "0");
                    if !existing_set.contains(&ge_zero) {
                        new_preds.push(ge_zero);
                    }
                } else {
                    let lt_zero = Predicate::comparison(name, CmpOp::Lt, "0");
                    if !existing_set.contains(&lt_zero) {
                        new_preds.push(lt_zero);
                    }
                }

                // Ordering with next variable in trace (if exists).
                if let Some((next_name, next_val)) = cex.assignments.get(i + 1)
                    && let CounterexampleValue::Int(next_n) = next_val {
                        let op = if n < next_n {
                            CmpOp::Lt
                        } else if n == next_n {
                            CmpOp::Eq
                        } else {
                            CmpOp::Gt
                        };
                        let pred = Predicate::comparison(name, op, next_name);
                        if !existing_set.contains(&pred) {
                            new_preds.push(pred);
                        }
                    }
            }
            CounterexampleValue::Uint(n) => {
                let eq = Predicate::comparison(name, CmpOp::Eq, n.to_string());
                if !existing_set.contains(&eq) {
                    new_preds.push(eq);
                }
            }
            CounterexampleValue::Bool(b) => {
                let val = if *b { "1" } else { "0" };
                let pred = Predicate::comparison(name, CmpOp::Eq, val);
                if !existing_set.contains(&pred) {
                    new_preds.push(pred);
                }
            }
            _ => {}
        }
    }

    new_preds
}

/// Interpolant-based refinement: use Craig interpolation from the unsat core.
///
/// Falls back to predicate refinement if interpolation produces nothing.
pub(crate) fn interpolant_refine(
    cex: &Counterexample,
    path_a: &[(String, Formula)],
    path_b: &[(String, Formula)],
    unsat_core: &UnsatCore,
    existing: &[Predicate],
) -> Result<Vec<Predicate>, CegarError> {
    // Try Craig interpolation first.
    let mut new_preds = if !unsat_core.is_empty() {
        craig_interpolant(path_a, path_b, unsat_core).unwrap_or_default()
    } else {
        Vec::new()
    };

    // Fall back to predicate refinement if interpolation produced nothing.
    if new_preds.is_empty() {
        new_preds = predicate_refine(cex, existing);
    }

    // Filter already-known predicates.
    new_preds.retain(|p| !existing.contains(p));

    Ok(new_preds)
}

/// Rust semantic refinement: use ownership, borrowing, and lifetime semantics
/// to discover Rust-specific predicates from the counterexample.
///
/// This strategy goes beyond generic predicate extraction by leveraging the
/// `RustAbstractionDomain` to:
/// 1. Detect use-after-move and add blocking predicates
/// 2. Detect type-range violations and add type-bound predicates
/// 3. Detect aliasing rule violations and add borrow-check predicates
/// 4. Refine intervals from counterexample values
///
/// Falls back to generic predicate refinement if no Rust domain is available
/// or if Rust-specific analysis produces no new predicates.
pub(crate) fn rust_semantic_refine(
    cex: &Counterexample,
    existing: &[Predicate],
    rust_domain: Option<&RustAbstractionDomain>,
) -> Result<Vec<Predicate>, CegarError> {
    let existing_set: BTreeSet<&Predicate> = existing.iter().collect();
    let mut new_preds = Vec::new();

    if let Some(domain) = rust_domain {
        // Extract variable-value pairs from the counterexample.
        let var_values: Vec<(&str, i128)> = cex
            .assignments
            .iter()
            .filter_map(|(name, val)| match val {
                CounterexampleValue::Int(n) => Some((name.as_str(), *n)),
                CounterexampleValue::Uint(n) => {
                    i128::try_from(*n).ok().map(|v| (name.as_str(), v))
                }
                CounterexampleValue::Bool(b) => Some((name.as_str(), i128::from(*b))),
                _ => None,
            })
            .collect();

        // Phase 1: Check each variable against Rust-specific constraints.
        for &(var, value) in &var_values {
            // Use-after-move detection.
            if domain.ownership.is_moved(var) {
                let pred = Predicate::Custom(format!("{var}:moved"));
                if !existing_set.contains(&pred) {
                    new_preds.push(pred);
                }
                continue;
            }

            // Type consistency check: add range predicates for type-bound violations.
            if !domain.type_info.is_consistent(var, value) {
                if let Some((min, max)) = domain.type_info.integer_range(var) {
                    let pred = Predicate::range(var, min, max);
                    if !existing_set.contains(&pred) {
                        new_preds.push(pred);
                    }
                }
                if let Some(discs) = domain.type_info.discriminants(var)
                    && let (Some(&min), Some(&max)) =
                        (discs.iter().next(), discs.iter().next_back())
                    {
                        let pred = Predicate::range(var, min, max);
                        if !existing_set.contains(&pred) {
                            new_preds.push(pred);
                        }
                    }
                continue;
            }

            // Interval check: add interval boundary predicates.
            if !domain.intervals.contains_value(var, value)
                && let Some((lo, hi)) = domain.intervals.get_interval(var) {
                    let pred = Predicate::range(var, lo, hi);
                    if !existing_set.contains(&pred) {
                        new_preds.push(pred);
                    }
                }

            // Non-null reference check.
            if domain.type_info.is_non_null_ref(var) && value == 0 {
                let pred = Predicate::NonNull(var.to_string());
                if !existing_set.contains(&pred) {
                    new_preds.push(pred);
                }
            }
        }

        // Phase 2: Add ownership predicates for tracked variables.
        for op in &domain.ownership_predicates {
            if op.blocks_access() {
                let pred = op.to_predicate();
                if !existing_set.contains(&pred) {
                    new_preds.push(pred);
                }
            }
        }

        // Phase 3: Add borrow-check violation predicates.
        for bc in &domain.borrow_checks {
            if bc.is_violated(&domain.ownership) {
                let pred = bc.to_predicate();
                if !existing_set.contains(&pred) {
                    new_preds.push(pred);
                }
            }
        }

        // Phase 4: Add all Rust-domain seed predicates that are not yet tracked.
        for pred in domain.all_predicates() {
            if !existing_set.contains(&pred) && !new_preds.contains(&pred) {
                new_preds.push(pred);
            }
        }
    }

    // Fall back to generic predicate refinement if Rust semantics produced nothing.
    if new_preds.is_empty() {
        new_preds = predicate_refine(cex, existing);
    }

    // Filter already-known predicates.
    new_preds.retain(|p| !existing.contains(p));

    Ok(new_preds)
}
