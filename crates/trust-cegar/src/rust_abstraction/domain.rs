// trust-cegar: Combined Rust abstraction domain for CEGAR
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use trust_types::Formula;

use crate::abstraction::{AbstractDomain, bottom_sentinel, is_bottom};
use crate::predicate::{AbstractState, Predicate};

use super::borrow_check::BorrowCheckPredicate;
use super::interval::IntervalAbstraction;
use super::lifetime::LifetimeAbstraction;
use super::ownership::{OwnershipAbstraction, OwnershipPredicate, OwnershipState};
use super::type_abs::TypeAbstraction;

// ---------------------------------------------------------------------------
// Combined Rust abstraction domain
// ---------------------------------------------------------------------------

/// A combined abstract domain that integrates ownership, lifetime, type,
/// interval, and borrow-check abstractions with predicate abstraction.
///
/// This is the Rust-specific abstraction layer for the CEGAR loop. Instead
/// of relying solely on generic predicate discovery, it exploits Rust's
/// type system to:
/// 1. Start with tighter initial abstractions (type bounds, non-null refs).
/// 2. Prune infeasible counterexample paths (moved variables, invalid discriminants).
/// 3. Generate more precise predicates during refinement.
/// 4. Encode ownership/borrowing aliasing rules as first-class predicates.
/// 5. Track numeric intervals discovered through refinement.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RustAbstractionDomain {
    /// Ownership state tracking.
    pub ownership: OwnershipAbstraction,
    /// Lifetime outlives relations.
    pub lifetimes: LifetimeAbstraction,
    /// Type-based constraints.
    pub type_info: TypeAbstraction,
    /// Numeric intervals discovered through refinement (separate from type ranges).
    pub intervals: IntervalAbstraction,
    /// Borrow-check predicates encoding Rust's aliasing rules.
    pub borrow_checks: Vec<BorrowCheckPredicate>,
    /// Ownership predicates for tracked variables.
    pub ownership_predicates: Vec<OwnershipPredicate>,
}

impl RustAbstractionDomain {
    /// Create an empty Rust abstraction domain.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Collect all predicates from all sub-domains.
    #[must_use]
    pub fn all_predicates(&self) -> Vec<Predicate> {
        let mut preds = self.ownership.to_predicates();
        preds.extend(self.lifetimes.to_predicates());
        preds.extend(self.type_info.to_predicates());
        preds.extend(self.intervals.to_predicates());
        // Add borrow-check predicates.
        preds.extend(self.borrow_checks.iter().map(BorrowCheckPredicate::to_predicate));
        // Add ownership predicates.
        preds.extend(self.ownership_predicates.iter().map(OwnershipPredicate::to_predicate));
        preds
    }

    /// Check if a counterexample is infeasible due to Rust-specific constraints.
    ///
    /// Returns `true` if any of the following hold:
    /// - A variable used in the counterexample is in a Moved state.
    /// - A value violates known type constraints (integer range, discriminant).
    /// - A value is outside a tracked interval.
    /// - An ownership predicate blocks access to the variable.
    /// - A borrow-check predicate is violated.
    #[must_use]
    pub fn is_infeasible(&self, var: &str, value: i128) -> bool {
        // Use-after-move is infeasible in safe Rust.
        if self.ownership.is_moved(var) {
            return true;
        }
        // Type constraint violation.
        if !self.type_info.is_consistent(var, value) {
            return true;
        }
        // Interval constraint violation.
        if !self.intervals.contains_value(var, value) {
            return true;
        }
        // Ownership predicate blocks access.
        for op in &self.ownership_predicates {
            if op.variable() == var && op.blocks_access() {
                return true;
            }
        }
        // Borrow-check violation.
        for bc in &self.borrow_checks {
            if bc.is_violated(&self.ownership) {
                return true;
            }
        }
        false
    }

    /// Add a borrow-check predicate to the domain.
    pub fn add_borrow_check(&mut self, pred: BorrowCheckPredicate) {
        if !self.borrow_checks.contains(&pred) {
            self.borrow_checks.push(pred);
        }
    }

    /// Add an ownership predicate to the domain.
    pub fn add_ownership_predicate(&mut self, pred: OwnershipPredicate) {
        // Remove conflicting predicates for the same variable.
        self.ownership_predicates.retain(|existing| !existing.conflicts_with(&pred));
        if !self.ownership_predicates.contains(&pred) {
            self.ownership_predicates.push(pred);
        }
    }

    /// Refine the domain from a spurious counterexample.
    ///
    /// Analyzes the counterexample variables and values to discover new
    /// Rust-specific predicates that eliminate the spurious path.
    ///
    /// # Arguments
    /// * `var_values` - Variable names and their counterexample values.
    ///
    /// # Returns
    /// New predicates discovered through Rust-specific refinement.
    #[must_use]
    pub fn refine_from_counterexample(
        &mut self,
        var_values: &[(&str, i128)],
    ) -> Vec<Predicate> {
        let mut new_preds = Vec::new();

        for &(var, value) in var_values {
            // Check ownership: if variable is moved, add a blocking predicate.
            if self.ownership.is_moved(var) {
                let op = OwnershipPredicate::IsMoved(var.to_string());
                let pred = op.to_predicate();
                self.add_ownership_predicate(op);
                new_preds.push(pred);
                continue;
            }

            // Check type consistency: add type-range predicate.
            if !self.type_info.is_consistent(var, value) {
                if let Some((min, max)) = self.type_info.integer_range(var) {
                    new_preds.push(Predicate::range(var, min, max));
                }
                if let Some(discs) = self.type_info.discriminants(var)
                    && let (Some(&min), Some(&max)) = (discs.iter().next(), discs.iter().next_back()) {
                        new_preds.push(Predicate::range(var, min, max));
                    }
                continue;
            }

            // Refine intervals from the counterexample value.
            let interval_preds = self.intervals.refine_from_cex(var, value);
            new_preds.extend(interval_preds);

            // If variable is a reference, add non-null predicate.
            if self.type_info.is_non_null_ref(var) {
                new_preds.push(Predicate::NonNull(var.to_string()));
            }
        }

        // Add borrow-check violations as predicates.
        for bc in &self.borrow_checks {
            if bc.is_violated(&self.ownership) {
                new_preds.push(bc.to_predicate());
            }
        }

        new_preds
    }
}

impl AbstractDomain for RustAbstractionDomain {
    fn top(&self) -> AbstractState {
        AbstractState::top()
    }

    fn bottom(&self) -> AbstractState {
        let mut state = AbstractState::top();
        state.add(bottom_sentinel());
        state
    }

    fn join(&self, a: &AbstractState, b: &AbstractState) -> AbstractState {
        if is_bottom(a) {
            return b.clone();
        }
        if is_bottom(b) {
            return a.clone();
        }
        // Standard predicate join, then re-add Rust-specific predicates
        // that are structurally guaranteed (type bounds, non-null refs).
        let mut joined = a.join(b);
        // Type-guaranteed predicates survive all joins.
        for pred in self.type_info.to_predicates() {
            joined.add(pred);
        }
        // Interval predicates survive joins (from type info or refinement).
        for pred in self.intervals.to_predicates() {
            joined.add(pred);
        }
        // Non-null reference predicates survive joins.
        for var in &self.ownership.states {
            if *var.1 == OwnershipState::SharedBorrow || *var.1 == OwnershipState::MutableBorrow {
                joined.add(Predicate::NonNull(var.0.clone()));
            }
        }
        // Ownership predicates survive joins (type-system guaranteed).
        for op in &self.ownership_predicates {
            joined.add(op.to_predicate());
        }
        // Borrow-check predicates survive joins (aliasing rules are invariant).
        for bc in &self.borrow_checks {
            joined.add(bc.to_predicate());
        }
        joined
    }

    fn meet(&self, a: &AbstractState, b: &AbstractState) -> AbstractState {
        // Meet is union of predicates (conjunction).
        let mut met = a.meet(b);
        // Add all Rust-specific predicates.
        for pred in self.all_predicates() {
            met.add(pred);
        }
        met
    }

    fn widen(&self, prev: &AbstractState, next: &AbstractState) -> AbstractState {
        // Widening: drop non-stable predicates but keep type-guaranteed ones.
        let mut widened = self.join(prev, next);
        // Ensure type-system predicates are never dropped by widening.
        for pred in self.type_info.to_predicates() {
            widened.add(pred);
        }
        // Ownership and borrow-check predicates survive widening.
        for op in &self.ownership_predicates {
            widened.add(op.to_predicate());
        }
        for bc in &self.borrow_checks {
            widened.add(bc.to_predicate());
        }
        widened
    }

    fn narrow(&self, wide: &AbstractState, precise: &AbstractState) -> AbstractState {
        self.meet(wide, precise)
    }
}

/// Combine three abstraction sub-domains into a unified `RustAbstractionDomain`.
#[must_use]
pub fn combined_abstraction(
    ownership: &OwnershipAbstraction,
    lifetimes: &LifetimeAbstraction,
    type_info: &TypeAbstraction,
) -> RustAbstractionDomain {
    RustAbstractionDomain {
        ownership: ownership.clone(),
        lifetimes: lifetimes.clone(),
        type_info: type_info.clone(),
        intervals: IntervalAbstraction::new(),
        borrow_checks: Vec::new(),
        ownership_predicates: Vec::new(),
    }
}

/// Refine CEGAR predicates using Rust type knowledge from a counterexample.
///
/// Given a counterexample (as a slice of `Formula`) and the current Rust
/// abstraction domain, extract new predicates that exploit Rust-specific
/// invariants to rule out the spurious path.
///
/// This goes beyond generic predicate extraction by:
/// - Adding type-range predicates for variables whose CEX values are out of type bounds.
/// - Adding non-null predicates for reference variables.
/// - Adding discriminant-range predicates for enum variables.
/// - Adding ownership-state predicates for moved/borrowed variables.
#[must_use]
pub fn refine_with_rust_semantics(
    cex: &[Formula],
    domain: &RustAbstractionDomain,
) -> Vec<Predicate> {
    let mut new_preds = Vec::new();
    let mut seen = BTreeSet::new();

    // Extract variable names and values from the counterexample formulas.
    for formula in cex {
        extract_refinement_predicates(formula, domain, &mut new_preds, &mut seen);
    }

    // Add type-guaranteed predicates that are not yet tracked.
    for pred in domain.all_predicates() {
        if seen.insert(pred.clone()) {
            new_preds.push(pred);
        }
    }

    new_preds
}

/// Extract refinement predicates from a single formula node.
fn extract_refinement_predicates(
    formula: &Formula,
    domain: &RustAbstractionDomain,
    out: &mut Vec<Predicate>,
    seen: &mut BTreeSet<Predicate>,
) {
    match formula {
        Formula::Var(name, _sort) => {
            // If the variable is moved, add a moved predicate to block this path.
            if domain.ownership.is_moved(name) {
                let pred = Predicate::Custom(format!("{name}:moved"));
                if seen.insert(pred.clone()) {
                    out.push(pred);
                }
            }
            // If the variable has a type range, add the range predicate.
            if let Some((min, max)) = domain.type_info.integer_range(name) {
                let pred = Predicate::range(name, min, max);
                if seen.insert(pred.clone()) {
                    out.push(pred);
                }
            }
            // If the variable is a non-null reference, add non-null.
            if domain.type_info.is_non_null_ref(name) {
                let pred = Predicate::NonNull(name.clone());
                if seen.insert(pred.clone()) {
                    out.push(pred);
                }
            }
            // If the variable has enum discriminant constraints, add range.
            if let Some(discs) = domain.type_info.discriminants(name)
                && let (Some(&min), Some(&max)) = (discs.iter().next(), discs.iter().next_back()) {
                    let pred = Predicate::range(name, min, max);
                    if seen.insert(pred.clone()) {
                        out.push(pred);
                    }
                }
        }
        // Recurse into comparisons to find constrained variables.
        Formula::Eq(a, b) | Formula::Lt(a, b) | Formula::Le(a, b)
        | Formula::Gt(a, b) | Formula::Ge(a, b) => {
            extract_refinement_predicates(a, domain, out, seen);
            extract_refinement_predicates(b, domain, out, seen);
        }
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                extract_refinement_predicates(child, domain, out, seen);
            }
        }
        Formula::Not(inner) => {
            extract_refinement_predicates(inner, domain, out, seen);
        }
        _ => {}
    }
}
