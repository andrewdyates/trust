// trust-cegar: Type abstraction for Rust-specific CEGAR path pruning
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::predicate::Predicate;

/// Rust type information used to prune infeasible paths.
///
/// Encodes:
/// - Enum discriminant values (only valid variants are reachable).
/// - Integer type bounds (e.g., u8 values are in [0, 255]).
/// - Boolean constraints (values are 0 or 1).
/// - Non-null guarantees for references.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeAbstraction {
    /// Enum discriminant constraints: variable -> set of valid discriminant values.
    enum_discriminants: BTreeMap<String, BTreeSet<i128>>,
    /// Integer range constraints from types: variable -> (min, max).
    integer_ranges: BTreeMap<String, (i128, i128)>,
    /// Variables known to be booleans (value is 0 or 1).
    booleans: BTreeSet<String>,
    /// Variables known to be non-null references.
    non_null_refs: BTreeSet<String>,
}

impl TypeAbstraction {
    /// Create an empty type abstraction.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add enum discriminant constraints for a variable.
    pub fn add_enum_discriminants(
        &mut self,
        var: impl Into<String>,
        discriminants: impl IntoIterator<Item = i128>,
    ) {
        self.enum_discriminants
            .insert(var.into(), discriminants.into_iter().collect());
    }

    /// Get valid discriminant values for a variable.
    #[must_use]
    pub fn discriminants(&self, var: &str) -> Option<&BTreeSet<i128>> {
        self.enum_discriminants.get(var)
    }

    /// Check if a discriminant value is valid for a variable.
    #[must_use]
    pub fn is_valid_discriminant(&self, var: &str, value: i128) -> bool {
        self.enum_discriminants
            .get(var)
            .is_none_or(|discs| discs.contains(&value))
    }

    /// Add integer range constraint from a Rust type.
    pub fn add_integer_range(&mut self, var: impl Into<String>, min: i128, max: i128) {
        self.integer_ranges.insert(var.into(), (min, max));
    }

    /// Get the integer range for a variable.
    #[must_use]
    pub fn integer_range(&self, var: &str) -> Option<(i128, i128)> {
        self.integer_ranges.get(var).copied()
    }

    /// Check if a value is within the type's valid range.
    #[must_use]
    pub fn is_in_range(&self, var: &str, value: i128) -> bool {
        self.integer_ranges
            .get(var)
            .is_none_or(|(min, max)| value >= *min && value <= *max)
    }

    /// Mark a variable as boolean-typed.
    pub fn add_boolean(&mut self, var: impl Into<String>) {
        self.booleans.insert(var.into());
    }

    /// Check if a variable is boolean-typed.
    #[must_use]
    pub fn is_boolean(&self, var: &str) -> bool {
        self.booleans.contains(var)
    }

    /// Mark a variable as a non-null reference.
    pub fn add_non_null_ref(&mut self, var: impl Into<String>) {
        self.non_null_refs.insert(var.into());
    }

    /// Check if a variable is a non-null reference.
    #[must_use]
    pub fn is_non_null_ref(&self, var: &str) -> bool {
        self.non_null_refs.contains(var)
    }

    /// Join two type abstractions at a merge point.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let mut enum_discriminants = BTreeMap::new();
        for (var, discs_a) in &self.enum_discriminants {
            if let Some(discs_b) = other.enum_discriminants.get(var) {
                enum_discriminants.insert(var.clone(), discs_a.union(discs_b).copied().collect());
            }
        }

        let mut integer_ranges = BTreeMap::new();
        for (var, (min_a, max_a)) in &self.integer_ranges {
            if let Some((min_b, max_b)) = other.integer_ranges.get(var) {
                integer_ranges.insert(var.clone(), ((*min_a).min(*min_b), (*max_a).max(*max_b)));
            }
        }

        let booleans = self.booleans.intersection(&other.booleans).cloned().collect();
        let non_null_refs = self.non_null_refs.intersection(&other.non_null_refs).cloned().collect();

        Self { enum_discriminants, integer_ranges, booleans, non_null_refs }
    }

    /// Meet two type abstractions (conjunction).
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        let mut enum_discriminants = self.enum_discriminants.clone();
        for (var, discs_b) in &other.enum_discriminants {
            enum_discriminants
                .entry(var.clone())
                .and_modify(|discs_a| {
                    *discs_a = discs_a.intersection(discs_b).copied().collect();
                })
                .or_insert_with(|| discs_b.clone());
        }

        let mut integer_ranges = self.integer_ranges.clone();
        for (var, (min_b, max_b)) in &other.integer_ranges {
            integer_ranges
                .entry(var.clone())
                .and_modify(|(min_a, max_a)| {
                    *min_a = (*min_a).max(*min_b);
                    *max_a = (*max_a).min(*max_b);
                })
                .or_insert((*min_b, *max_b));
        }

        let booleans = self.booleans.union(&other.booleans).cloned().collect();
        let non_null_refs = self.non_null_refs.union(&other.non_null_refs).cloned().collect();

        Self { enum_discriminants, integer_ranges, booleans, non_null_refs }
    }

    /// Generate predicates from type constraints.
    #[must_use]
    pub fn to_predicates(&self) -> Vec<Predicate> {
        let mut preds = Vec::new();

        for (var, (min, max)) in &self.integer_ranges {
            preds.push(Predicate::range(var, *min, *max));
        }

        for var in &self.booleans {
            preds.push(Predicate::range(var, 0, 1));
        }

        for var in &self.non_null_refs {
            preds.push(Predicate::NonNull(var.clone()));
        }

        for (var, discs) in &self.enum_discriminants {
            if let (Some(&min), Some(&max)) = (discs.iter().next(), discs.iter().next_back()) {
                preds.push(Predicate::range(var, min, max));
            }
        }

        preds
    }

    /// Check if a counterexample value is consistent with type constraints.
    #[must_use]
    pub fn is_consistent(&self, var: &str, value: i128) -> bool {
        if let Some((min, max)) = self.integer_ranges.get(var)
            && (value < *min || value > *max) {
                return false;
            }
        if let Some(discs) = self.enum_discriminants.get(var)
            && !discs.contains(&value) {
                return false;
            }
        if self.booleans.contains(var) && value != 0 && value != 1 {
            return false;
        }
        true
    }
}
