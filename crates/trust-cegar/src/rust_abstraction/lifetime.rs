// trust-cegar: Lifetime abstraction for Rust CEGAR refinement
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::predicate::Predicate;

/// Tracks lifetime containment (outlives) relationships as abstract predicates.
///
/// In Rust, `'a: 'b` means lifetime `'a` outlives `'b`. These relationships
/// constrain which references can be stored where, and which paths through
/// the program are feasible.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LifetimeAbstraction {
    /// Outlives relations: (longer, shorter) meaning `longer: shorter`.
    outlives: BTreeSet<(String, String)>,
    /// Variables and their associated lifetime names.
    bindings: BTreeMap<String, String>,
}

impl LifetimeAbstraction {
    /// Create an empty lifetime abstraction.
    #[must_use]
    pub fn new() -> Self {
        Self { outlives: BTreeSet::new(), bindings: BTreeMap::new() }
    }

    /// Add an outlives relation: `longer` outlives `shorter`.
    pub fn add_outlives(&mut self, longer: impl Into<String>, shorter: impl Into<String>) {
        self.outlives.insert((longer.into(), shorter.into()));
    }

    /// Check if `a` outlives `b` (directly, not transitively).
    #[must_use]
    pub fn outlives(&self, longer: &str, shorter: &str) -> bool {
        self.outlives.contains(&(longer.to_string(), shorter.to_string()))
    }

    /// Check if `a` outlives `b` transitively via the outlives chain.
    #[must_use]
    pub fn outlives_transitive(&self, longer: &str, shorter: &str) -> bool {
        if self.outlives(longer, shorter) {
            return true;
        }
        let mut visited = BTreeSet::new();
        let mut queue = vec![longer.to_string()];
        while let Some(current) = queue.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            for (l, s) in &self.outlives {
                if l == &current {
                    if s == shorter {
                        return true;
                    }
                    queue.push(s.clone());
                }
            }
        }
        false
    }

    /// Bind a variable to a lifetime name.
    pub fn bind_variable(&mut self, var: impl Into<String>, lifetime: impl Into<String>) {
        self.bindings.insert(var.into(), lifetime.into());
    }

    /// Get the lifetime bound to a variable.
    #[must_use]
    pub fn variable_lifetime(&self, var: &str) -> Option<&str> {
        self.bindings.get(var).map(String::as_str)
    }

    /// Check if a reference assignment `lhs = &rhs` is valid given lifetime constraints.
    #[must_use]
    pub fn is_valid_borrow(&self, reference_var: &str, referent_var: &str) -> bool {
        let ref_lt = match self.bindings.get(reference_var) {
            Some(lt) => lt,
            None => return true,
        };
        let referent_lt = match self.bindings.get(referent_var) {
            Some(lt) => lt,
            None => return true,
        };
        self.outlives_transitive(referent_lt, ref_lt)
    }

    /// Number of outlives relations tracked.
    #[must_use]
    pub fn num_relations(&self) -> usize {
        self.outlives.len()
    }

    /// Number of variable-lifetime bindings.
    #[must_use]
    pub fn num_bindings(&self) -> usize {
        self.bindings.len()
    }

    /// Join two lifetime abstractions at a merge point.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let outlives = self.outlives.intersection(&other.outlives).cloned().collect();
        let mut bindings = BTreeMap::new();
        for (var, lt_a) in &self.bindings {
            if let Some(lt_b) = other.bindings.get(var)
                && lt_a == lt_b {
                    bindings.insert(var.clone(), lt_a.clone());
                }
        }
        Self { outlives, bindings }
    }

    /// Meet two lifetime abstractions (conjunction).
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        let outlives = self.outlives.union(&other.outlives).cloned().collect();
        let mut bindings = self.bindings.clone();
        bindings.extend(other.bindings.iter().map(|(k, v)| (k.clone(), v.clone())));
        Self { outlives, bindings }
    }

    /// Generate predicates from lifetime constraints.
    #[must_use]
    pub fn to_predicates(&self) -> Vec<Predicate> {
        self.outlives
            .iter()
            .map(|(l, s)| Predicate::Custom(format!("{l}:outlives:{s}")))
            .collect()
    }

    /// Refine the lifetime abstraction from a spurious counterexample.
    #[must_use]
    pub fn refine_from_borrow(
        &mut self,
        reference_var: &str,
        referent_var: &str,
    ) -> Vec<Predicate> {
        let mut new_preds = Vec::new();

        let ref_lt = self.bindings.get(reference_var).cloned()
            .unwrap_or_else(|| format!("'lt_{reference_var}"));
        let referent_lt = self.bindings.get(referent_var).cloned()
            .unwrap_or_else(|| format!("'lt_{referent_var}"));

        if !self.outlives_transitive(&referent_lt, &ref_lt) {
            self.add_outlives(referent_lt.clone(), ref_lt.clone());
            new_preds.push(Predicate::Custom(format!(
                "{referent_lt}:outlives:{ref_lt}"
            )));
        }

        if !self.bindings.contains_key(reference_var) {
            self.bind_variable(reference_var, &ref_lt);
        }
        if !self.bindings.contains_key(referent_var) {
            self.bind_variable(referent_var, &referent_lt);
        }

        new_preds
    }

    /// Get all lifetime names mentioned in this abstraction.
    #[must_use]
    pub fn all_lifetimes(&self) -> BTreeSet<String> {
        let mut lifetimes = BTreeSet::new();
        for (longer, shorter) in &self.outlives {
            lifetimes.insert(longer.clone());
            lifetimes.insert(shorter.clone());
        }
        for lt in self.bindings.values() {
            lifetimes.insert(lt.clone());
        }
        lifetimes
    }

    /// Check if two variables' lifetimes are compatible for simultaneous access.
    #[must_use]
    pub fn are_compatible(&self, var_a: &str, var_b: &str) -> bool {
        let lt_a = match self.bindings.get(var_a) {
            Some(lt) => lt,
            None => return true,
        };
        let lt_b = match self.bindings.get(var_b) {
            Some(lt) => lt,
            None => return true,
        };
        if lt_a == lt_b {
            return true;
        }
        self.outlives_transitive(lt_a, lt_b) || self.outlives_transitive(lt_b, lt_a)
    }
}
