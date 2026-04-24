// trust-cegar: Interval abstraction for CEGAR numeric refinement
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::predicate::{CmpOp, Predicate};

/// Tracks numeric intervals for variables, used in the combined
/// `RustAbstractionDomain` for Rust-specific CEGAR refinement.
///
/// This is separate from `TypeAbstraction` because it tracks dynamically
/// discovered intervals from counterexample refinement, not static type bounds.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntervalAbstraction {
    /// Per-variable intervals: variable -> (lower bound, upper bound).
    intervals: BTreeMap<String, (i128, i128)>,
}

impl IntervalAbstraction {
    /// Create an empty interval abstraction.
    #[must_use]
    pub fn new() -> Self {
        Self { intervals: BTreeMap::new() }
    }

    /// Set the interval for a variable.
    pub fn set_interval(&mut self, var: impl Into<String>, lo: i128, hi: i128) {
        self.intervals.insert(var.into(), (lo, hi));
    }

    /// Get the interval for a variable.
    #[must_use]
    pub fn get_interval(&self, var: &str) -> Option<(i128, i128)> {
        self.intervals.get(var).copied()
    }

    /// Check if a value is within the variable's interval.
    #[must_use]
    pub fn contains_value(&self, var: &str, value: i128) -> bool {
        self.intervals.get(var).is_none_or(|(lo, hi)| value >= *lo && value <= *hi)
    }

    /// Refine (narrow) an interval based on a counterexample value.
    #[must_use]
    pub fn refine_from_cex(&mut self, var: &str, cex_value: i128) -> Vec<Predicate> {
        let mut new_preds = Vec::new();

        match self.intervals.get(var).copied() {
            Some((lo, hi)) => {
                if cex_value >= lo && cex_value <= hi {
                    if cex_value > lo {
                        new_preds.push(Predicate::comparison(
                            var,
                            CmpOp::Lt,
                            cex_value.to_string(),
                        ));
                    }
                    if cex_value < hi {
                        new_preds.push(Predicate::comparison(
                            var,
                            CmpOp::Gt,
                            cex_value.to_string(),
                        ));
                    }
                }
                new_preds.push(Predicate::range(var, lo, hi));
            }
            None => {
                new_preds.push(Predicate::comparison(var, CmpOp::Ge, (cex_value + 1).to_string()));
                new_preds.push(Predicate::comparison(var, CmpOp::Le, (cex_value - 1).to_string()));
            }
        }

        new_preds
    }

    /// Number of tracked intervals.
    #[must_use]
    pub fn len(&self) -> usize {
        self.intervals.len()
    }

    /// Whether no intervals are tracked.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.intervals.is_empty()
    }

    /// Join two interval abstractions at a merge point.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let mut result = BTreeMap::new();
        for (var, (lo_a, hi_a)) in &self.intervals {
            if let Some((lo_b, hi_b)) = other.intervals.get(var) {
                result.insert(var.clone(), ((*lo_a).min(*lo_b), (*hi_a).max(*hi_b)));
            }
        }
        Self { intervals: result }
    }

    /// Meet two interval abstractions (conjunction).
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        let mut result = self.intervals.clone();
        for (var, (lo_b, hi_b)) in &other.intervals {
            result
                .entry(var.clone())
                .and_modify(|(lo_a, hi_a)| {
                    *lo_a = (*lo_a).max(*lo_b);
                    *hi_a = (*hi_a).min(*hi_b);
                })
                .or_insert((*lo_b, *hi_b));
        }
        Self { intervals: result }
    }

    /// Generate predicates from all tracked intervals.
    #[must_use]
    pub fn to_predicates(&self) -> Vec<Predicate> {
        self.intervals.iter().map(|(var, (lo, hi))| Predicate::range(var, *lo, *hi)).collect()
    }
}
