// Octagon abstract domain: relational constraints +-x +-y <= c.
//
// Reference: Mine, "The Octagon Abstract Domain" (HOSC 2006).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

/// A constraint of the form `coeff_x * x + coeff_y * y <= constant`.
///
/// Coefficients are restricted to {-1, 0, +1} for octagonal constraints.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct OctagonConstraint {
    pub(crate) var_x: String,
    pub(crate) coeff_x: i8,
    pub(crate) var_y: String,
    pub(crate) coeff_y: i8,
    pub(crate) constant: i128,
}

/// Octagon abstract domain: conjunctions of constraints `+-x +-y <= c`.
///
/// Reference: Mine, "The Octagon Abstract Domain" (HOSC 2006).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OctagonDomain {
    pub(crate) constraints: Vec<OctagonConstraint>,
    pub(crate) is_unreachable: bool,
}

impl OctagonDomain {
    #[must_use]
    pub(crate) fn top() -> Self {
        OctagonDomain { constraints: Vec::new(), is_unreachable: false }
    }

    #[must_use]
    pub(crate) fn bottom() -> Self {
        OctagonDomain { constraints: Vec::new(), is_unreachable: true }
    }

    pub(crate) fn add_constraint(&mut self, constraint: OctagonConstraint) {
        if !self.is_unreachable {
            self.constraints.push(constraint);
        }
    }

    /// Join: keep only constraints present in both, with the weaker bound.
    #[must_use]
    pub(crate) fn join(&self, other: &Self) -> Self {
        if self.is_unreachable {
            return other.clone();
        }
        if other.is_unreachable {
            return self.clone();
        }

        let mut result = Vec::new();
        for c1 in &self.constraints {
            for c2 in &other.constraints {
                if c1.var_x == c2.var_x
                    && c1.var_y == c2.var_y
                    && c1.coeff_x == c2.coeff_x
                    && c1.coeff_y == c2.coeff_y
                {
                    result.push(OctagonConstraint {
                        var_x: c1.var_x.clone(),
                        coeff_x: c1.coeff_x,
                        var_y: c1.var_y.clone(),
                        coeff_y: c1.coeff_y,
                        constant: c1.constant.max(c2.constant),
                    });
                }
            }
        }

        OctagonDomain { constraints: result, is_unreachable: false }
    }

    /// Widen: drop constraints whose bounds increased.
    #[must_use]
    pub(crate) fn widen(&self, other: &Self) -> Self {
        if self.is_unreachable {
            return other.clone();
        }
        if other.is_unreachable {
            return self.clone();
        }

        let mut result = Vec::new();
        for c1 in &self.constraints {
            let matching = other.constraints.iter().find(|c2| {
                c1.var_x == c2.var_x
                    && c1.var_y == c2.var_y
                    && c1.coeff_x == c2.coeff_x
                    && c1.coeff_y == c2.coeff_y
            });
            if let Some(c2) = matching
                && c2.constant <= c1.constant {
                    result.push(c1.clone());
                }
        }

        OctagonDomain { constraints: result, is_unreachable: false }
    }

    /// Extract octagonal invariants as formulas.
    #[must_use]
    pub(crate) fn to_formulas(&self) -> Vec<Formula> {
        if self.is_unreachable {
            return vec![Formula::Bool(false)];
        }

        self.constraints
            .iter()
            .map(|c| {
                let x_term = match c.coeff_x {
                    1 => Formula::Var(c.var_x.clone(), Sort::Int),
                    -1 => Formula::Neg(Box::new(Formula::Var(c.var_x.clone(), Sort::Int))),
                    _ => Formula::Int(0),
                };
                let y_term = match c.coeff_y {
                    1 => Formula::Var(c.var_y.clone(), Sort::Int),
                    -1 => Formula::Neg(Box::new(Formula::Var(c.var_y.clone(), Sort::Int))),
                    _ => Formula::Int(0),
                };
                let lhs = if c.coeff_x != 0 && c.coeff_y != 0 {
                    Formula::Add(Box::new(x_term), Box::new(y_term))
                } else if c.coeff_x != 0 {
                    x_term
                } else {
                    y_term
                };
                Formula::Le(Box::new(lhs), Box::new(Formula::Int(c.constant)))
            })
            .collect()
    }

    /// Check if this domain satisfies a constraint.
    #[must_use]
    pub(crate) fn satisfies(&self, constraint: &OctagonConstraint) -> bool {
        if self.is_unreachable {
            return true;
        }
        self.constraints.iter().any(|c| {
            c.var_x == constraint.var_x
                && c.var_y == constraint.var_y
                && c.coeff_x == constraint.coeff_x
                && c.coeff_y == constraint.coeff_y
                && c.constant <= constraint.constant
        })
    }
}
