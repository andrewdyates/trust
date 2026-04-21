// trust-vcgen/abstract_domains.rs: Advanced abstract domains for VC generation
//
// Adds relational domains beyond intervals:
// - Octagons for constraints of the form +-x +-y <= c
// - Polyhedra for linear constraints of the form sum(a_i * x_i) <= b
// - Product domains for composing abstract domains pointwise
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use serde::{Deserialize, Serialize};
use trust_types::{Formula, Sort};

use crate::abstract_interp::AbstractDomain;

#[must_use]
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Sign {
    Pos,
    Neg,
}

impl Sign {
    pub const fn opposite(self) -> Self {
        match self {
            Self::Pos => Self::Neg,
            Self::Neg => Self::Pos,
        }
    }

    #[must_use]
    pub const fn prefix(self) -> &'static str {
        match self {
            Self::Pos => "",
            Self::Neg => "-",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OctagonConstraint {
    pub var_i: String,
    pub var_j: Option<String>,
    pub sign_i: Sign,
    pub sign_j: Option<Sign>,
    pub bound: i128,
}

impl OctagonConstraint {
    #[must_use]
    pub fn unary(var: impl Into<String>, sign: Sign, bound: i128) -> Self {
        Self { var_i: var.into(), var_j: None, sign_i: sign, sign_j: None, bound }
    }

    #[must_use]
    pub fn binary(
        var_i: impl Into<String>,
        sign_i: Sign,
        var_j: impl Into<String>,
        sign_j: Sign,
        bound: i128,
    ) -> Self {
        Self { var_i: var_i.into(), var_j: Some(var_j.into()), sign_i, sign_j: Some(sign_j), bound }
    }
}

impl fmt::Display for OctagonConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.sign_i.prefix(), self.var_i)?;
        if let Some(var_j) = &self.var_j {
            let sign_j = self.sign_j.unwrap_or(Sign::Pos);
            write!(
                f,
                " {} {} <= {}",
                match sign_j {
                    Sign::Pos => "+",
                    Sign::Neg => "-",
                },
                var_j,
                self.bound
            )
        } else {
            write!(f, " <= {}", self.bound)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OctagonDomain {
    pub constraints: BTreeSet<OctagonConstraint>,
    pub is_unreachable: bool,
}

impl Default for OctagonDomain {
    fn default() -> Self {
        Self::top()
    }
}

impl OctagonDomain {
    #[must_use]
    pub fn new<I>(constraints: I) -> Self
    where
        I: IntoIterator<Item = OctagonConstraint>,
    {
        Self::from_constraints(constraints)
    }

    #[must_use]
    pub fn from_constraints<I>(constraints: I) -> Self
    where
        I: IntoIterator<Item = OctagonConstraint>,
    {
        if let Some(constraints) = close_octagon_constraints(constraints) {
            Self { constraints, is_unreachable: false }
        } else {
            Self::bottom()
        }
    }

    #[must_use]
    pub fn is_top(&self) -> bool {
        !self.is_unreachable && self.constraints.is_empty()
    }

    #[must_use]
    pub fn to_formula(&self) -> Formula {
        if self.is_unreachable {
            return Formula::Bool(false);
        }
        conjoin(self.constraints.iter().map(octagon_constraint_to_formula).collect())
    }
}

impl AbstractDomain for OctagonDomain {
    fn top() -> Self {
        Self { constraints: BTreeSet::new(), is_unreachable: false }
    }

    fn bottom() -> Self {
        Self { constraints: BTreeSet::new(), is_unreachable: true }
    }

    fn join(&self, other: &Self) -> Self {
        if self.is_unreachable {
            return other.clone();
        }
        if other.is_unreachable {
            return self.clone();
        }
        let right = octagon_bounds(&other.constraints);
        Self::from_constraints(octagon_bounds(&self.constraints).into_iter().filter_map(
            |(shape, bound)| {
                right.get(&shape).map(|other_bound| shape.with_bound(bound.max(*other_bound)))
            },
        ))
    }

    fn meet(&self, other: &Self) -> Self {
        if self.is_unreachable || other.is_unreachable {
            return Self::bottom();
        }
        Self::from_constraints(
            self.constraints.iter().cloned().chain(other.constraints.iter().cloned()),
        )
    }

    fn widen(&self, other: &Self) -> Self {
        if self.is_unreachable {
            return other.clone();
        }
        if other.is_unreachable {
            return self.clone();
        }
        let right = octagon_bounds(&other.constraints);
        Self::from_constraints(octagon_bounds(&self.constraints).into_iter().filter_map(
            |(shape, bound)| match right.get(&shape) {
                Some(other_bound) if *other_bound <= bound => Some(shape.with_bound(bound)),
                _ => None,
            },
        ))
    }

    fn narrow(&self, other: &Self) -> Self {
        self.meet(other)
    }

    fn is_bottom(&self) -> bool {
        self.is_unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        if self.is_unreachable {
            return true;
        }
        if other.is_unreachable {
            return false;
        }
        let left = octagon_bounds(&self.constraints);
        octagon_bounds(&other.constraints)
            .into_iter()
            .all(|(shape, bound)| left.get(&shape).is_some_and(|own| *own <= bound))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PolyhedraConstraint {
    pub coefficients: Vec<(String, i128)>,
    pub bound: i128,
}

impl PolyhedraConstraint {
    #[must_use]
    pub fn new(coefficients: Vec<(String, i128)>, bound: i128) -> Self {
        let mut merged = BTreeMap::<String, i128>::new();
        for (var, coeff) in coefficients {
            *merged.entry(var).or_insert(0) += coeff;
        }
        Self { coefficients: merged.into_iter().filter(|(_, coeff)| *coeff != 0).collect(), bound }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PolyhedraDomain {
    pub constraints: BTreeSet<PolyhedraConstraint>,
    pub is_unreachable: bool,
}

impl Default for PolyhedraDomain {
    fn default() -> Self {
        Self::top()
    }
}

impl PolyhedraDomain {
    #[must_use]
    pub fn new<I>(constraints: I) -> Self
    where
        I: IntoIterator<Item = PolyhedraConstraint>,
    {
        Self::from_constraints(constraints)
    }

    #[must_use]
    pub fn from_constraints<I>(constraints: I) -> Self
    where
        I: IntoIterator<Item = PolyhedraConstraint>,
    {
        let mut bounds = BTreeMap::new();
        for constraint in constraints {
            let normalized = PolyhedraConstraint::new(constraint.coefficients, constraint.bound);
            if normalized.coefficients.is_empty() {
                if normalized.bound < 0 {
                    return Self::bottom();
                }
                continue;
            }
            let shape = PolyhedronShape::from(&normalized);
            bounds
                .entry(shape)
                .and_modify(|bound: &mut i128| *bound = (*bound).min(normalized.bound))
                .or_insert(normalized.bound);
        }
        let domain = Self {
            constraints: bounds.into_iter().map(|(shape, bound)| shape.with_bound(bound)).collect(),
            is_unreachable: false,
        };
        if domain.has_obvious_conflict() { Self::bottom() } else { domain }
    }

    #[must_use]
    pub fn is_top(&self) -> bool {
        !self.is_unreachable && self.constraints.is_empty()
    }

    #[must_use]
    pub fn to_formula(&self) -> Formula {
        if self.is_unreachable {
            return Formula::Bool(false);
        }
        conjoin(self.constraints.iter().map(polyhedra_constraint_to_formula).collect())
    }

    #[must_use]
    fn has_obvious_conflict(&self) -> bool {
        let mut lowers = BTreeMap::<String, i128>::new();
        let mut uppers = BTreeMap::<String, i128>::new();
        let bounds = polyhedra_bounds(&self.constraints);
        for constraint in &self.constraints {
            if let [(var, coeff)] = constraint.coefficients.as_slice() {
                if *coeff > 0 {
                    let upper = div_floor(constraint.bound, *coeff);
                    uppers
                        .entry(var.clone())
                        .and_modify(|bound| *bound = (*bound).min(upper))
                        .or_insert(upper);
                } else {
                    let lower = div_ceil(constraint.bound, *coeff);
                    lowers
                        .entry(var.clone())
                        .and_modify(|bound| *bound = (*bound).max(lower))
                        .or_insert(lower);
                }
            }
        }
        if lowers.iter().any(|(var, lower)| uppers.get(var).is_some_and(|upper| lower > upper)) {
            return true;
        }
        bounds.iter().any(|(shape, bound)| {
            let negated = shape.negated();
            bounds.get(&negated).is_some_and(|other| -*other > *bound)
        })
    }
}

impl AbstractDomain for PolyhedraDomain {
    fn top() -> Self {
        Self { constraints: BTreeSet::new(), is_unreachable: false }
    }

    fn bottom() -> Self {
        Self { constraints: BTreeSet::new(), is_unreachable: true }
    }

    fn join(&self, other: &Self) -> Self {
        if self.is_unreachable {
            return other.clone();
        }
        if other.is_unreachable {
            return self.clone();
        }
        let right = polyhedra_bounds(&other.constraints);
        Self::from_constraints(polyhedra_bounds(&self.constraints).into_iter().filter_map(
            |(shape, bound)| {
                right.get(&shape).map(|other_bound| shape.with_bound(bound.max(*other_bound)))
            },
        ))
    }

    fn meet(&self, other: &Self) -> Self {
        if self.is_unreachable || other.is_unreachable {
            return Self::bottom();
        }
        Self::from_constraints(
            self.constraints.iter().cloned().chain(other.constraints.iter().cloned()),
        )
    }

    fn widen(&self, other: &Self) -> Self {
        if self.is_unreachable {
            return other.clone();
        }
        if other.is_unreachable {
            return self.clone();
        }
        let right = polyhedra_bounds(&other.constraints);
        Self::from_constraints(polyhedra_bounds(&self.constraints).into_iter().filter_map(
            |(shape, bound)| match right.get(&shape) {
                Some(other_bound) if *other_bound <= bound => Some(shape.with_bound(bound)),
                _ => None,
            },
        ))
    }

    fn narrow(&self, other: &Self) -> Self {
        self.meet(other)
    }

    fn is_bottom(&self) -> bool {
        self.is_unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        if self.is_unreachable {
            return true;
        }
        if other.is_unreachable {
            return false;
        }
        let left = polyhedra_bounds(&self.constraints);
        polyhedra_bounds(&other.constraints)
            .into_iter()
            .all(|(shape, bound)| left.get(&shape).is_some_and(|own| *own <= bound))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DomainProduct<A, B> {
    left: A,
    right: B,
}

impl<A, B> DomainProduct<A, B> {
    #[must_use]
    pub fn new(left: A, right: B) -> Self {
        Self { left, right }
    }

    #[must_use]
    pub fn left(&self) -> &A {
        &self.left
    }

    #[must_use]
    pub fn right(&self) -> &B {
        &self.right
    }

    #[must_use]
    pub fn into_parts(self) -> (A, B) {
        (self.left, self.right)
    }
}

impl<A, B> DomainProduct<A, B>
where
    A: AbstractDomain,
    B: AbstractDomain,
{
    #[must_use]
    pub fn is_top(&self) -> bool {
        self.left == A::top() && self.right == B::top()
    }
}

impl<A, B> AbstractDomain for DomainProduct<A, B>
where
    A: AbstractDomain,
    B: AbstractDomain,
{
    fn top() -> Self {
        Self::new(A::top(), B::top())
    }

    fn bottom() -> Self {
        Self::new(A::bottom(), B::bottom())
    }

    fn join(&self, other: &Self) -> Self {
        Self::new(self.left.join(&other.left), self.right.join(&other.right))
    }

    fn meet(&self, other: &Self) -> Self {
        Self::new(self.left.meet(&other.left), self.right.meet(&other.right))
    }

    fn widen(&self, other: &Self) -> Self {
        Self::new(self.left.widen(&other.left), self.right.widen(&other.right))
    }

    fn narrow(&self, other: &Self) -> Self {
        Self::new(self.left.narrow(&other.left), self.right.narrow(&other.right))
    }

    fn is_bottom(&self) -> bool {
        self.left.is_bottom() || self.right.is_bottom()
    }

    fn leq(&self, other: &Self) -> bool {
        self.left.leq(&other.left) && self.right.leq(&other.right)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct OctagonShape(String, Option<String>, Sign, Option<Sign>);

impl OctagonShape {
    fn with_bound(&self, bound: i128) -> OctagonConstraint {
        OctagonConstraint {
            var_i: self.0.clone(),
            var_j: self.1.clone(),
            sign_i: self.2,
            sign_j: self.3,
            bound,
        }
    }
}

impl From<&OctagonConstraint> for OctagonShape {
    fn from(value: &OctagonConstraint) -> Self {
        Self(value.var_i.clone(), value.var_j.clone(), value.sign_i, value.sign_j)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct PolyhedronShape(Vec<(String, i128)>);

impl PolyhedronShape {
    fn with_bound(&self, bound: i128) -> PolyhedraConstraint {
        PolyhedraConstraint { coefficients: self.0.clone(), bound }
    }

    fn negated(&self) -> Self {
        Self(self.0.iter().map(|(var, coeff)| (var.clone(), -*coeff)).collect())
    }
}

impl From<&PolyhedraConstraint> for PolyhedronShape {
    fn from(value: &PolyhedraConstraint) -> Self {
        Self(value.coefficients.clone())
    }
}

fn octagon_bounds(constraints: &BTreeSet<OctagonConstraint>) -> BTreeMap<OctagonShape, i128> {
    constraints
        .iter()
        .map(|constraint| (OctagonShape::from(constraint), constraint.bound))
        .collect()
}

fn polyhedra_bounds(
    constraints: &BTreeSet<PolyhedraConstraint>,
) -> BTreeMap<PolyhedronShape, i128> {
    constraints
        .iter()
        .map(|constraint| (PolyhedronShape::from(constraint), constraint.bound))
        .collect()
}

fn close_octagon_constraints<I>(constraints: I) -> Option<BTreeSet<OctagonConstraint>>
where
    I: IntoIterator<Item = OctagonConstraint>,
{
    let mut vars = BTreeMap::<String, usize>::new();
    let mut normalized = Vec::new();
    for constraint in constraints {
        let Some(constraint) = normalize_octagon_constraint(constraint)? else {
            continue;
        };
        let next = vars.len();
        vars.entry(constraint.var_i.clone()).or_insert(next);
        if let Some(var_j) = &constraint.var_j {
            let next = vars.len();
            vars.entry(var_j.clone()).or_insert(next);
        }
        normalized.push(constraint);
    }
    if vars.is_empty() {
        return Some(BTreeSet::new());
    }

    let mut dist = vec![vec![None; vars.len() * 2]; vars.len() * 2];
    for (index, row) in dist.iter_mut().enumerate() {
        row[index] = Some(0);
    }
    for constraint in normalized {
        let i = octagon_index(&vars, &constraint.var_i, constraint.sign_i);
        if let Some(var_j) = &constraint.var_j {
            let sign_j = constraint.sign_j.unwrap_or(Sign::Pos);
            let j = octagon_index(&vars, var_j, sign_j);
            tighten(&mut dist[i][opposite_octagon_index(j)], constraint.bound);
            tighten(&mut dist[j][opposite_octagon_index(i)], constraint.bound);
        } else {
            tighten(&mut dist[i][opposite_octagon_index(i)], constraint.bound.saturating_mul(2));
        }
    }
    if !close_dbm(&mut dist) {
        return None;
    }

    let mut names = vec![String::new(); vars.len()];
    for (name, index) in vars {
        names[index] = name;
    }
    let mut result = BTreeMap::<OctagonShape, i128>::new();
    for (i, row) in dist.iter().enumerate() {
        for (j, bound) in row.iter().enumerate() {
            let Some(bound) = *bound else {
                continue;
            };
            if i == j {
                continue;
            }
            let (var_i, sign_i) = octagon_name(&names, i);
            let (var_j, sign_j) = octagon_name(&names, j);
            let derived = if var_i == var_j && sign_i == sign_j.opposite() {
                OctagonConstraint::unary(var_i, sign_i, bound.div_euclid(2))
            } else {
                OctagonConstraint::binary(var_i, sign_i, var_j, sign_j.opposite(), bound)
            };
            if let Some(derived) = normalize_octagon_constraint(derived)? {
                let shape = OctagonShape::from(&derived);
                result
                    .entry(shape)
                    .and_modify(|known| *known = (*known).min(derived.bound))
                    .or_insert(derived.bound);
            }
        }
    }
    Some(result.into_iter().map(|(shape, bound)| shape.with_bound(bound)).collect())
}

fn normalize_octagon_constraint(
    constraint: OctagonConstraint,
) -> Option<Option<OctagonConstraint>> {
    match constraint.var_j {
        None => Some(Some(OctagonConstraint::unary(
            constraint.var_i,
            constraint.sign_i,
            constraint.bound,
        ))),
        Some(var_j) => {
            let sign_j = constraint.sign_j.unwrap_or(Sign::Pos);
            if constraint.var_i == var_j {
                if constraint.sign_i == sign_j {
                    return Some(Some(OctagonConstraint::unary(
                        constraint.var_i,
                        constraint.sign_i,
                        constraint.bound.div_euclid(2),
                    )));
                }
                return if constraint.bound < 0 { None } else { Some(None) };
            }
            let left = (constraint.var_i.clone(), constraint.sign_i);
            let right = (var_j.clone(), sign_j);
            Some(if left <= right {
                Some(OctagonConstraint::binary(
                    constraint.var_i,
                    constraint.sign_i,
                    var_j,
                    sign_j,
                    constraint.bound,
                ))
            } else {
                Some(OctagonConstraint::binary(
                    var_j,
                    sign_j,
                    constraint.var_i,
                    constraint.sign_i,
                    constraint.bound,
                ))
            })
        }
    }
}

#[allow(clippy::needless_range_loop)]
fn close_dbm(dist: &mut [Vec<Option<i128>>]) -> bool {
    for k in 0..dist.len() {
        for i in 0..dist.len() {
            let Some(left) = dist[i][k] else {
                continue;
            };
            for j in 0..dist.len() {
                let Some(right) = dist[k][j] else {
                    continue;
                };
                tighten(&mut dist[i][j], left.saturating_add(right));
            }
        }
    }
    for i in 0..dist.len() {
        let oi = opposite_octagon_index(i);
        for j in 0..dist.len() {
            let oj = opposite_octagon_index(j);
            if let (Some(left), Some(right)) = (dist[i][oi], dist[oj][j]) {
                tighten(&mut dist[i][j], left.saturating_add(right).div_euclid(2));
            }
        }
    }
    for k in 0..dist.len() {
        for i in 0..dist.len() {
            let Some(left) = dist[i][k] else {
                continue;
            };
            for j in 0..dist.len() {
                let Some(right) = dist[k][j] else {
                    continue;
                };
                tighten(&mut dist[i][j], left.saturating_add(right));
            }
        }
    }
    dist.iter().enumerate().all(|(index, row)| row[index].unwrap_or(0) >= 0)
}

fn octagon_index(vars: &BTreeMap<String, usize>, var: &str, sign: Sign) -> usize {
    vars[var] * 2
        + match sign {
            Sign::Pos => 0,
            Sign::Neg => 1,
        }
}

fn octagon_name(vars: &[String], index: usize) -> (String, Sign) {
    (vars[index / 2].clone(), if index.is_multiple_of(2) { Sign::Pos } else { Sign::Neg })
}

const fn opposite_octagon_index(index: usize) -> usize {
    index ^ 1
}

fn tighten(slot: &mut Option<i128>, candidate: i128) {
    if match slot {
        Some(current) => candidate < *current,
        None => true,
    } {
        *slot = Some(candidate);
    }
}

fn octagon_constraint_to_formula(constraint: &OctagonConstraint) -> Formula {
    Formula::Le(
        Box::new(octagon_term(
            &constraint.var_i,
            constraint.sign_i,
            constraint.var_j.as_deref(),
            constraint.sign_j,
        )),
        Box::new(Formula::Int(constraint.bound)),
    )
}

fn octagon_term(var_i: &str, sign_i: Sign, var_j: Option<&str>, sign_j: Option<Sign>) -> Formula {
    let left = signed_var(var_i, sign_i);
    match var_j.zip(sign_j) {
        Some((var_j, sign_j)) => Formula::Add(Box::new(left), Box::new(signed_var(var_j, sign_j))),
        None => left,
    }
}

fn signed_var(var: &str, sign: Sign) -> Formula {
    let var = Formula::Var(var.to_string(), Sort::Int);
    match sign {
        Sign::Pos => var,
        Sign::Neg => Formula::Neg(Box::new(var)),
    }
}

fn polyhedra_constraint_to_formula(constraint: &PolyhedraConstraint) -> Formula {
    let mut iter = constraint.coefficients.iter().map(|(var, coeff)| linear_term(var, *coeff));
    let lhs = iter.next().map_or(Formula::Int(0), |first| {
        iter.fold(first, |acc, term| Formula::Add(Box::new(acc), Box::new(term)))
    });
    Formula::Le(Box::new(lhs), Box::new(Formula::Int(constraint.bound)))
}

fn linear_term(var: &str, coeff: i128) -> Formula {
    let var = Formula::Var(var.to_string(), Sort::Int);
    match coeff {
        1 => var,
        -1 => Formula::Neg(Box::new(var)),
        _ => Formula::Mul(Box::new(Formula::Int(coeff)), Box::new(var)),
    }
}

fn conjoin(mut formulae: Vec<Formula>) -> Formula {
    formulae.retain(|formula| *formula != Formula::Bool(true));
    match formulae.len() {
        0 => Formula::Bool(true),
        1 => formulae.pop().unwrap_or(Formula::Bool(true)),
        _ => Formula::And(formulae),
    }
}

fn div_floor(lhs: i128, rhs: i128) -> i128 {
    let quotient = lhs / rhs;
    let remainder = lhs % rhs;
    if remainder != 0 && (remainder > 0) != (rhs > 0) { quotient - 1 } else { quotient }
}

fn div_ceil(lhs: i128, rhs: i128) -> i128 {
    let quotient = lhs / rhs;
    let remainder = lhs % rhs;
    if remainder != 0 && (remainder > 0) == (rhs > 0) { quotient + 1 } else { quotient }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::abstract_interp::{Interval, IntervalDomain};

    fn interval_state(var: &str, interval: Interval) -> IntervalDomain {
        let mut state = IntervalDomain::top();
        state.set(var.to_string(), interval);
        state
    }

    #[test]
    fn test_octagon_constraint_creation_and_display() {
        let constraint = OctagonConstraint::binary("x", Sign::Pos, "y", Sign::Neg, 7);
        assert_eq!(constraint.var_i, "x");
        assert_eq!(constraint.var_j.as_deref(), Some("y"));
        assert_eq!(constraint.to_string(), "x - y <= 7");
    }

    #[test]
    fn test_octagon_domain_join_meet_widen_and_leq() {
        let left = OctagonDomain::from_constraints([
            OctagonConstraint::binary("x", Sign::Pos, "y", Sign::Neg, 3),
            OctagonConstraint::unary("x", Sign::Pos, 5),
        ]);
        let right = OctagonDomain::from_constraints([
            OctagonConstraint::binary("x", Sign::Pos, "y", Sign::Neg, 8),
            OctagonConstraint::unary("y", Sign::Pos, 4),
        ]);

        let joined = left.join(&right);
        let met = left.meet(&right);
        let widened = left.widen(&right);

        assert!(joined.constraints.contains(&OctagonConstraint::binary(
            "x",
            Sign::Pos,
            "y",
            Sign::Neg,
            8
        )));
        assert!(joined.leq(&OctagonDomain::top()));
        assert!(met.constraints.contains(&OctagonConstraint::unary("y", Sign::Pos, 4)));
        assert!(!widened.constraints.contains(&OctagonConstraint::binary(
            "x",
            Sign::Pos,
            "y",
            Sign::Neg,
            3
        )));
        assert!(met.leq(&left));
        assert!(!left.leq(&joined.meet(&right)));
    }

    #[test]
    fn test_octagon_domain_to_formula() {
        let domain = OctagonDomain::from_constraints([OctagonConstraint::binary(
            "x",
            Sign::Pos,
            "y",
            Sign::Neg,
            5,
        )]);
        assert_eq!(
            domain.to_formula(),
            Formula::Le(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Neg(Box::new(Formula::Var("y".into(), Sort::Int)))),
                )),
                Box::new(Formula::Int(5)),
            )
        );
    }

    #[test]
    fn test_octagon_domain_closure_tightens_derived_constraint() {
        let domain = OctagonDomain::from_constraints([
            OctagonConstraint::binary("x", Sign::Pos, "y", Sign::Neg, 3),
            OctagonConstraint::binary("y", Sign::Pos, "z", Sign::Neg, 4),
        ]);
        assert!(domain.constraints.contains(&OctagonConstraint::binary(
            "x",
            Sign::Pos,
            "z",
            Sign::Neg,
            7
        )));
    }

    #[test]
    fn test_polyhedra_constraint_creation_normalizes_terms() {
        let constraint =
            PolyhedraConstraint::new(vec![("y".into(), 2), ("x".into(), 1), ("y".into(), -1)], 9);
        assert_eq!(constraint.coefficients, vec![("x".into(), 1), ("y".into(), 1)]);
        assert_eq!(constraint.bound, 9);
    }

    #[test]
    fn test_polyhedra_domain_join_and_widen() {
        let left = PolyhedraDomain::from_constraints([
            PolyhedraConstraint::new(vec![("x".into(), 1)], 5),
            PolyhedraConstraint::new(vec![("x".into(), 1), ("y".into(), 1)], 9),
        ]);
        let right = PolyhedraDomain::from_constraints([
            PolyhedraConstraint::new(vec![("x".into(), 1)], 7),
            PolyhedraConstraint::new(vec![("y".into(), 1)], 4),
        ]);

        let joined = left.join(&right);
        let widened = left.widen(&right);

        assert!(joined.constraints.contains(&PolyhedraConstraint::new(vec![("x".into(), 1)], 7)));
        assert!(!joined.constraints.contains(&PolyhedraConstraint::new(vec![("y".into(), 1)], 4)));
        assert!(!widened.constraints.contains(&PolyhedraConstraint::new(vec![("x".into(), 1)], 5)));
    }

    #[test]
    fn test_polyhedra_domain_to_formula() {
        let domain = PolyhedraDomain::from_constraints([PolyhedraConstraint::new(
            vec![("x".into(), 2), ("y".into(), -1)],
            11,
        )]);
        assert_eq!(
            domain.to_formula(),
            Formula::Le(
                Box::new(Formula::Add(
                    Box::new(Formula::Mul(
                        Box::new(Formula::Int(2)),
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                    )),
                    Box::new(Formula::Neg(Box::new(Formula::Var("y".into(), Sort::Int)))),
                )),
                Box::new(Formula::Int(11)),
            )
        );
    }

    #[test]
    fn test_polyhedra_domain_detects_obvious_bottom() {
        let domain = PolyhedraDomain::from_constraints([
            PolyhedraConstraint::new(vec![("x".into(), 1)], 1),
            PolyhedraConstraint::new(vec![("x".into(), -1)], -3),
        ]);
        assert!(domain.is_bottom());
    }

    #[test]
    fn test_domain_product_combines_interval_and_octagon() {
        let product = DomainProduct::new(
            interval_state("x", Interval::new(0, 10)),
            OctagonDomain::from_constraints([OctagonConstraint::unary("x", Sign::Pos, 8)]),
        );
        assert_eq!(product.left().get("x"), Interval::new(0, 10));
        assert!(product.right().constraints.contains(&OctagonConstraint::unary("x", Sign::Pos, 8)));
    }

    #[test]
    fn test_domain_product_join_preserves_components() {
        let left = DomainProduct::new(
            interval_state("x", Interval::new(0, 5)),
            OctagonDomain::from_constraints([OctagonConstraint::unary("x", Sign::Pos, 5)]),
        );
        let right = DomainProduct::new(
            interval_state("x", Interval::new(3, 8)),
            OctagonDomain::from_constraints([OctagonConstraint::unary("x", Sign::Pos, 9)]),
        );

        let joined = left.join(&right);
        assert_eq!(joined.left().get("x"), Interval::new(0, 8));
        assert!(joined.right().constraints.contains(&OctagonConstraint::unary("x", Sign::Pos, 9)));
    }

    #[test]
    fn test_bottom_detection_for_all_domains() {
        let interval_product: DomainProduct<IntervalDomain, OctagonDomain> =
            DomainProduct::bottom();
        assert!(OctagonDomain::bottom().is_bottom());
        assert!(PolyhedraDomain::bottom().is_bottom());
        assert!(interval_product.is_bottom());
    }

    #[test]
    fn test_top_detection_for_all_domains() {
        let interval_product: DomainProduct<IntervalDomain, OctagonDomain> = DomainProduct::top();
        assert!(OctagonDomain::top().is_top());
        assert!(PolyhedraDomain::top().is_top());
        assert!(interval_product.is_top());
    }
}
