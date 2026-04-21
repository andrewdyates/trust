// trust-cegar: Bitvector-based predicate abstraction domain
//
// Compact predicate abstraction using bitvectors: bit i = 1 means predicate i
// holds in the abstract state. This is Cartesian abstraction (each predicate
// tracked independently) with O(1) lattice operations via bitwise ops.
//
// Complements the existing PredicateSet/BooleanAbstraction by providing:
//   - BitVecState: fixed-width bitvector abstract state
//   - abstract_state: concrete values -> BitVecState
//   - abstract_transfer: BitVecState x block transfer -> BitVecState
//   - PredicateDiscovery: interpolant formula -> atomic predicates
//
// Reference: CPAchecker's predicate abstraction domain
//   refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use trust_types::Formula;

use crate::interpolation::formula_variables;
use crate::predicate::{CmpOp, Predicate};
use crate::predicate_discovery::PredicateSet;

/// Maximum number of predicates supported in a single bitvector state.
///
/// Uses u128 internally, so 128 predicates max. This is sufficient for
/// typical CEGAR refinement (CPAchecker rarely exceeds 50 predicates per
/// function).
pub(crate) const MAX_PREDICATES: usize = 128;

/// A bitvector-based abstract state over a predicate set.
///
/// Bit `i` being set means predicate `i` (from the associated `PredicateSet`)
/// is known to hold. This is a Cartesian abstraction: each predicate is tracked
/// independently, and correlations between predicates are not represented.
///
/// Lattice operations are O(1) bitwise operations:
/// - Top: all zeros (no predicates known to hold)
/// - Bottom: sentinel bit pattern (all ones)
/// - Join: bitwise AND (intersection of known predicates)
/// - Meet: bitwise OR (union of known predicates)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BitVecState {
    /// Bitvector where bit i = 1 means predicate i holds.
    bits: u128,
    /// Number of predicates in the associated PredicateSet.
    num_predicates: u8,
}

impl BitVecState {
    /// Create the top element: no predicates known to hold.
    #[must_use]
    pub fn top(num_predicates: usize) -> Self {
        debug_assert!(num_predicates <= MAX_PREDICATES);
        Self { bits: 0, num_predicates: num_predicates as u8 }
    }

    /// Create the bottom element: unreachable state.
    ///
    /// Represented as all bits set within the valid range.
    #[must_use]
    pub fn bottom(num_predicates: usize) -> Self {
        debug_assert!(num_predicates <= MAX_PREDICATES);
        let mask = if num_predicates >= 128 { u128::MAX } else { (1u128 << num_predicates) - 1 };
        Self { bits: mask, num_predicates: num_predicates as u8 }
    }

    /// Create a state from a raw bitvector.
    #[must_use]
    pub fn from_bits(bits: u128, num_predicates: usize) -> Self {
        debug_assert!(num_predicates <= MAX_PREDICATES);
        let mask = if num_predicates >= 128 { u128::MAX } else { (1u128 << num_predicates) - 1 };
        Self { bits: bits & mask, num_predicates: num_predicates as u8 }
    }

    /// Raw bitvector value.
    #[must_use]
    pub fn bits(&self) -> u128 {
        self.bits
    }

    /// Number of predicates in the associated set.
    #[must_use]
    pub fn num_predicates(&self) -> usize {
        self.num_predicates as usize
    }

    /// Check if predicate `i` holds in this state.
    #[must_use]
    pub fn get(&self, i: usize) -> bool {
        i < self.num_predicates as usize && (self.bits >> i) & 1 == 1
    }

    /// Set predicate `i` to hold.
    pub fn set(&mut self, i: usize) {
        if i < self.num_predicates as usize {
            self.bits |= 1u128 << i;
        }
    }

    /// Clear predicate `i` (no longer known to hold).
    pub fn clear(&mut self, i: usize) {
        if i < self.num_predicates as usize {
            self.bits &= !(1u128 << i);
        }
    }

    /// Number of predicates known to hold.
    #[must_use]
    pub fn count_true(&self) -> usize {
        self.bits.count_ones() as usize
    }

    /// Whether this is the top element (no predicates hold).
    #[must_use]
    pub fn is_top(&self) -> bool {
        self.bits == 0
    }

    /// Whether this is the bottom element (all predicates hold).
    #[must_use]
    pub fn is_bottom(&self) -> bool {
        let mask = if self.num_predicates >= 128 {
            u128::MAX
        } else {
            (1u128 << self.num_predicates) - 1
        };
        self.bits == mask && self.num_predicates > 0
    }

    /// Join (least upper bound): intersection of known predicates.
    ///
    /// A predicate holds in the join only if it holds in both inputs.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        debug_assert_eq!(self.num_predicates, other.num_predicates);
        Self { bits: self.bits & other.bits, num_predicates: self.num_predicates }
    }

    /// Meet (greatest lower bound): union of known predicates.
    ///
    /// All predicates from either state are assumed to hold.
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        debug_assert_eq!(self.num_predicates, other.num_predicates);
        let mask = if self.num_predicates >= 128 {
            u128::MAX
        } else {
            (1u128 << self.num_predicates) - 1
        };
        Self { bits: (self.bits | other.bits) & mask, num_predicates: self.num_predicates }
    }

    /// Widen: same as join for Cartesian predicate abstraction.
    ///
    /// A more aggressive widening could drop predicates that are not stable.
    #[must_use]
    pub fn widen(&self, other: &Self) -> Self {
        self.join(other)
    }

    /// Check if this state is less than or equal to `other` in the lattice.
    ///
    /// `self <= other` means every predicate that holds in `other` also holds
    /// in `self` (other is more precise / lower in the lattice).
    #[must_use]
    pub fn subsumes(&self, other: &Self) -> bool {
        debug_assert_eq!(self.num_predicates, other.num_predicates);
        // self subsumes other if other's bits are a subset of self's bits
        (other.bits & self.bits) == other.bits
    }

    /// Convert to the existing `AbstractState` (predicate set) representation.
    #[must_use]
    pub fn to_abstract_state(&self, predicates: &PredicateSet) -> crate::predicate::AbstractState {
        let mut state = crate::predicate::AbstractState::top();
        for i in 0..self.num_predicates as usize {
            if self.get(i)
                && let Some(pred) = predicates.get(i) {
                    state.add(pred.clone());
                }
        }
        state
    }

    /// Create from an existing `AbstractState` by looking up predicates in the set.
    #[must_use]
    pub fn from_abstract_state(
        state: &crate::predicate::AbstractState,
        predicates: &PredicateSet,
    ) -> Self {
        let n = predicates.len();
        let mut bv = Self::top(n);
        for pred in &state.predicates {
            if let Some(idx) = predicates.index_of(pred) {
                bv.set(idx);
            }
        }
        bv
    }

    /// Indices of predicates that hold in this state.
    pub fn true_indices(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.num_predicates as usize).filter(|&i| self.get(i))
    }
}

impl Default for BitVecState {
    fn default() -> Self {
        Self::top(0)
    }
}

impl std::fmt::Display for BitVecState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_top() {
            return write!(f, "top");
        }
        if self.is_bottom() {
            return write!(f, "bottom");
        }
        write!(f, "0b")?;
        for i in (0..self.num_predicates as usize).rev() {
            write!(f, "{}", if self.get(i) { '1' } else { '0' })?;
        }
        Ok(())
    }
}

/// Compute the bitvector abstract state from concrete variable values.
///
/// Evaluates each predicate against the concrete values. A predicate is set
/// if the concrete values satisfy it.
///
/// # Arguments
/// * `concrete_values` - Variable name -> integer value mapping.
/// * `predicates` - The ordered predicate set.
#[must_use]
pub fn abstract_state_from_concrete(
    concrete_values: &BTreeMap<String, i128>,
    predicates: &PredicateSet,
) -> BitVecState {
    let n = predicates.len();
    let mut state = BitVecState::top(n);

    for (i, pred) in predicates.iter().enumerate() {
        if evaluate_predicate(pred, concrete_values) {
            state.set(i);
        }
    }

    state
}

/// Evaluate a predicate against concrete variable values.
///
/// Returns `true` if the predicate is satisfied, `false` if it is not
/// satisfied or if the required variables are not present.
fn evaluate_predicate(pred: &Predicate, values: &BTreeMap<String, i128>) -> bool {
    match pred {
        Predicate::Comparison { lhs, op, rhs } => {
            let lhs_val = resolve_value(lhs, values);
            let rhs_val = resolve_value(rhs, values);
            match (lhs_val, rhs_val) {
                (Some(l), Some(r)) => match op {
                    CmpOp::Lt => l < r,
                    CmpOp::Le => l <= r,
                    CmpOp::Gt => l > r,
                    CmpOp::Ge => l >= r,
                    CmpOp::Eq => l == r,
                    CmpOp::Ne => l != r,
                },
                _ => false, // Unknown if variables are missing
            }
        }
        Predicate::Range { var, lo, hi } => {
            values.get(var.as_str()).is_some_and(|&v| v >= *lo && v <= *hi)
        }
        Predicate::NonNull(var) => values.get(var.as_str()).is_some_and(|&v| v != 0),
        Predicate::Custom(_) => false, // Cannot evaluate custom predicates
    }
}

/// Resolve a name to an integer value: either a literal or a variable lookup.
fn resolve_value(name: &str, values: &BTreeMap<String, i128>) -> Option<i128> {
    if let Ok(n) = name.parse::<i128>() {
        Some(n)
    } else {
        values.get(name).copied()
    }
}

/// A block transfer function for abstract transfer.
///
/// Describes how a basic block transforms variable values:
/// - `kills`: variables assigned in this block (predicates mentioning them are invalidated)
/// - `generates`: new predicates established by the block (e.g., from assertions, branches)
#[derive(Debug, Clone, Default)]
pub struct BlockTransfer {
    /// Variables killed (assigned) by this block.
    pub kills: Vec<String>,
    /// Predicate indices generated (established) by this block.
    pub generates: Vec<usize>,
}

/// Compute the abstract transfer through a basic block.
///
/// 1. Kill predicates that mention any killed variable.
/// 2. Add generated predicates.
///
/// # Arguments
/// * `state` - Abstract state before the block.
/// * `predicates` - The predicate universe.
/// * `transfer` - The block's transfer function.
#[must_use]
pub fn abstract_transfer(
    state: &BitVecState,
    predicates: &PredicateSet,
    transfer: &BlockTransfer,
) -> BitVecState {
    let n = predicates.len();
    let mut result = *state;

    // Kill: clear predicates that mention any killed variable.
    for i in 0..n {
        if result.get(i)
            && let Some(pred) = predicates.get(i)
                && mentions_any_var(pred, &transfer.kills) {
                    result.clear(i);
                }
    }

    // Generate: set predicates established by this block.
    for &gen_idx in &transfer.generates {
        result.set(gen_idx);
    }

    result
}

/// Check if a predicate mentions any of the given variables.
fn mentions_any_var(pred: &Predicate, vars: &[String]) -> bool {
    vars.iter().any(|v| mentions_var(pred, v))
}

/// Check if a predicate mentions a specific variable.
fn mentions_var(pred: &Predicate, var: &str) -> bool {
    match pred {
        Predicate::Comparison { lhs, rhs, .. } => lhs == var || rhs == var,
        Predicate::Range { var: v, .. } => v == var,
        Predicate::NonNull(v) => v == var,
        Predicate::Custom(s) => s.contains(var),
    }
}

/// Predicate discovery from interpolant formulas.
///
/// Given a Craig interpolant (or any formula), extract atomic predicates
/// suitable for refining the predicate abstraction. Each comparison in the
/// formula becomes a candidate predicate.
pub struct PredicateDiscovery;

impl PredicateDiscovery {
    /// Extract atomic predicates from an interpolant formula.
    ///
    /// Decomposes the formula into its atomic comparison predicates,
    /// which can then be added to the predicate set for refinement.
    #[must_use]
    pub fn from_interpolant(formula: &Formula) -> Vec<Predicate> {
        let mut predicates = Vec::new();
        Self::extract_atoms(formula, &mut predicates, false);
        // Deduplicate
        predicates.sort();
        predicates.dedup();
        predicates
    }

    /// Extract predicates and annotate with the variables they reference.
    ///
    /// Returns `(predicate, variables)` pairs for filtering by scope.
    #[must_use]
    pub fn from_interpolant_with_vars(formula: &Formula) -> Vec<(Predicate, Vec<String>)> {
        let atoms = Self::from_interpolant(formula);
        atoms
            .into_iter()
            .map(|pred| {
                let vars = predicate_variables(&pred);
                (pred, vars)
            })
            .collect()
    }

    /// Filter predicates to only those using variables from a given scope.
    ///
    /// In Craig interpolation, the interpolant should only use variables
    /// common to both the prefix and suffix. This filter enforces that.
    #[must_use]
    pub fn filter_by_scope(predicates: &[Predicate], allowed_vars: &[String]) -> Vec<Predicate> {
        predicates
            .iter()
            .filter(|pred| {
                let vars = predicate_variables(pred);
                vars.iter().all(|v| {
                    // Allow integer literals (they're not variables)
                    v.parse::<i128>().is_ok() || allowed_vars.contains(v)
                })
            })
            .cloned()
            .collect()
    }

    /// Extract atomic predicates from a formula.
    fn extract_atoms(formula: &Formula, out: &mut Vec<Predicate>, negated: bool) {
        match formula {
            Formula::Lt(a, b) => {
                if let (Some(lhs), Some(rhs)) = (formula_leaf_name(a), formula_leaf_name(b)) {
                    let op = if negated { CmpOp::Ge } else { CmpOp::Lt };
                    out.push(Predicate::comparison(lhs, op, rhs));
                }
            }
            Formula::Le(a, b) => {
                if let (Some(lhs), Some(rhs)) = (formula_leaf_name(a), formula_leaf_name(b)) {
                    let op = if negated { CmpOp::Gt } else { CmpOp::Le };
                    out.push(Predicate::comparison(lhs, op, rhs));
                }
            }
            Formula::Gt(a, b) => {
                if let (Some(lhs), Some(rhs)) = (formula_leaf_name(a), formula_leaf_name(b)) {
                    let op = if negated { CmpOp::Le } else { CmpOp::Gt };
                    out.push(Predicate::comparison(lhs, op, rhs));
                }
            }
            Formula::Ge(a, b) => {
                if let (Some(lhs), Some(rhs)) = (formula_leaf_name(a), formula_leaf_name(b)) {
                    let op = if negated { CmpOp::Lt } else { CmpOp::Ge };
                    out.push(Predicate::comparison(lhs, op, rhs));
                }
            }
            Formula::Eq(a, b) => {
                if let (Some(lhs), Some(rhs)) = (formula_leaf_name(a), formula_leaf_name(b)) {
                    let op = if negated { CmpOp::Ne } else { CmpOp::Eq };
                    out.push(Predicate::comparison(lhs, op, rhs));
                }
            }
            Formula::Not(inner) => {
                Self::extract_atoms(inner, out, !negated);
            }
            Formula::And(children) | Formula::Or(children) => {
                for child in children {
                    Self::extract_atoms(child, out, negated);
                }
            }
            Formula::Implies(a, b) => {
                Self::extract_atoms(a, out, !negated);
                Self::extract_atoms(b, out, negated);
            }
            _ => {}
        }
    }
}

/// Extract variable names referenced by a predicate.
#[must_use]
pub(crate) fn predicate_variables(pred: &Predicate) -> Vec<String> {
    match pred {
        Predicate::Comparison { lhs, rhs, .. } => {
            let mut vars = Vec::new();
            if lhs.parse::<i128>().is_err() {
                vars.push(lhs.clone());
            }
            if rhs.parse::<i128>().is_err() {
                vars.push(rhs.clone());
            }
            vars
        }
        Predicate::Range { var, .. } => vec![var.clone()],
        Predicate::NonNull(var) => vec![var.clone()],
        Predicate::Custom(_) => vec![],
    }
}

/// Convert a formula leaf to a name string.
fn formula_leaf_name(formula: &Formula) -> Option<String> {
    match formula {
        Formula::Var(name, _) => Some(name.clone()),
        Formula::Int(n) => Some(n.to_string()),
        Formula::Bool(b) => Some(if *b { "1".to_string() } else { "0".to_string() }),
        _ => None,
    }
}

/// Compute the common variables between two formulas (for interpolant scoping).
#[must_use]
pub fn common_variables(formula_a: &Formula, formula_b: &Formula) -> Vec<String> {
    let vars_a = formula_variables(formula_a);
    let vars_b = formula_variables(formula_b);
    vars_a.into_iter().filter(|v| vars_b.contains(v)).collect()
}

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    // --- BitVecState tests ---

    #[test]
    fn test_bitvec_state_top_is_zero() {
        let state = BitVecState::top(5);
        assert_eq!(state.bits(), 0);
        assert!(state.is_top());
        assert!(!state.is_bottom());
        assert_eq!(state.count_true(), 0);
        assert_eq!(state.num_predicates(), 5);
    }

    #[test]
    fn test_bitvec_state_bottom_all_bits_set() {
        let state = BitVecState::bottom(5);
        assert_eq!(state.bits(), 0b11111);
        assert!(state.is_bottom());
        assert!(!state.is_top());
        assert_eq!(state.count_true(), 5);
    }

    #[test]
    fn test_bitvec_state_set_and_get() {
        let mut state = BitVecState::top(4);
        assert!(!state.get(0));
        state.set(0);
        assert!(state.get(0));
        state.set(2);
        assert!(state.get(2));
        assert!(!state.get(1));
        assert_eq!(state.count_true(), 2);
        assert_eq!(state.bits(), 0b0101);
    }

    #[test]
    fn test_bitvec_state_clear() {
        let mut state = BitVecState::bottom(4);
        assert!(state.get(1));
        state.clear(1);
        assert!(!state.get(1));
        assert_eq!(state.count_true(), 3);
    }

    #[test]
    fn test_bitvec_state_out_of_bounds() {
        let mut state = BitVecState::top(3);
        state.set(10); // Out of bounds, should be no-op
        assert!(!state.get(10));
        assert_eq!(state.bits(), 0);
    }

    #[test]
    fn test_bitvec_state_join_is_intersection() {
        let a = BitVecState::from_bits(0b1010, 4);
        let b = BitVecState::from_bits(0b1100, 4);
        let joined = a.join(&b);
        assert_eq!(joined.bits(), 0b1000); // Only bit 3 in common
        assert_eq!(joined.count_true(), 1);
    }

    #[test]
    fn test_bitvec_state_meet_is_union() {
        let a = BitVecState::from_bits(0b1010, 4);
        let b = BitVecState::from_bits(0b0101, 4);
        let met = a.meet(&b);
        assert_eq!(met.bits(), 0b1111);
        assert_eq!(met.count_true(), 4);
    }

    #[test]
    fn test_bitvec_state_widen_same_as_join() {
        let a = BitVecState::from_bits(0b1010, 4);
        let b = BitVecState::from_bits(0b1100, 4);
        assert_eq!(a.widen(&b), a.join(&b));
    }

    #[test]
    fn test_bitvec_state_subsumes() {
        let a = BitVecState::from_bits(0b1111, 4);
        let b = BitVecState::from_bits(0b1010, 4);
        assert!(a.subsumes(&b)); // a has all of b's bits
        assert!(!b.subsumes(&a)); // b does not have all of a's bits
    }

    #[test]
    fn test_bitvec_state_subsumes_equal() {
        let a = BitVecState::from_bits(0b1010, 4);
        let b = BitVecState::from_bits(0b1010, 4);
        assert!(a.subsumes(&b));
        assert!(b.subsumes(&a));
    }

    #[test]
    fn test_bitvec_state_from_bits_masks() {
        // Bits beyond num_predicates should be masked off
        let state = BitVecState::from_bits(0b11111111, 4);
        assert_eq!(state.bits(), 0b1111);
        assert_eq!(state.count_true(), 4);
    }

    #[test]
    fn test_bitvec_state_display_top() {
        let state = BitVecState::top(3);
        assert_eq!(state.to_string(), "top");
    }

    #[test]
    fn test_bitvec_state_display_bottom() {
        let state = BitVecState::bottom(3);
        assert_eq!(state.to_string(), "bottom");
    }

    #[test]
    fn test_bitvec_state_display_mixed() {
        let state = BitVecState::from_bits(0b101, 3);
        assert_eq!(state.to_string(), "0b101");
    }

    #[test]
    fn test_bitvec_state_true_indices() {
        let state = BitVecState::from_bits(0b1010, 4);
        let indices: Vec<usize> = state.true_indices().collect();
        assert_eq!(indices, vec![1, 3]);
    }

    // --- abstract_state_from_concrete tests ---

    #[test]
    fn test_abstract_state_from_concrete_basic() {
        let predicates = PredicateSet::from_predicates(vec![
            Predicate::comparison("x", CmpOp::Gt, "0"),
            Predicate::comparison("y", CmpOp::Le, "10"),
            Predicate::comparison("x", CmpOp::Eq, "y"),
        ]);
        let mut values = BTreeMap::new();
        values.insert("x".to_string(), 5);
        values.insert("y".to_string(), 5);

        let state = abstract_state_from_concrete(&values, &predicates);
        assert!(state.get(0)); // x > 0: 5 > 0 = true
        assert!(state.get(1)); // y <= 10: 5 <= 10 = true
        assert!(state.get(2)); // x == y: 5 == 5 = true
        assert_eq!(state.count_true(), 3);
    }

    #[test]
    fn test_abstract_state_from_concrete_partial() {
        let predicates = PredicateSet::from_predicates(vec![
            Predicate::comparison("x", CmpOp::Gt, "0"),
            Predicate::comparison("y", CmpOp::Lt, "0"),
        ]);
        let mut values = BTreeMap::new();
        values.insert("x".to_string(), 5);
        values.insert("y".to_string(), 10); // y = 10, not < 0

        let state = abstract_state_from_concrete(&values, &predicates);
        assert!(state.get(0));  // x > 0: true
        assert!(!state.get(1)); // y < 0: false
    }

    #[test]
    fn test_abstract_state_from_concrete_missing_vars() {
        let predicates = PredicateSet::from_predicates(vec![
            Predicate::comparison("x", CmpOp::Gt, "0"),
            Predicate::comparison("z", CmpOp::Eq, "42"),
        ]);
        let mut values = BTreeMap::new();
        values.insert("x".to_string(), 1);
        // z is missing

        let state = abstract_state_from_concrete(&values, &predicates);
        assert!(state.get(0));  // x > 0: true
        assert!(!state.get(1)); // z not present -> false
    }

    #[test]
    fn test_abstract_state_from_concrete_range() {
        let predicates = PredicateSet::from_predicates(vec![
            Predicate::range("i", 0, 100),
        ]);
        let mut values = BTreeMap::new();
        values.insert("i".to_string(), 50);

        let state = abstract_state_from_concrete(&values, &predicates);
        assert!(state.get(0)); // 0 <= 50 <= 100
    }

    #[test]
    fn test_abstract_state_from_concrete_range_outside() {
        let predicates = PredicateSet::from_predicates(vec![
            Predicate::range("i", 0, 100),
        ]);
        let mut values = BTreeMap::new();
        values.insert("i".to_string(), 200);

        let state = abstract_state_from_concrete(&values, &predicates);
        assert!(!state.get(0)); // 200 > 100
    }

    #[test]
    fn test_abstract_state_from_concrete_non_null() {
        let predicates = PredicateSet::from_predicates(vec![
            Predicate::non_null("ptr"),
        ]);
        let mut values = BTreeMap::new();
        values.insert("ptr".to_string(), 0x1000);

        let state = abstract_state_from_concrete(&values, &predicates);
        assert!(state.get(0));

        values.insert("ptr".to_string(), 0);
        let state2 = abstract_state_from_concrete(&values, &predicates);
        assert!(!state2.get(0)); // null pointer
    }

    // --- abstract_transfer tests ---

    #[test]
    fn test_abstract_transfer_no_kills_no_gen() {
        let predicates = PredicateSet::from_predicates(vec![
            Predicate::comparison("x", CmpOp::Gt, "0"),
            Predicate::comparison("y", CmpOp::Lt, "10"),
        ]);
        let state = BitVecState::from_bits(0b11, 2);
        let transfer = BlockTransfer::default();

        let result = abstract_transfer(&state, &predicates, &transfer);
        assert_eq!(result.bits(), 0b11); // Unchanged
    }

    #[test]
    fn test_abstract_transfer_kills_variable() {
        let predicates = PredicateSet::from_predicates(vec![
            Predicate::comparison("x", CmpOp::Gt, "0"),
            Predicate::comparison("y", CmpOp::Lt, "10"),
            Predicate::comparison("x", CmpOp::Lt, "y"),
        ]);
        let state = BitVecState::from_bits(0b111, 3);
        let transfer = BlockTransfer {
            kills: vec!["x".to_string()],
            generates: vec![],
        };

        let result = abstract_transfer(&state, &predicates, &transfer);
        assert!(!result.get(0)); // x > 0 killed (mentions x)
        assert!(result.get(1));  // y < 10 survives (doesn't mention x)
        assert!(!result.get(2)); // x < y killed (mentions x)
    }

    #[test]
    fn test_abstract_transfer_generates_predicate() {
        let predicates = PredicateSet::from_predicates(vec![
            Predicate::comparison("x", CmpOp::Gt, "0"),
            Predicate::comparison("y", CmpOp::Lt, "10"),
        ]);
        let state = BitVecState::top(2);
        let transfer = BlockTransfer {
            kills: vec![],
            generates: vec![1], // Generate "y < 10"
        };

        let result = abstract_transfer(&state, &predicates, &transfer);
        assert!(!result.get(0)); // Not generated
        assert!(result.get(1));  // Generated by transfer
    }

    #[test]
    fn test_abstract_transfer_kill_then_generate() {
        let predicates = PredicateSet::from_predicates(vec![
            Predicate::comparison("x", CmpOp::Ge, "0"),
        ]);
        let state = BitVecState::from_bits(0b1, 1); // x >= 0 holds
        let transfer = BlockTransfer {
            kills: vec!["x".to_string()],
            generates: vec![0], // Re-establish x >= 0 after assignment
        };

        let result = abstract_transfer(&state, &predicates, &transfer);
        assert!(result.get(0)); // Killed then re-generated
    }

    // --- PredicateDiscovery tests ---

    #[test]
    fn test_discovery_from_simple_comparison() {
        let formula = Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        );
        let preds = PredicateDiscovery::from_interpolant(&formula);
        assert_eq!(preds.len(), 1);
        assert_eq!(preds[0], Predicate::comparison("x", CmpOp::Lt, "10"));
    }

    #[test]
    fn test_discovery_from_conjunction() {
        let formula = Formula::And(vec![
            Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Var("n".into(), Sort::Int)),
            ),
        ]);
        let preds = PredicateDiscovery::from_interpolant(&formula);
        assert_eq!(preds.len(), 2);
        assert!(preds.contains(&Predicate::comparison("x", CmpOp::Ge, "0")));
        assert!(preds.contains(&Predicate::comparison("y", CmpOp::Lt, "n")));
    }

    #[test]
    fn test_discovery_from_negated_formula() {
        // NOT(x >= 10) should yield x < 10
        let formula = Formula::Not(Box::new(Formula::Ge(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        )));
        let preds = PredicateDiscovery::from_interpolant(&formula);
        assert_eq!(preds.len(), 1);
        assert_eq!(preds[0], Predicate::comparison("x", CmpOp::Lt, "10"));
    }

    #[test]
    fn test_discovery_from_double_negation() {
        // NOT(NOT(x < 5)) should yield x < 5
        let formula = Formula::Not(Box::new(Formula::Not(Box::new(Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(5)),
        )))));
        let preds = PredicateDiscovery::from_interpolant(&formula);
        assert_eq!(preds.len(), 1);
        assert_eq!(preds[0], Predicate::comparison("x", CmpOp::Lt, "5"));
    }

    #[test]
    fn test_discovery_from_equality() {
        let formula = Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        );
        let preds = PredicateDiscovery::from_interpolant(&formula);
        assert_eq!(preds.len(), 1);
        assert_eq!(preds[0], Predicate::comparison("x", CmpOp::Eq, "y"));
    }

    #[test]
    fn test_discovery_deduplicates() {
        // Same comparison appears twice in a conjunction
        let formula = Formula::And(vec![
            Formula::Lt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
        ]);
        let preds = PredicateDiscovery::from_interpolant(&formula);
        assert_eq!(preds.len(), 1);
    }

    #[test]
    fn test_discovery_from_implication() {
        // x < 5 => y >= 0 should extract NOT(x < 5) = x >= 5 and y >= 0
        let formula = Formula::Implies(
            Box::new(Formula::Lt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(5)),
            )),
            Box::new(Formula::Ge(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        let preds = PredicateDiscovery::from_interpolant(&formula);
        assert!(preds.contains(&Predicate::comparison("x", CmpOp::Ge, "5")));
        assert!(preds.contains(&Predicate::comparison("y", CmpOp::Ge, "0")));
    }

    #[test]
    fn test_discovery_empty_for_non_comparison() {
        let formula = Formula::Bool(true);
        let preds = PredicateDiscovery::from_interpolant(&formula);
        assert!(preds.is_empty());
    }

    #[test]
    fn test_discovery_with_vars() {
        let formula = Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        );
        let preds_with_vars = PredicateDiscovery::from_interpolant_with_vars(&formula);
        assert_eq!(preds_with_vars.len(), 1);
        let (pred, vars) = &preds_with_vars[0];
        assert_eq!(*pred, Predicate::comparison("x", CmpOp::Lt, "10"));
        assert_eq!(vars, &["x".to_string()]);
    }

    #[test]
    fn test_filter_by_scope() {
        let preds = vec![
            Predicate::comparison("x", CmpOp::Lt, "10"),
            Predicate::comparison("y", CmpOp::Ge, "0"),
            Predicate::comparison("z", CmpOp::Eq, "w"),
        ];
        let allowed = vec!["x".to_string(), "y".to_string()];
        let filtered = PredicateDiscovery::filter_by_scope(&preds, &allowed);
        assert_eq!(filtered.len(), 2); // x and y predicates pass, z/w don't
        assert!(filtered.contains(&Predicate::comparison("x", CmpOp::Lt, "10")));
        assert!(filtered.contains(&Predicate::comparison("y", CmpOp::Ge, "0")));
    }

    #[test]
    fn test_filter_by_scope_allows_constants() {
        let preds = vec![
            Predicate::comparison("x", CmpOp::Lt, "10"), // 10 is a constant
        ];
        let allowed = vec!["x".to_string()];
        let filtered = PredicateDiscovery::filter_by_scope(&preds, &allowed);
        assert_eq!(filtered.len(), 1); // "10" is a literal, allowed
    }

    // --- Conversion tests ---

    #[test]
    fn test_bitvec_to_abstract_state_roundtrip() {
        let predicates = PredicateSet::from_predicates(vec![
            Predicate::comparison("x", CmpOp::Ge, "0"),
            Predicate::comparison("y", CmpOp::Lt, "10"),
            Predicate::non_null("ptr"),
        ]);
        let bv = BitVecState::from_bits(0b101, 3); // predicates 0 and 2

        let abs = bv.to_abstract_state(&predicates);
        assert!(abs.contains(&Predicate::comparison("x", CmpOp::Ge, "0")));
        assert!(!abs.contains(&Predicate::comparison("y", CmpOp::Lt, "10")));
        assert!(abs.contains(&Predicate::non_null("ptr")));

        // Round-trip back
        let bv2 = BitVecState::from_abstract_state(&abs, &predicates);
        assert_eq!(bv.bits(), bv2.bits());
    }

    // --- common_variables tests ---

    #[test]
    fn test_common_variables() {
        let a = Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        );
        let b = Formula::Ge(
            Box::new(Formula::Var("y".into(), Sort::Int)),
            Box::new(Formula::Var("z".into(), Sort::Int)),
        );
        let common = common_variables(&a, &b);
        assert_eq!(common, vec!["y".to_string()]);
    }

    #[test]
    fn test_common_variables_no_overlap() {
        let a = Formula::Var("x".into(), Sort::Int);
        let b = Formula::Var("y".into(), Sort::Int);
        let common = common_variables(&a, &b);
        assert!(common.is_empty());
    }

    // --- predicate_variables tests ---

    #[test]
    fn test_predicate_variables_comparison() {
        let pred = Predicate::comparison("x", CmpOp::Lt, "y");
        let vars = predicate_variables(&pred);
        assert_eq!(vars, vec!["x".to_string(), "y".to_string()]);
    }

    #[test]
    fn test_predicate_variables_with_constant() {
        let pred = Predicate::comparison("x", CmpOp::Lt, "10");
        let vars = predicate_variables(&pred);
        assert_eq!(vars, vec!["x".to_string()]); // "10" is not a variable
    }

    #[test]
    fn test_predicate_variables_range() {
        let pred = Predicate::range("i", 0, 100);
        let vars = predicate_variables(&pred);
        assert_eq!(vars, vec!["i".to_string()]);
    }

    #[test]
    fn test_predicate_variables_non_null() {
        let pred = Predicate::non_null("ptr");
        let vars = predicate_variables(&pred);
        assert_eq!(vars, vec!["ptr".to_string()]);
    }

    // --- Edge cases ---

    #[test]
    fn test_bitvec_state_zero_predicates() {
        let state = BitVecState::top(0);
        assert!(state.is_top());
        assert_eq!(state.count_true(), 0);
        assert_eq!(state.to_string(), "top");
    }

    #[test]
    fn test_bitvec_state_max_predicates() {
        let state = BitVecState::bottom(128);
        assert!(state.is_bottom());
        assert_eq!(state.count_true(), 128);
    }

    #[test]
    fn test_abstract_transfer_empty_predicates() {
        let predicates = PredicateSet::new();
        let state = BitVecState::top(0);
        let transfer = BlockTransfer::default();
        let result = abstract_transfer(&state, &predicates, &transfer);
        assert!(result.is_top());
    }

    #[test]
    fn test_discovery_from_disjunction() {
        // OR(x < 5, y > 10) should still extract both atoms
        let formula = Formula::Or(vec![
            Formula::Lt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(5)),
            ),
            Formula::Gt(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
        ]);
        let preds = PredicateDiscovery::from_interpolant(&formula);
        assert_eq!(preds.len(), 2);
        assert!(preds.contains(&Predicate::comparison("x", CmpOp::Lt, "5")));
        assert!(preds.contains(&Predicate::comparison("y", CmpOp::Gt, "10")));
    }
}
