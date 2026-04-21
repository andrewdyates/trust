// trust-cegar: Predicate abstraction over MIR basic blocks
//
// Inspired by CPAchecker's predicate CPA:
//   refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use trust_types::{BasicBlock, BinOp, Operand, Rvalue, Statement, Terminator};

/// Comparison operators for predicate expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum CmpOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl CmpOp {
    /// Return the negation of this comparison operator.
    #[must_use]
    pub fn negate(self) -> Self {
        match self {
            Self::Lt => Self::Ge,
            Self::Le => Self::Gt,
            Self::Gt => Self::Le,
            Self::Ge => Self::Lt,
            Self::Eq => Self::Ne,
            Self::Ne => Self::Eq,
        }
    }

    /// Convert from a MIR `BinOp`, returning `None` for non-comparison ops.
    #[must_use]
    pub fn from_bin_op(op: BinOp) -> Option<Self> {
        match op {
            BinOp::Lt => Some(Self::Lt),
            BinOp::Le => Some(Self::Le),
            BinOp::Gt => Some(Self::Gt),
            BinOp::Ge => Some(Self::Ge),
            BinOp::Eq => Some(Self::Eq),
            BinOp::Ne => Some(Self::Ne),
            _ => None,
        }
    }
}

impl std::fmt::Display for CmpOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Lt => write!(f, "<"),
            Self::Le => write!(f, "<="),
            Self::Gt => write!(f, ">"),
            Self::Ge => write!(f, ">="),
            Self::Eq => write!(f, "=="),
            Self::Ne => write!(f, "!="),
        }
    }
}

/// A predicate tracked in the abstract domain.
///
/// Predicates are the atoms of our abstract state. They are discovered
/// from program conditions (branch guards, assert conditions) and from
/// counterexample refinement (Craig interpolation).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Predicate {
    /// A comparison between two symbolic expressions: `lhs op rhs`.
    Comparison { lhs: String, op: CmpOp, rhs: String },

    /// A range predicate: `lo <= var <= hi`.
    Range { var: String, lo: i128, hi: i128 },

    /// A non-null predicate for a pointer/reference variable.
    NonNull(String),

    /// A custom predicate expressed as a formula string.
    Custom(String),
}

impl Predicate {
    /// Create a comparison predicate.
    #[must_use]
    pub fn comparison(lhs: impl Into<String>, op: CmpOp, rhs: impl Into<String>) -> Self {
        Self::Comparison { lhs: lhs.into(), op, rhs: rhs.into() }
    }

    /// Create a range predicate.
    #[must_use]
    pub fn range(var: impl Into<String>, lo: i128, hi: i128) -> Self {
        Self::Range { var: var.into(), lo, hi }
    }

    /// Create a non-null predicate.
    #[must_use]
    pub fn non_null(var: impl Into<String>) -> Self {
        Self::NonNull(var.into())
    }

    /// Negate this predicate.
    #[must_use]
    pub fn negate(&self) -> Self {
        match self {
            Self::Comparison { lhs, op, rhs } => {
                Self::Comparison { lhs: lhs.clone(), op: op.negate(), rhs: rhs.clone() }
            }
            Self::Range { var, lo, hi } => {
                // Negation of lo <= var <= hi is var < lo || var > hi.
                // We approximate as a custom formula.
                Self::Custom(format!("!({lo} <= {var} <= {hi})"))
            }
            Self::NonNull(var) => Self::Custom(format!("{var} == null")),
            Self::Custom(s) => Self::Custom(format!("!({s})")),
        }
    }
}

impl std::fmt::Display for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Comparison { lhs, op, rhs } => write!(f, "{lhs} {op} {rhs}"),
            Self::Range { var, lo, hi } => write!(f, "{lo} <= {var} <= {hi}"),
            Self::NonNull(var) => write!(f, "{var} != null"),
            Self::Custom(s) => write!(f, "{s}"),
        }
    }
}

/// The abstract state at a program point: a set of predicates known to hold.
///
/// This corresponds to CPAchecker's `PredicateAbstractState` — a conjunction
/// of boolean predicates over program variables.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AbstractState {
    /// Predicates known to be true at this program point.
    pub predicates: BTreeSet<Predicate>,
}

impl AbstractState {
    /// Create an empty abstract state (top of the lattice — no information).
    #[must_use]
    pub fn top() -> Self {
        Self { predicates: BTreeSet::new() }
    }

    /// Add a predicate to the abstract state.
    pub fn add(&mut self, pred: Predicate) {
        self.predicates.insert(pred);
    }

    /// Check if a predicate is known to hold.
    #[must_use]
    pub fn contains(&self, pred: &Predicate) -> bool {
        self.predicates.contains(pred)
    }

    /// Number of predicates in this state.
    #[must_use]
    pub fn len(&self) -> usize {
        self.predicates.len()
    }

    /// Whether this abstract state is top (no predicates).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.predicates.is_empty()
    }

    /// Join (intersection) of two abstract states.
    /// A predicate holds in the join only if it holds in both inputs.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let predicates = self.predicates.intersection(&other.predicates).cloned().collect();
        Self { predicates }
    }

    /// Meet (union) of two abstract states.
    /// All predicates from both states are assumed to hold.
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        let predicates = self.predicates.union(&other.predicates).cloned().collect();
        Self { predicates }
    }
}

impl std::fmt::Display for AbstractState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.predicates.is_empty() {
            return write!(f, "true");
        }
        let parts: Vec<String> = self.predicates.iter().map(ToString::to_string).collect();
        write!(f, "{}", parts.join(" /\\ "))
    }
}

/// Extract an operand name as a string for predicate construction.
fn operand_name(op: &Operand) -> String {
    match op {
        Operand::Copy(place) | Operand::Move(place) => format!("_{}", place.local),
        Operand::Constant(c) => format!("{c:?}"),
        _ => "unknown".to_string(),
    }
}

/// Compute the abstract state after executing a basic block, given a set of
/// tracked predicates.
///
/// This is a forward abstract transfer function. It:
/// 1. Starts with predicates that survive the block's assignments (kill/gen).
/// 2. Adds predicates implied by branch conditions in the terminator.
///
/// # Arguments
/// * `block` - The basic block to abstract.
/// * `preds` - The universe of predicates being tracked.
///
/// # Returns
/// The abstract state at the exit of this block.
#[must_use]
pub fn abstract_block(block: &BasicBlock, preds: &[Predicate]) -> AbstractState {
    let mut state = AbstractState::top();

    // Collect variables assigned in this block (killed predicates).
    let mut killed_vars: BTreeSet<String> = BTreeSet::new();
    for stmt in &block.stmts {
        if let Statement::Assign { place, .. } = stmt {
            killed_vars.insert(format!("_{}", place.local));
        }
    }

    // Add predicates that are not killed by assignments.
    for pred in preds {
        if !predicate_mentions_any(pred, &killed_vars) {
            state.add(pred.clone());
        }
    }

    // Extract predicates from the terminator.
    match &block.terminator {
        Terminator::SwitchInt { discr, .. } => {
            let var = operand_name(discr);
            // The discriminant itself is being tested — add comparison predicates
            // from the tracked set that reference this variable.
            for pred in preds {
                if predicate_mentions(pred, &var) && !state.contains(pred) {
                    state.add(pred.clone());
                }
            }
        }
        Terminator::Assert { cond, expected, .. } => {
            // Assert condition gives us a predicate directly.
            let cond_name = operand_name(cond);
            let pred = if *expected {
                Predicate::comparison(cond_name, CmpOp::Ne, "0")
            } else {
                Predicate::comparison(cond_name, CmpOp::Eq, "0")
            };
            state.add(pred);
        }
        _ => {}
    }

    // Extract predicates from assignments that are comparisons.
    for stmt in &block.stmts {
        if let Statement::Assign { place, rvalue, .. } = stmt
            && let Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) =
                rvalue
            {
                if let Some(cmp) = CmpOp::from_bin_op(*op) {
                    let pred =
                        Predicate::comparison(operand_name(lhs), cmp, operand_name(rhs));
                    state.add(pred);
                }
                // Track the assigned variable for range predicates.
                let assigned = format!("_{}", place.local);
                for p in preds {
                    if predicate_mentions(p, &assigned) {
                        state.add(p.clone());
                    }
                }
            }
    }

    state
}

/// Check if a predicate mentions a specific variable name.
fn predicate_mentions(pred: &Predicate, var: &str) -> bool {
    match pred {
        Predicate::Comparison { lhs, rhs, .. } => lhs == var || rhs == var,
        Predicate::Range { var: v, .. } => v == var,
        Predicate::NonNull(v) => v == var,
        Predicate::Custom(s) => s.contains(var),
    }
}

/// Check if a predicate mentions any variable in the given set.
fn predicate_mentions_any(pred: &Predicate, vars: &BTreeSet<String>) -> bool {
    vars.iter().any(|v| predicate_mentions(pred, v))
}

#[cfg(test)]
mod tests {
    use trust_types::{BlockId, ConstValue, Operand, Place, SourceSpan};

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    #[test]
    fn test_cmpop_negate_is_involution() {
        for op in [CmpOp::Lt, CmpOp::Le, CmpOp::Gt, CmpOp::Ge, CmpOp::Eq, CmpOp::Ne] {
            assert_eq!(op.negate().negate(), op);
        }
    }

    #[test]
    fn test_cmpop_from_bin_op_comparisons() {
        assert_eq!(CmpOp::from_bin_op(BinOp::Lt), Some(CmpOp::Lt));
        assert_eq!(CmpOp::from_bin_op(BinOp::Eq), Some(CmpOp::Eq));
        assert_eq!(CmpOp::from_bin_op(BinOp::Add), None);
    }

    #[test]
    fn test_predicate_display() {
        let p = Predicate::comparison("x", CmpOp::Ge, "0");
        assert_eq!(p.to_string(), "x >= 0");

        let r = Predicate::range("idx", 0, 100);
        assert_eq!(r.to_string(), "0 <= idx <= 100");

        let nn = Predicate::non_null("ptr");
        assert_eq!(nn.to_string(), "ptr != null");
    }

    #[test]
    fn test_predicate_negate() {
        let p = Predicate::comparison("x", CmpOp::Lt, "y");
        let neg = p.negate();
        assert_eq!(neg, Predicate::comparison("x", CmpOp::Ge, "y"));
        assert_eq!(neg.negate(), p);
    }

    #[test]
    fn test_abstract_state_top_is_empty() {
        let state = AbstractState::top();
        assert!(state.is_empty());
        assert_eq!(state.to_string(), "true");
    }

    #[test]
    fn test_abstract_state_add_and_contains() {
        let mut state = AbstractState::top();
        let pred = Predicate::comparison("x", CmpOp::Ge, "0");
        state.add(pred.clone());
        assert!(state.contains(&pred));
        assert_eq!(state.len(), 1);
    }

    #[test]
    fn test_abstract_state_join_intersection() {
        let mut a = AbstractState::top();
        let mut b = AbstractState::top();
        let p1 = Predicate::comparison("x", CmpOp::Ge, "0");
        let p2 = Predicate::non_null("ptr");
        a.add(p1.clone());
        a.add(p2.clone());
        b.add(p1.clone());
        let joined = a.join(&b);
        assert!(joined.contains(&p1));
        assert!(!joined.contains(&p2));
    }

    #[test]
    fn test_abstract_state_meet_union() {
        let mut a = AbstractState::top();
        let mut b = AbstractState::top();
        let p1 = Predicate::comparison("x", CmpOp::Ge, "0");
        let p2 = Predicate::non_null("ptr");
        a.add(p1.clone());
        b.add(p2.clone());
        let met = a.meet(&b);
        assert!(met.contains(&p1));
        assert!(met.contains(&p2));
        assert_eq!(met.len(), 2);
    }

    #[test]
    fn test_abstract_block_empty_block() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Return,
        };
        let preds = vec![Predicate::comparison("x", CmpOp::Ge, "0")];
        let state = abstract_block(&block, &preds);
        assert!(state.contains(&preds[0]));
    }

    #[test]
    fn test_abstract_block_kills_assigned_var() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(42, 64))),
                span: span(),
            }],
            terminator: Terminator::Return,
        };
        let preds = vec![
            Predicate::comparison("_1", CmpOp::Ge, "0"),
            Predicate::comparison("_2", CmpOp::Lt, "100"),
        ];
        let state = abstract_block(&block, &preds);
        // _1 is assigned, so the predicate on _1 is killed
        assert!(!state.contains(&preds[0]));
        // _2 is not assigned, so predicate survives
        assert!(state.contains(&preds[1]));
    }

    #[test]
    fn test_abstract_block_assert_generates_predicate() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Assert {
                cond: Operand::Copy(Place::local(1)),
                expected: true,
                msg: trust_types::AssertMessage::BoundsCheck,
                target: BlockId(1),
                span: span(),
            },
        };
        let state = abstract_block(&block, &[]);
        // Assert(cond, true) means cond != 0 holds after the assert
        assert!(state.contains(&Predicate::comparison("_1", CmpOp::Ne, "0")));
    }

    #[test]
    fn test_abstract_block_comparison_assignment() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };
        let state = abstract_block(&block, &[]);
        assert!(state.contains(&Predicate::comparison("_1", CmpOp::Lt, "_2")));
    }
}
