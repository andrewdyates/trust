// trust-symex execution engine
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use std::fmt::Write;

use serde::{Deserialize, Serialize};
use trust_types::{
    BasicBlock, BinOp, ConstValue, Operand, Place, Rvalue, Statement, Terminator, Ty,
};

use crate::error::SymexError;
use crate::path::PathConstraint;
use crate::state::{SymbolicState, SymbolicValue};

/// A fork in execution produced when a branch is encountered.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionFork {
    /// Symbolic state at the fork point.
    pub state: SymbolicState,
    /// Path constraints accumulated up to and including this fork.
    pub path: PathConstraint,
    /// The next block to execute.
    pub next_block: usize,
}

/// Result of executing a single basic block.
#[derive(Debug)]
pub enum BlockResult {
    /// Execution continues to a single next block (no branching).
    Continue(usize),
    /// Execution forks at a branch: multiple possible successors.
    Fork(Vec<ExecutionFork>),
    /// Execution terminates (return or unreachable).
    Terminated,
}

/// The symbolic execution engine.
///
/// Tracks symbolic state, path constraints, and block coverage.
#[derive(Debug, Clone)]
pub struct SymbolicExecutor {
    /// Current symbolic state (variable -> symbolic value).
    pub state: SymbolicState,
    /// Current path constraints.
    pub path: PathConstraint,
    /// Set of covered block IDs.
    pub coverage: FxHashSet<usize>,
    /// Maximum execution depth (number of blocks).
    pub depth_limit: usize,
    /// Current execution depth.
    pub(crate) current_depth: usize,
}

impl SymbolicExecutor {
    /// Create a new executor with the given depth limit.
    #[must_use]
    pub fn new(depth_limit: usize) -> Self {
        Self {
            state: SymbolicState::new(),
            path: PathConstraint::new(),
            coverage: FxHashSet::default(),
            depth_limit,
            current_depth: 0,
        }
    }

    /// Create an executor from a prior fork point.
    #[must_use]
    pub fn from_fork(fork: ExecutionFork, depth_limit: usize) -> Self {
        Self {
            state: fork.state,
            path: fork.path,
            coverage: FxHashSet::default(),
            depth_limit,
            current_depth: 0,
        }
    }

    /// Execute a single basic block, potentially forking on branches.
    pub fn execute_block(&mut self, block: &BasicBlock) -> Result<BlockResult, SymexError> {
        if self.current_depth >= self.depth_limit {
            return Err(SymexError::DepthLimitExceeded {
                depth: self.current_depth,
                limit: self.depth_limit,
            });
        }

        self.current_depth += 1;
        self.coverage.insert(block.id.0);

        // Execute all statements in the block.
        for stmt in &block.stmts {
            self.execute_statement(stmt)?;
        }

        // Process the terminator.
        self.execute_terminator(&block.terminator)
    }

    fn execute_statement(&mut self, stmt: &Statement) -> Result<(), SymexError> {
        match stmt {
            Statement::Assign { place, rvalue, .. } => {
                // CheckedBinaryOp produces a (result, overflow_flag) tuple.
                // We store the result at place.f0 and the overflow condition at place.f1.
                if let Rvalue::CheckedBinaryOp(op, lhs, rhs) = rvalue {
                    let l = self.eval_operand(lhs)?;
                    let r = self.eval_operand(rhs)?;
                    let result_val = SymbolicValue::bin_op(l.clone(), *op, r.clone());
                    // tRust #803 P0-5: Extract bit width/signedness from operands
                    // so overflow checks use range-based detection instead of the
                    // algebraically tautological (result - lhs) != rhs.
                    let type_info = infer_operand_type(lhs).or_else(|| infer_operand_type(rhs));
                    let overflow_cond = build_overflow_condition(l, *op, r, type_info);
                    let base = place_to_name(place);
                    self.state.set(format!("{base}.f0"), result_val);
                    self.state.set(format!("{base}.f1"), overflow_cond);
                    return Ok(());
                }
                let val = self.eval_rvalue(rvalue)?;
                let name = place_to_name(place);
                self.state.set(name, val);
                Ok(())
            }
            Statement::Nop => Ok(()),
            _ => Ok(()),
        }
    }

    fn execute_terminator(&mut self, term: &Terminator) -> Result<BlockResult, SymexError> {
        match term {
            Terminator::Goto(target) => Ok(BlockResult::Continue(target.0)),
            Terminator::Return => Ok(BlockResult::Terminated),
            Terminator::Unreachable => Err(SymexError::UnreachableReached),
            Terminator::SwitchInt {
                discr, targets, otherwise, ..
            } => {
                let discr_val = self.eval_operand(discr)?;

                let mut forks = Vec::new();

                // One fork per target value.
                for (value, target) in targets {
                    // tRust: #783 — two's complement cast preserves bitvector semantics.
                    let cond = SymbolicValue::bin_op(
                        discr_val.clone(),
                        BinOp::Eq,
                        SymbolicValue::Concrete(*value as i128),
                    );
                    let mut fork_path = self.path.clone();
                    fork_path.add_constraint(cond, true);
                    forks.push(ExecutionFork {
                        state: self.state.clone(),
                        path: fork_path,
                        next_block: target.0,
                    });
                }

                // Otherwise branch: none of the target values matched.
                let mut otherwise_path = self.path.clone();
                for (value, _) in targets {
                    // tRust: #783 — two's complement cast preserves bitvector semantics.
                    let cond = SymbolicValue::bin_op(
                        discr_val.clone(),
                        BinOp::Eq,
                        SymbolicValue::Concrete(*value as i128),
                    );
                    otherwise_path.add_constraint(cond, false);
                }
                forks.push(ExecutionFork {
                    state: self.state.clone(),
                    path: otherwise_path,
                    next_block: otherwise.0,
                });

                Ok(BlockResult::Fork(forks))
            }
            Terminator::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                let cond_val = self.eval_operand(cond)?;
                let constraint_cond = if *expected {
                    cond_val
                } else {
                    SymbolicValue::Not(Box::new(cond_val))
                };
                self.path.add_constraint(constraint_cond, true);
                Ok(BlockResult::Continue(target.0))
            }
            Terminator::Call { dest, target, .. } => {
                // Model calls as producing a fresh symbolic value.
                let name = place_to_name(dest);
                let fresh = SymbolicValue::Symbol(format!("call_result_{name}"));
                self.state.set(name, fresh);
                match target {
                    Some(t) => Ok(BlockResult::Continue(t.0)),
                    None => Ok(BlockResult::Terminated),
                }
            }
            Terminator::Drop { target, .. } => Ok(BlockResult::Continue(target.0)),
            _ => Ok(BlockResult::Terminated),
        }
    }

    fn eval_rvalue(&self, rvalue: &Rvalue) -> Result<SymbolicValue, SymexError> {
        match rvalue {
            Rvalue::Use(op) => self.eval_operand(op),
            Rvalue::BinaryOp(op, lhs, rhs) => {
                let l = self.eval_operand(lhs)?;
                let r = self.eval_operand(rhs)?;
                Ok(SymbolicValue::bin_op(l, *op, r))
            }
            // CheckedBinaryOp is handled in execute_statement to produce
            // the (result, overflow_flag) tuple at place.f0 and place.f1.
            // If reached here directly, return just the result value.
            Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
                let l = self.eval_operand(lhs)?;
                let r = self.eval_operand(rhs)?;
                Ok(SymbolicValue::bin_op(l, *op, r))
            }
            Rvalue::UnaryOp(un_op, op) => {
                let v = self.eval_operand(op)?;
                match un_op {
                    trust_types::UnOp::Neg => Ok(SymbolicValue::Neg(Box::new(v))),
                    trust_types::UnOp::Not => Ok(SymbolicValue::BitwiseNot(Box::new(v))),
                    trust_types::UnOp::PtrMetadata | _ => {
                        Ok(SymbolicValue::Symbol(format!("ptrmeta_{}", self.current_depth)))
                    }
                }
            }
            Rvalue::Ref { place, .. } => {
                // #776: Return a symbolic reference (pointer token), not the
                // value at the place. `&x` produces a pointer to x, not x itself.
                // Deref operations resolve the pointer via the state mapping.
                let name = place_to_name(place);
                Ok(SymbolicValue::Symbol(format!("ref_{name}")))
            }
            Rvalue::Cast(op, dest_ty) => {
                let val = self.eval_operand(op)?;
                Ok(apply_cast(val, dest_ty))
            }
            Rvalue::Aggregate(_, ops) => {
                // Aggregates: represent as the first field or a fresh symbol.
                if let Some(first) = ops.first() {
                    self.eval_operand(first)
                } else {
                    Ok(SymbolicValue::Concrete(0))
                }
            }
            Rvalue::Discriminant(place) => {
                let name = format!("discr_{}", place_to_name(place));
                Ok(SymbolicValue::Symbol(name))
            }
            Rvalue::Len(place) => {
                let name = format!("len_{}", place_to_name(place));
                Ok(SymbolicValue::Symbol(name))
            }
            Rvalue::Repeat(op, _) => self.eval_operand(op),
            Rvalue::AddressOf(_, place) => {
                // #776: Return a symbolic address token, not the value at
                // the place. `&raw const x` / `&raw mut x` produce pointer
                // values, distinct from the pointee value.
                let name = place_to_name(place);
                Ok(SymbolicValue::Symbol(format!("addr_{name}")))
            }
            Rvalue::CopyForDeref(place) => {
                let name = place_to_name(place);
                match self.state.try_get(&name) {
                    Some(val) => Ok(val.clone()),
                    None => Ok(SymbolicValue::Symbol(name)),
                }
            }
                    _ => Ok(SymbolicValue::Symbol("unknown_rvalue".into())),
        }
    }

    fn eval_operand(&self, op: &Operand) -> Result<SymbolicValue, SymexError> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let name = place_to_name(place);
                match self.state.try_get(&name) {
                    Some(val) => Ok(val.clone()),
                    None => Ok(SymbolicValue::Symbol(name)),
                }
            }
            Operand::Constant(cv) => Ok(const_to_symbolic(cv)),
            _ => Ok(SymbolicValue::Symbol("unknown_operand".into())),
        }
    }
}

/// Convert a `Place` to a flat variable name for the symbolic state.
#[must_use]
pub(crate) fn place_to_name(place: &Place) -> String {
    let mut name = format!("_local{}", place.local);
    for proj in &place.projections {
        match proj {
            trust_types::Projection::Field(f) => {
                let _ = write!(name, ".f{f}");
            }
            trust_types::Projection::Index(i) => {
                let _ = write!(name, "[{i}]");
            }
            trust_types::Projection::Deref => {
                name.push_str(".*");
            }
            trust_types::Projection::Downcast(v) => {
                let _ = write!(name, "@{v}");
            }
            trust_types::Projection::ConstantIndex { offset, from_end } => {
                if *from_end {
                    let _ = write!(name, "[-{offset}]");
                } else {
                    let _ = write!(name, "[{offset}]");
                }
            }
            trust_types::Projection::Subslice { from, to, from_end } => {
                if *from_end {
                    let _ = write!(name, "[{from}..-{to}]");
                } else {
                    let _ = write!(name, "[{from}..{to}]");
                }
            }
            _ => {},
        }
    }
    name
}

/// tRust #803 P0-5: Extract bit-width and signedness from an operand when possible.
///
/// Returns `Some((width, signed))` for constant operands with known type.
/// Returns `None` for place-based operands (type info not available in symex).
fn infer_operand_type(op: &Operand) -> Option<(u32, bool)> {
    match op {
        Operand::Constant(ConstValue::Uint(_, width)) => Some((*width, false)),
        Operand::Constant(ConstValue::Int(_)) => Some((128, true)),
        _ => None,
    }
}

/// Build a symbolic overflow condition for a checked arithmetic operation.
///
/// tRust #803 P0-5: Uses bit-width-aware range checks instead of algebraic
/// identities that simplify to tautologies in the unbounded symbolic domain.
///
/// When `type_info` is `Some((width, signed))`, overflow is detected by checking
/// whether the mathematical result falls outside the type's representable range:
/// - **Unsigned w-bit:** overflow = `result < 0 || result >= 2^w`
/// - **Signed w-bit:** overflow = `result < -2^(w-1) || result >= 2^(w-1)`
///
/// For multiplication, we use `(rhs != 0) && (result / rhs != lhs)` which is
/// correct because integer division truncates, making this non-tautological
/// for multiplication (unlike addition/subtraction where the inverse is exact).
///
/// When `type_info` is `None`, returns `Concrete(0)` (conservatively assumes
/// no overflow detectable without type information).
fn build_overflow_condition(
    lhs: SymbolicValue,
    op: BinOp,
    rhs: SymbolicValue,
    type_info: Option<(u32, bool)>,
) -> SymbolicValue {
    let result = SymbolicValue::bin_op(lhs.clone(), op, rhs.clone());

    match op {
        BinOp::Add | BinOp::Sub => {
            // For Add/Sub, the algebraic inverse is exact in unbounded arithmetic,
            // so we MUST use range-based checks.
            if let Some((width, signed)) = type_info {
                let (min_val, max_val) = type_range(width, signed);
                // overflow = result < min || result > max
                let below_min = SymbolicValue::bin_op(
                    result.clone(),
                    BinOp::Lt,
                    SymbolicValue::Concrete(min_val),
                );
                let above_max = SymbolicValue::bin_op(
                    result,
                    BinOp::Gt,
                    SymbolicValue::Concrete(max_val),
                );
                // Encode OR as: if below_min then 1 else above_max
                SymbolicValue::ite(
                    below_min,
                    SymbolicValue::Concrete(1),
                    above_max,
                )
            } else {
                // Without type info, cannot detect overflow in unbounded domain.
                SymbolicValue::Concrete(0)
            }
        }
        BinOp::Mul => {
            // For Mul, integer division truncates so (result / rhs != lhs) is
            // NOT a tautology — it correctly detects when the product wraps.
            let rhs_nonzero = SymbolicValue::bin_op(
                rhs.clone(),
                BinOp::Ne,
                SymbolicValue::Concrete(0),
            );
            let div_check = SymbolicValue::bin_op(
                SymbolicValue::bin_op(result, BinOp::Div, rhs),
                BinOp::Ne,
                lhs,
            );
            SymbolicValue::ite(rhs_nonzero, div_check, SymbolicValue::Concrete(0))
        }
        _ => SymbolicValue::Concrete(0),
    }
}

/// Compute the (min, max) representable range for a `width`-bit integer type.
fn type_range(width: u32, signed: bool) -> (i128, i128) {
    if signed {
        if width >= 128 {
            (i128::MIN, i128::MAX)
        } else {
            let half = 1i128 << (width - 1);
            (-half, half - 1)
        }
    } else {
        let max = if width >= 128 {
            i128::MAX
        } else {
            (1i128 << width) - 1
        };
        (0, max)
    }
}

fn const_to_symbolic(cv: &ConstValue) -> SymbolicValue {
    match cv {
        ConstValue::Bool(b) => SymbolicValue::Concrete(i128::from(*b)),
        ConstValue::Int(n) => SymbolicValue::Concrete(*n),
        // tRust: #783 — `as i128` preserves the bit pattern (two's complement / bitvector
        // semantics). Values > i128::MAX wrap to negative, which is the correct bitvector
        // interpretation for our formula representation.
        ConstValue::Uint(n, _) => SymbolicValue::Concrete(*n as i128),
        ConstValue::Float(_) => SymbolicValue::Symbol("float_const".into()),
        ConstValue::Unit => SymbolicValue::Concrete(0),
        _ => SymbolicValue::Symbol("unknown_const".into()),
    }
}

/// Apply a cast to a symbolic value based on the destination type.
///
/// - Integer narrowing: applies a truncation bitmask (e.g. `& 0xFF` for u8).
/// - Signed narrowing: truncates then sign-extends from the destination width.
/// - Unsigned widening: identity (no bits change).
/// - Signed widening: sign-extends from the current value's bit pattern.
///   Without source type info we model this as identity, which is correct when
///   the value was previously truncated to the right width.
/// - Non-integer casts (pointers, floats): identity (passthrough).
fn apply_cast(val: SymbolicValue, dest_ty: &Ty) -> SymbolicValue {
    match dest_ty {
        Ty::Int { width, signed } => {
            let w = *width;
            // Full i128 width or wider — no truncation needed.
            if w >= 128 {
                return val;
            }
            let mask = (1i128 << w) - 1;
            // Truncate to destination width via BitAnd with mask.
            let truncated = SymbolicValue::bin_op(
                val,
                BinOp::BitAnd,
                SymbolicValue::Concrete(mask),
            );
            if *signed {
                // Sign-extend: if the sign bit (bit w-1) is set, the value
                // should be interpreted as negative. We model this as:
                //   ite(truncated & sign_bit != 0, truncated | ~mask, truncated)
                // which sets the high bits for negative values.
                let sign_bit = 1i128 << (w - 1);
                let sign_test = SymbolicValue::bin_op(
                    SymbolicValue::bin_op(
                        truncated.clone(),
                        BinOp::BitAnd,
                        SymbolicValue::Concrete(sign_bit),
                    ),
                    BinOp::Ne,
                    SymbolicValue::Concrete(0),
                );
                let sign_extended = SymbolicValue::bin_op(
                    truncated.clone(),
                    BinOp::BitOr,
                    SymbolicValue::Concrete(!mask),
                );
                SymbolicValue::ite(sign_test, sign_extended, truncated)
            } else {
                // Unsigned: truncation alone is sufficient.
                truncated
            }
        }
        // Non-integer casts (pointers, floats, etc.) — identity.
        _ => val,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{AssertMessage, BlockId, SourceSpan};

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    #[test]
    fn test_engine_execute_assign_and_goto() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
                span: span(),
            }],
            terminator: Terminator::Goto(BlockId(1)),
        };

        let mut exec = SymbolicExecutor::new(100);
        let result = exec.execute_block(&block).expect("should succeed");
        match result {
            BlockResult::Continue(next) => assert_eq!(next, 1),
            other => panic!("expected Continue, got {other:?}"),
        }
        assert_eq!(
            exec.state.get("_local1").unwrap(),
            &SymbolicValue::Concrete(42)
        );
    }

    #[test]
    fn test_engine_switch_int_forks() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Constant(ConstValue::Bool(true)),
                targets: vec![(1, BlockId(1))],
                otherwise: BlockId(2),
                span: span(),
            },
        };

        let mut exec = SymbolicExecutor::new(100);
        let result = exec.execute_block(&block).expect("should succeed");
        match result {
            BlockResult::Fork(forks) => {
                assert_eq!(forks.len(), 2);
                assert_eq!(forks[0].next_block, 1);
                assert_eq!(forks[1].next_block, 2);
            }
            other => panic!("expected Fork, got {other:?}"),
        }
    }

    #[test]
    fn test_engine_return_terminates() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        let result = exec.execute_block(&block).expect("should succeed");
        assert!(matches!(result, BlockResult::Terminated));
    }

    #[test]
    fn test_engine_depth_limit() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Goto(BlockId(0)),
        };

        let mut exec = SymbolicExecutor::new(1);
        exec.execute_block(&block).expect("first block ok");
        let err = exec.execute_block(&block).expect_err("should hit limit");
        assert!(matches!(err, SymexError::DepthLimitExceeded { .. }));
    }

    #[test]
    fn test_engine_assert_adds_constraint() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Assert {
                cond: Operand::Copy(Place::local(1)),
                expected: true,
                msg: AssertMessage::BoundsCheck,
                target: BlockId(1),
                span: span(),
            },
        };

        let mut exec = SymbolicExecutor::new(100);
        let result = exec.execute_block(&block).expect("should succeed");
        match result {
            BlockResult::Continue(1) => {}
            other => panic!("expected Continue(1), got {other:?}"),
        }
        assert_eq!(exec.path.depth(), 1);
    }

    #[test]
    fn test_engine_binary_op_symbolic() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(0)),
                    Operand::Constant(ConstValue::Int(1)),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.state.set("_local0", SymbolicValue::Symbol("arg0".into()));
        exec.execute_block(&block).expect("should succeed");

        let result = exec.state.get("_local2").unwrap();
        match result {
            SymbolicValue::BinOp(_, BinOp::Add, _) => {}
            other => panic!("expected BinOp Add, got {other:?}"),
        }
    }

    #[test]
    fn test_engine_coverage_tracking() {
        let blocks = [BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Return,
            }];

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&blocks[0]).expect("block 0");
        exec.execute_block(&blocks[1]).expect("block 1");
        assert!(exec.coverage.contains(&0));
        assert!(exec.coverage.contains(&1));
        assert_eq!(exec.coverage.len(), 2);
    }

    #[test]
    fn test_engine_place_to_name_projections() {
        let p = Place {
            local: 3,
            projections: vec![
                trust_types::Projection::Field(1),
                trust_types::Projection::Deref,
            ],
        };
        assert_eq!(place_to_name(&p), "_local3.f1.*");
    }

    #[test]
    fn test_engine_from_fork() {
        let mut state = SymbolicState::new();
        state.set("_local0", SymbolicValue::Concrete(7));

        let mut path = PathConstraint::new();
        path.add_constraint(SymbolicValue::Symbol("cond".into()), true);

        let fork = ExecutionFork { state, path, next_block: 3 };
        let exec = SymbolicExecutor::from_fork(fork, 25);

        assert_eq!(
            exec.state.get("_local0").expect("fork state should be preserved"),
            &SymbolicValue::Concrete(7)
        );
        assert_eq!(exec.path.depth(), 1);
        assert!(exec.path.decisions()[0].taken);
        assert!(exec.coverage.is_empty());
        assert_eq!(exec.depth_limit, 25);
        assert_eq!(exec.current_depth, 0);
    }

    #[test]
    fn test_engine_nop_statement() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Nop],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        let result = exec.execute_block(&block).expect("nop block should execute");

        assert!(matches!(result, BlockResult::Terminated));
        assert!(exec.state.is_empty());
    }

    #[test]
    fn test_engine_call_terminator_with_target() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "callee".into(),
                args: vec![],
                dest: Place::local(2),
                target: Some(BlockId(1)),
                span: span(),
                atomic: None,
            },
        };

        let mut exec = SymbolicExecutor::new(100);
        let result = exec.execute_block(&block).expect("call should execute");

        assert!(matches!(result, BlockResult::Continue(1)));
        match exec
            .state
            .get("_local2")
            .expect("call destination should be initialized")
        {
            SymbolicValue::Symbol(name) => {
                assert!(name.starts_with("call_result_"));
                assert!(name.ends_with("_local2"));
            }
            other => panic!("expected fresh call result symbol, got {other:?}"),
        }
    }

    #[test]
    fn test_engine_call_terminator_no_target() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "callee".into(),
                args: vec![],
                dest: Place::local(3),
                target: None,
                span: span(),
                atomic: None,
            },
        };

        let mut exec = SymbolicExecutor::new(100);
        let result = exec
            .execute_block(&block)
            .expect("call without target should terminate");

        assert!(matches!(result, BlockResult::Terminated));
        match exec
            .state
            .get("_local3")
            .expect("call destination should still be initialized")
        {
            SymbolicValue::Symbol(name) => {
                assert!(name.starts_with("call_result_"));
                assert!(name.ends_with("_local3"));
            }
            other => panic!("expected fresh call result symbol, got {other:?}"),
        }
    }

    #[test]
    fn test_engine_drop_terminator() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Drop {
                place: Place::local(1),
                target: BlockId(2),
                span: span(),
            },
        };

        let mut exec = SymbolicExecutor::new(100);
        let result = exec.execute_block(&block).expect("drop should continue");

        assert!(matches!(result, BlockResult::Continue(2)));
    }

    #[test]
    fn test_engine_unary_neg() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::UnaryOp(
                    trust_types::UnOp::Neg,
                    Operand::Constant(ConstValue::Int(5)),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("unary neg should execute");

        let result = exec
            .state
            .get("_local2")
            .expect("unary result should be stored");
        assert_eq!(
            result,
            &SymbolicValue::Neg(Box::new(SymbolicValue::Concrete(5)))
        );
        // Verify concrete evaluation: -5
        let state = crate::state::SymbolicState::new();
        assert_eq!(crate::state::eval(&state, result), Some(-5));
    }

    #[test]
    fn test_engine_unary_not() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::UnaryOp(
                    trust_types::UnOp::Not,
                    Operand::Constant(ConstValue::Int(0)),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("unary not should execute");

        let result = exec
            .state
            .get("_local2")
            .expect("unary not result should be stored");
        assert_eq!(
            result,
            &SymbolicValue::BitwiseNot(Box::new(SymbolicValue::Concrete(0)))
        );
        let state = crate::state::SymbolicState::new();
        assert_eq!(crate::state::eval(&state, result), Some(!0i128));
    }

    #[test]
    fn test_engine_checked_add_overflow_flag() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Add,
                    Operand::Constant(ConstValue::Int(3)),
                    Operand::Constant(ConstValue::Int(4)),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("checked add should execute");

        // Result at place.f0
        let result = exec.state.get("_local2.f0").expect("checked result at f0");
        let state = crate::state::SymbolicState::new();
        assert_eq!(crate::state::eval(&state, result), Some(7));

        // Overflow flag at place.f1 — for non-wrapping add, should eval to 0 (false)
        let overflow = exec.state.get("_local2.f1").expect("overflow flag at f1");
        assert_eq!(crate::state::eval(&state, overflow), Some(0));
    }

    #[test]
    fn test_engine_rvalue_len() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Len(Place::local(3)),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("len rvalue should execute");

        match exec
            .state
            .get("_local2")
            .expect("len result should be stored")
        {
            SymbolicValue::Symbol(name) => {
                assert!(name.starts_with("len_"));
                assert!(name.ends_with("_local3"));
            }
            other => panic!("expected len symbol, got {other:?}"),
        }
    }

    #[test]
    fn test_engine_rvalue_discriminant() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Discriminant(Place::local(4)),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block)
            .expect("discriminant rvalue should execute");

        match exec
            .state
            .get("_local2")
            .expect("discriminant result should be stored")
        {
            SymbolicValue::Symbol(name) => {
                assert!(name.starts_with("discr_"));
                assert!(name.ends_with("_local4"));
            }
            other => panic!("expected discriminant symbol, got {other:?}"),
        }
    }

    // --- Cast tests (Part of #780) ---

    #[test]
    fn test_engine_cast_narrowing_i32_to_u8() {
        // Casting 300_i32 as u8 should truncate to 300 & 0xFF = 44.
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Cast(
                    Operand::Constant(ConstValue::Int(300)),
                    Ty::u8(),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("cast block should execute");

        let result = exec.state.get("_local1").expect("cast result stored");
        let concrete = crate::state::eval(&exec.state, result);
        assert_eq!(concrete, Some(44), "300 & 0xFF = 44");
    }

    #[test]
    fn test_engine_cast_widening_u8_to_u32() {
        // Casting 200_u8 as u32 — value fits, truncation mask is 0xFFFFFFFF,
        // so result should still be 200.
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Cast(
                    Operand::Constant(ConstValue::Int(200)),
                    Ty::u32(),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("widening cast should execute");

        let result = exec.state.get("_local1").expect("widening cast result stored");
        let concrete = crate::state::eval(&exec.state, result);
        assert_eq!(concrete, Some(200), "200 unchanged through u32 widening");
    }

    #[test]
    fn test_engine_cast_sign_extension_i8() {
        // Casting 0xFF (255, which is -1 in i8) as i8 should sign-extend to -1.
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Cast(
                    Operand::Constant(ConstValue::Int(0xFF)),
                    Ty::i8(),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("sign-extend cast should execute");

        let result = exec.state.get("_local1").expect("sign-extend result stored");
        let concrete = crate::state::eval(&exec.state, result);
        assert_eq!(concrete, Some(-1), "0xFF sign-extended as i8 = -1");
    }

    #[test]
    fn test_engine_cast_positive_i8_stays_positive() {
        // Casting 42 as i8 — sign bit is 0, so result remains 42.
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Cast(
                    Operand::Constant(ConstValue::Int(42)),
                    Ty::i8(),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("positive i8 cast should execute");

        let result = exec.state.get("_local1").expect("positive i8 result stored");
        let concrete = crate::state::eval(&exec.state, result);
        assert_eq!(concrete, Some(42), "42 fits in i8 without sign extension");
    }

    #[test]
    fn test_engine_cast_narrowing_u16() {
        // Casting 0x1_FFFF (131071) as u16 should truncate to 0xFFFF = 65535.
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Cast(
                    Operand::Constant(ConstValue::Int(0x1_FFFF)),
                    Ty::u16(),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("u16 truncation should execute");

        let result = exec.state.get("_local1").expect("u16 truncation result stored");
        let concrete = crate::state::eval(&exec.state, result);
        assert_eq!(concrete, Some(0xFFFF), "0x1_FFFF & 0xFFFF = 0xFFFF");
    }

    #[test]
    fn test_engine_cast_pointer_identity() {
        // Pointer casts should pass through unchanged.
        let ptr_ty = Ty::RawPtr {
            mutable: false,
            pointee: Box::new(Ty::u8()),
        };
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Cast(
                    Operand::Constant(ConstValue::Int(0xDEAD)),
                    ptr_ty,
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("pointer cast should execute");

        let result = exec.state.get("_local1").expect("pointer cast result stored");
        let concrete = crate::state::eval(&exec.state, result);
        assert_eq!(concrete, Some(0xDEAD), "pointer cast is identity");
    }

    #[test]
    fn test_apply_cast_concrete_truncation() {
        // Direct unit test for apply_cast: 0x1234 truncated to u8 = 0x34.
        let val = SymbolicValue::Concrete(0x1234);
        let result = apply_cast(val, &Ty::u8());
        let state = SymbolicState::new();
        assert_eq!(crate::state::eval(&state, &result), Some(0x34));
    }

    #[test]
    fn test_apply_cast_signed_negative() {
        // Direct unit test: 0x80 as i8 should sign-extend to -128.
        let val = SymbolicValue::Concrete(0x80);
        let result = apply_cast(val, &Ty::i8());
        let state = SymbolicState::new();
        assert_eq!(crate::state::eval(&state, &result), Some(-128));
    }
}
