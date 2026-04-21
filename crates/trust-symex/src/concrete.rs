// trust-symex concrete executor
//
// Execute MIR statements concretely while tracking which values are symbolic.
// When a symbolic value affects control flow, record the branch point for
// the concolic engine to explore alternative paths.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use serde::{Deserialize, Serialize};
use trust_types::{BasicBlock, BinOp, BlockId, ConstValue, Operand, Rvalue, Terminator};

use crate::engine::place_to_name;
use crate::error::SymexError;
use crate::path::PathConstraint;
use crate::state::SymbolicValue;

/// A concrete value paired with its symbolic shadow.
///
/// During concolic execution every value has both a concrete component
/// (used to drive execution deterministically) and a symbolic component
/// (used to build path constraints for the solver).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConcolicValue {
    /// The concrete integer value used for execution.
    pub concrete: i128,
    /// The symbolic expression shadowing this value. `None` when the value
    /// is purely concrete (no input dependency).
    pub symbolic: Option<SymbolicValue>,
}

impl ConcolicValue {
    /// Create a purely concrete value with no symbolic shadow.
    #[must_use]
    pub(crate) fn concrete(value: i128) -> Self {
        Self {
            concrete: value,
            symbolic: None,
        }
    }

    /// Create a concolic value with both concrete and symbolic components.
    #[must_use]
    pub(crate) fn with_shadow(concrete: i128, symbolic: SymbolicValue) -> Self {
        Self {
            concrete,
            symbolic: Some(symbolic),
        }
    }

    /// Returns `true` if this value has a symbolic shadow.
    #[must_use]
    pub(crate) fn is_symbolic(&self) -> bool {
        self.symbolic.is_some()
    }

    /// Get the symbolic expression, falling back to a concrete literal.
    #[must_use]
    pub(crate) fn to_symbolic(&self) -> SymbolicValue {
        self.symbolic
            .clone()
            .unwrap_or(SymbolicValue::Concrete(self.concrete))
    }
}

/// A branch point detected during concrete execution where a symbolic
/// value influenced control flow.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct SymbolicBranchPoint {
    /// The block in which the branch occurs.
    pub block_id: usize,
    /// The symbolic condition at the branch.
    pub condition: SymbolicValue,
    /// The direction taken during concrete execution.
    pub taken: bool,
    /// Index of this decision within the path.
    pub decision_index: usize,
}

/// The concrete executor: runs MIR blocks using concrete values while
/// maintaining symbolic shadows for constraint collection.
#[derive(Debug, Clone)]
pub(crate) struct ConcreteExecutor {
    /// Mapping from variable names to concolic values.
    vars: FxHashMap<String, ConcolicValue>,
    /// Path constraints accumulated during execution.
    pub(crate) path: PathConstraint,
    /// Branch points where symbolic values affected control flow.
    pub(crate) symbolic_branches: Vec<SymbolicBranchPoint>,
    /// Maximum number of blocks to execute before aborting.
    pub(crate) step_limit: usize,
    /// Current step count.
    pub(crate) steps: usize,
}

impl ConcreteExecutor {
    /// Create a new concrete executor.
    #[must_use]
    pub(crate) fn new(step_limit: usize) -> Self {
        Self {
            vars: FxHashMap::default(),
            path: PathConstraint::new(),
            symbolic_branches: Vec::new(),
            step_limit,
            steps: 0,
        }
    }

    /// Bind a variable to a concolic value.
    pub(crate) fn set_input(&mut self, name: impl Into<String>, value: ConcolicValue) {
        self.vars.insert(name.into(), value);
    }

    /// Bind a symbolic input: the concrete seed plus a named symbolic variable.
    pub(crate) fn set_symbolic_input(&mut self, name: impl Into<String>, concrete_seed: i128) {
        let n: String = name.into();
        let cv = ConcolicValue::with_shadow(concrete_seed, SymbolicValue::Symbol(n.clone()));
        self.vars.insert(n, cv);
    }

    /// Get the concolic value of a variable, returning a purely concrete 0 if absent.
    #[must_use]
    pub(crate) fn get(&self, name: &str) -> ConcolicValue {
        self.vars
            .get(name)
            .cloned()
            .unwrap_or(ConcolicValue::concrete(0))
    }

    /// Returns the symbolic branches collected so far.
    #[must_use]
    pub(crate) fn branches(&self) -> &[SymbolicBranchPoint] {
        &self.symbolic_branches
    }

    /// Returns the accumulated path constraint.
    #[must_use]
    pub(crate) fn path_constraint(&self) -> &PathConstraint {
        &self.path
    }

    /// Execute a single basic block concretely.
    ///
    /// Returns the ID of the next block to execute, or `None` if the block
    /// terminates (return / unreachable).
    pub(crate) fn execute_block(&mut self, block: &BasicBlock) -> Result<Option<usize>, SymexError> {
        if self.steps >= self.step_limit {
            return Err(SymexError::DepthLimitExceeded {
                depth: self.steps,
                limit: self.step_limit,
            });
        }
        self.steps += 1;

        // Execute statements.
        for stmt in &block.stmts {
            self.execute_statement(stmt)?;
        }

        // Process terminator.
        self.execute_terminator(block.id, &block.terminator)
    }

    fn execute_statement(
        &mut self,
        stmt: &trust_types::Statement,
    ) -> Result<(), SymexError> {
        match stmt {
            trust_types::Statement::Assign { place, rvalue, .. } => {
                let val = self.eval_rvalue(rvalue)?;
                let name = place_to_name(place);
                self.vars.insert(name, val);
                Ok(())
            }
            trust_types::Statement::Nop => Ok(()),
            other => Err(SymexError::UnsupportedOperation(
                format!("unhandled Statement variant: {other:?}"),
            )),
        }
    }

    fn execute_terminator(
        &mut self,
        block_id: BlockId,
        term: &Terminator,
    ) -> Result<Option<usize>, SymexError> {
        match term {
            Terminator::Goto(target) => Ok(Some(target.0)),
            Terminator::Return => Ok(None),
            Terminator::Unreachable => Err(SymexError::UnreachableReached),
            Terminator::SwitchInt {
                discr,
                targets,
                otherwise,
                ..
            } => {
                let discr_val = self.eval_operand(discr)?;
                let concrete_discr = discr_val.concrete;

                // Record symbolic branch if the discriminant has a symbolic shadow.
                if discr_val.is_symbolic() {
                    // Record constraints for each target comparison.
                    let mut matched_target = None;
                    for (value, target) in targets {
                        let cond = SymbolicValue::bin_op(
                            discr_val.to_symbolic(),
                            BinOp::Eq,
                            SymbolicValue::Concrete(*value as i128),
                        );
                        let taken = concrete_discr == *value as i128;
                        let decision_index = self.symbolic_branches.len();
                        self.symbolic_branches.push(SymbolicBranchPoint {
                            block_id: block_id.0,
                            condition: cond.clone(),
                            taken,
                            decision_index,
                        });
                        self.path.add_constraint(cond, taken);
                        if taken {
                            matched_target = Some(target.0);
                        }
                    }
                    return Ok(Some(matched_target.unwrap_or(otherwise.0)));
                }

                // Pure concrete dispatch.
                for (value, target) in targets {
                    if concrete_discr == *value as i128 {
                        return Ok(Some(target.0));
                    }
                }
                Ok(Some(otherwise.0))
            }
            Terminator::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                let cond_val = self.eval_operand(cond)?;
                if cond_val.is_symbolic() {
                    let sym_cond = if *expected {
                        cond_val.to_symbolic()
                    } else {
                        SymbolicValue::Not(Box::new(cond_val.to_symbolic()))
                    };
                    self.path.add_constraint(sym_cond, true);
                }
                Ok(Some(target.0))
            }
            Terminator::Call { dest, target, .. } => {
                let name = place_to_name(dest);
                let fresh = ConcolicValue::with_shadow(
                    0,
                    SymbolicValue::Symbol(format!("call_result_{name}")),
                );
                self.vars.insert(name, fresh);
                match target {
                    Some(t) => Ok(Some(t.0)),
                    None => Ok(None),
                }
            }
            Terminator::Drop { target, .. } => Ok(Some(target.0)),
            other => Err(SymexError::UnsupportedOperation(
                format!("unhandled Terminator variant: {other:?}"),
            )),
        }
    }

    fn eval_rvalue(&self, rvalue: &Rvalue) -> Result<ConcolicValue, SymexError> {
        match rvalue {
            Rvalue::Use(op) => self.eval_operand(op),
            Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
                let l = self.eval_operand(lhs)?;
                let r = self.eval_operand(rhs)?;
                let concrete = eval_concrete_binop(l.concrete, *op, r.concrete)?;
                let symbolic = if l.is_symbolic() || r.is_symbolic() {
                    Some(SymbolicValue::bin_op(l.to_symbolic(), *op, r.to_symbolic()))
                } else {
                    None
                };
                Ok(ConcolicValue {
                    concrete,
                    symbolic,
                })
            }
            Rvalue::UnaryOp(un_op, op) => {
                let v = self.eval_operand(op)?;
                match un_op {
                    trust_types::UnOp::Neg => {
                        let concrete = -v.concrete;
                        let symbolic = v.symbolic.map(|s| SymbolicValue::Neg(Box::new(s)));
                        Ok(ConcolicValue { concrete, symbolic })
                    }
                    trust_types::UnOp::Not => {
                        let concrete = !v.concrete;
                        let symbolic =
                            v.symbolic.map(|s| SymbolicValue::BitwiseNot(Box::new(s)));
                        Ok(ConcolicValue { concrete, symbolic })
                    }
                    trust_types::UnOp::PtrMetadata | _ => {
                        // PtrMetadata extracts length from fat pointers; use 0 as
                        // concrete stand-in and a fresh symbol for the symbolic side.
                        Ok(ConcolicValue {
                            concrete: 0,
                            symbolic: Some(SymbolicValue::Symbol(
                                "ptrmeta_concolic".to_owned(),
                            )),
                        })
                    }
                }
            }
            Rvalue::Ref { place, .. } => {
                let name = place_to_name(place);
                Ok(self.get(&name))
            }
            Rvalue::Cast(op, _) => self.eval_operand(op),
            Rvalue::Aggregate(_, ops) => {
                if let Some(first) = ops.first() {
                    self.eval_operand(first)
                } else {
                    Ok(ConcolicValue::concrete(0))
                }
            }
            Rvalue::Discriminant(place) => {
                let name = format!("discr_{}", place_to_name(place));
                Ok(ConcolicValue::with_shadow(
                    0,
                    SymbolicValue::Symbol(name),
                ))
            }
            Rvalue::Len(place) => {
                let name = format!("len_{}", place_to_name(place));
                Ok(ConcolicValue::with_shadow(
                    0,
                    SymbolicValue::Symbol(name),
                ))
            }
            Rvalue::Repeat(op, _) => self.eval_operand(op),
            Rvalue::AddressOf(_, place) => {
                let name = place_to_name(place);
                Ok(self.get(&name))
            }
            Rvalue::CopyForDeref(place) => {
                let name = place_to_name(place);
                Ok(self.get(&name))
            }
            other => Err(SymexError::UnsupportedOperation(
                format!("unhandled Rvalue variant: {other:?}"),
            )),
        }
    }

    fn eval_operand(&self, op: &Operand) -> Result<ConcolicValue, SymexError> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let name = place_to_name(place);
                Ok(self.get(&name))
            }
            Operand::Constant(cv) => const_to_concolic(cv),
            other => Err(SymexError::UnsupportedOperation(
                format!("unhandled Operand variant: {other:?}"),
            )),
        }
    }
}

/// Evaluate a binary operation on concrete values. Returns 0 on overflow/div-by-zero.
fn eval_concrete_binop(l: i128, op: BinOp, r: i128) -> Result<i128, SymexError> {
    match op {
        BinOp::Add => Ok(l.wrapping_add(r)),
        BinOp::Sub => Ok(l.wrapping_sub(r)),
        BinOp::Mul => Ok(l.wrapping_mul(r)),
        BinOp::Div => {
            if r == 0 { Ok(0) } else { Ok(l.wrapping_div(r)) }
        }
        BinOp::Rem => {
            if r == 0 { Ok(0) } else { Ok(l.wrapping_rem(r)) }
        }
        BinOp::Eq => Ok(i128::from(l == r)),
        BinOp::Ne => Ok(i128::from(l != r)),
        BinOp::Lt => Ok(i128::from(l < r)),
        BinOp::Le => Ok(i128::from(l <= r)),
        BinOp::Gt => Ok(i128::from(l > r)),
        BinOp::Ge => Ok(i128::from(l >= r)),
        BinOp::BitAnd => Ok(l & r),
        BinOp::BitOr => Ok(l | r),
        BinOp::BitXor => Ok(l ^ r),
        // tRust #784: Clamp shift to valid range; large shifts produce 0.
        BinOp::Shl => Ok(l.wrapping_shl(u32::try_from(r).unwrap_or(128).min(127))),
        BinOp::Shr => Ok(l.wrapping_shr(u32::try_from(r).unwrap_or(128).min(127))),
        // tRust #383: Three-way comparison returns -1 (Less), 0 (Equal), or 1 (Greater).
        BinOp::Cmp => {
            Ok(if l < r { -1 } else if l == r { 0 } else { 1 })
        }
        other => Err(SymexError::UnsupportedOperation(
            format!("unhandled BinOp variant: {other:?}"),
        )),
    }
}

fn const_to_concolic(cv: &ConstValue) -> Result<ConcolicValue, SymexError> {
    match cv {
        ConstValue::Bool(b) => Ok(ConcolicValue::concrete(i128::from(*b))),
        ConstValue::Int(n) => Ok(ConcolicValue::concrete(*n)),
        // tRust: #783 — two's complement cast preserves bitvector semantics.
        ConstValue::Uint(n, _) => Ok(ConcolicValue::concrete(*n as i128)),
        ConstValue::Float(f) => Ok(ConcolicValue::concrete(*f as i128)),
        ConstValue::Unit => Ok(ConcolicValue::concrete(0)),
        other => Err(SymexError::UnsupportedOperation(
            format!("unhandled ConstValue variant: {other:?}"),
        )),
    }
}

/// Run blocks concretely from an entry point to termination.
///
/// Returns the executor after execution completes (or hits the step limit).
pub(crate) fn run_concrete(
    blocks: &[BasicBlock],
    inputs: &FxHashMap<String, ConcolicValue>,
    step_limit: usize,
) -> Result<ConcreteExecutor, SymexError> {
    let mut executor = ConcreteExecutor::new(step_limit);
    for (name, val) in inputs {
        executor.set_input(name.clone(), val.clone());
    }

    let mut current_block = 0usize;
    loop {
        let block = blocks.get(current_block).ok_or_else(|| {
            SymexError::UnsupportedOperation(format!("block {current_block} out of range"))
        })?;
        match executor.execute_block(block)? {
            Some(next) => current_block = next,
            None => break,
        }
    }

    Ok(executor)
}

#[cfg(test)]
mod tests {
    use trust_types::{BlockId, Place, SourceSpan, Statement};

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    #[test]
    fn test_concrete_pure_concrete_execution() {
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
                    span: span(),
                }],
                terminator: Terminator::Return,
            },
        ];
        let inputs = FxHashMap::default();
        let exec = run_concrete(&blocks, &inputs, 100).expect("should succeed");
        let val = exec.get("_local1");
        assert_eq!(val.concrete, 42);
        assert!(!val.is_symbolic());
    }

    #[test]
    fn test_concrete_symbolic_input_tracking() {
        let mut executor = ConcreteExecutor::new(100);
        executor.set_symbolic_input("x", 5);
        let val = executor.get("x");
        assert_eq!(val.concrete, 5);
        assert!(val.is_symbolic());
        match val.to_symbolic() {
            SymbolicValue::Symbol(name) => assert_eq!(name, "x"),
            other => panic!("expected Symbol, got {other:?}"),
        }
    }

    #[test]
    fn test_concrete_binary_op_symbolic_propagation() {
        let blocks = vec![BasicBlock {
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
        }];

        let mut inputs = FxHashMap::default();
        inputs.insert(
            "_local0".to_string(),
            ConcolicValue::with_shadow(10, SymbolicValue::Symbol("arg0".into())),
        );

        let exec = run_concrete(&blocks, &inputs, 100).expect("should succeed");
        let result = exec.get("_local2");
        assert_eq!(result.concrete, 11); // 10 + 1
        assert!(result.is_symbolic());
    }

    #[test]
    fn test_concrete_switch_records_symbolic_branch() {
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(0)),
                    targets: vec![(1, BlockId(1))],
                    otherwise: BlockId(2),
                    span: span(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];

        let mut inputs = FxHashMap::default();
        inputs.insert(
            "_local0".to_string(),
            ConcolicValue::with_shadow(1, SymbolicValue::Symbol("input".into())),
        );

        let exec = run_concrete(&blocks, &inputs, 100).expect("should succeed");
        assert!(!exec.symbolic_branches.is_empty());
        // With concrete value 1, should take the first target (value == 1).
        assert!(exec.symbolic_branches[0].taken);
    }

    #[test]
    fn test_concrete_step_limit() {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Goto(BlockId(0)),
        }];
        let inputs = FxHashMap::default();
        let result = run_concrete(&blocks, &inputs, 3);
        assert!(result.is_err());
    }

    #[test]
    fn test_concolic_value_pure_concrete() {
        let v = ConcolicValue::concrete(42);
        assert!(!v.is_symbolic());
        assert_eq!(v.concrete, 42);
        assert_eq!(v.to_symbolic(), SymbolicValue::Concrete(42));
    }

    #[test]
    fn test_concolic_value_with_shadow() {
        let v = ConcolicValue::with_shadow(5, SymbolicValue::Symbol("x".into()));
        assert!(v.is_symbolic());
        assert_eq!(v.concrete, 5);
        match v.to_symbolic() {
            SymbolicValue::Symbol(name) => assert_eq!(name, "x"),
            other => panic!("expected Symbol, got {other:?}"),
        }
    }

    #[test]
    fn test_concrete_goto_chain() {
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(99))),
                    span: span(),
                }],
                terminator: Terminator::Return,
            },
        ];
        let exec = run_concrete(&blocks, &FxHashMap::default(), 100).expect("should succeed");
        assert_eq!(exec.get("_local1").concrete, 99);
        assert_eq!(exec.steps, 2);
    }

    #[test]
    fn test_eval_concrete_binop_div_by_zero() {
        assert_eq!(eval_concrete_binop(10, BinOp::Div, 0).unwrap(), 0);
        assert_eq!(eval_concrete_binop(10, BinOp::Rem, 0).unwrap(), 0);
    }

    #[test]
    fn test_eval_concrete_binop_comparisons() {
        assert_eq!(eval_concrete_binop(3, BinOp::Lt, 5).unwrap(), 1);
        assert_eq!(eval_concrete_binop(5, BinOp::Lt, 3).unwrap(), 0);
        assert_eq!(eval_concrete_binop(3, BinOp::Eq, 3).unwrap(), 1);
        assert_eq!(eval_concrete_binop(3, BinOp::Ne, 3).unwrap(), 0);
    }
}
