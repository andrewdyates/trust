// trust-cegar: Lazy refinement — only refine along counterexample paths
//
// CPAchecker's key optimization: instead of re-abstracting the entire program
// when a spurious counterexample is found, only refine the predicates along
// the specific path in the counterexample trace.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{BasicBlock, Counterexample, CounterexampleValue};

use crate::error::CegarError;
use crate::predicate::{AbstractState, CmpOp, Predicate, abstract_block};

/// Lazy refinement: refine only along counterexample paths.
///
/// Instead of eagerly refining the whole abstract model, `LazyRefiner` focuses
/// refinement effort on the blocks that appear in the counterexample trace.
/// This is much cheaper for large programs where most of the abstraction is
/// already precise enough.
#[derive(Debug)]
pub struct LazyRefiner {
    /// All predicates discovered so far across all refinements.
    predicates: Vec<Predicate>,
    /// Number of refinements performed.
    refinement_count: usize,
}

impl LazyRefiner {
    /// Create a new lazy refiner with optional initial predicates.
    #[must_use]
    pub fn new(initial_predicates: Vec<Predicate>) -> Self {
        Self { predicates: initial_predicates, refinement_count: 0 }
    }

    /// Access the current predicate set.
    #[must_use]
    pub fn predicates(&self) -> &[Predicate] {
        &self.predicates
    }

    /// Number of refinements completed.
    #[must_use]
    pub fn refinement_count(&self) -> usize {
        self.refinement_count
    }

    /// Refine predicates along a counterexample path.
    ///
    /// The `path` is a sequence of block indices (into the `blocks` array)
    /// representing the counterexample trace. We:
    ///
    /// 1. Walk the path forward, computing abstract states at each block.
    /// 2. At each step, check if the counterexample assignments contradict
    ///    the abstract state.
    /// 3. When we find a contradiction point, extract interpolant predicates
    ///    from the conflict.
    ///
    /// # Arguments
    /// * `path` - Block indices along the counterexample trace.
    /// * `blocks` - All basic blocks in the function.
    /// * `cex` - The counterexample to refine against.
    ///
    /// # Errors
    /// Returns `CegarError::InvalidBlockIndex` if any path index is out of bounds.
    pub fn refine_path(
        &mut self,
        path: &[usize],
        blocks: &[BasicBlock],
        cex: &Counterexample,
    ) -> Result<Vec<Predicate>, CegarError> {
        // Validate path indices.
        for &idx in path {
            if idx >= blocks.len() {
                return Err(CegarError::InvalidBlockIndex { index: idx, num_blocks: blocks.len() });
            }
        }

        let mut new_predicates = Vec::new();
        let mut accumulated_state = AbstractState::top();

        for &block_idx in path {
            let block = &blocks[block_idx];

            // Compute abstract state at this block.
            let block_state = abstract_block(block, &self.predicates);

            // Accumulate (meet = conjunction).
            accumulated_state = accumulated_state.meet(&block_state);

            // Extract interpolant predicates at this program point.
            let interpolants = self.extract_interpolants(&accumulated_state, cex, block_idx);
            for pred in interpolants {
                if !self.predicates.contains(&pred) && !new_predicates.contains(&pred) {
                    new_predicates.push(pred);
                }
            }
        }

        // Add discovered predicates to our set.
        for pred in &new_predicates {
            if !self.predicates.contains(pred) {
                self.predicates.push(pred.clone());
            }
        }

        self.refinement_count += 1;
        Ok(new_predicates)
    }

    /// Extract interpolant predicates from the conflict between an abstract
    /// state and a counterexample at a specific block.
    ///
    /// This is a simplified Craig interpolation: we look at the counterexample
    /// values and the abstract state to find predicates that would separate
    /// the feasible from the infeasible paths.
    fn extract_interpolants(
        &self,
        state: &AbstractState,
        cex: &Counterexample,
        _block_idx: usize,
    ) -> Vec<Predicate> {
        let mut interpolants = Vec::new();

        for (var_name, value) in &cex.assignments {
            match value {
                CounterexampleValue::Int(n) => {
                    // If the counterexample value is negative, add non-negativity.
                    if *n < 0 {
                        let ge_zero = Predicate::comparison(var_name, CmpOp::Ge, "0");
                        if !state.contains(&ge_zero) {
                            interpolants.push(ge_zero);
                        }
                    }
                    // Add equality predicate for exact value.
                    let eq = Predicate::comparison(var_name, CmpOp::Eq, n.to_string());
                    if !state.contains(&eq) {
                        interpolants.push(eq);
                    }
                }
                CounterexampleValue::Uint(n) => {
                    // For unsigned, check boundary conditions.
                    if *n == 0 {
                        let eq_zero = Predicate::comparison(var_name, CmpOp::Eq, "0");
                        if !state.contains(&eq_zero) {
                            interpolants.push(eq_zero);
                        }
                    } else {
                        let gt_zero = Predicate::comparison(var_name, CmpOp::Gt, "0");
                        if !state.contains(&gt_zero) {
                            interpolants.push(gt_zero);
                        }
                    }
                }
                CounterexampleValue::Bool(b) => {
                    let val_str = if *b { "1" } else { "0" };
                    let eq = Predicate::comparison(var_name, CmpOp::Eq, val_str);
                    if !state.contains(&eq) {
                        interpolants.push(eq);
                    }
                }
                CounterexampleValue::Float(_) => {
                    // Floats are complex; skip for now.
                }
                _ => {},
            }
        }

        // Generate pairwise ordering predicates between integer vars on the path.
        let int_vars: Vec<(&str, i128)> = cex
            .assignments
            .iter()
            .filter_map(|(name, val)| match val {
                CounterexampleValue::Int(n) => Some((name.as_str(), *n)),
                CounterexampleValue::Uint(n) => {
                    i128::try_from(*n).ok().map(|n| (name.as_str(), n))
                }
                _ => None,
            })
            .collect();

        for i in 0..int_vars.len() {
            for j in (i + 1)..int_vars.len() {
                let (a, a_val) = int_vars[i];
                let (b, b_val) = int_vars[j];
                let op = if a_val <= b_val { CmpOp::Le } else { CmpOp::Gt };
                let pred = Predicate::comparison(a, op, b);
                if !state.contains(&pred) {
                    interpolants.push(pred);
                }
            }
        }

        interpolants
    }

    /// Compute abstract states only for blocks on the given path.
    ///
    /// Returns the abstract state at each block in the path, in order.
    ///
    /// # Errors
    /// Returns `CegarError::InvalidBlockIndex` if any index is out of bounds.
    pub fn abstract_path(
        &self,
        path: &[usize],
        blocks: &[BasicBlock],
    ) -> Result<Vec<AbstractState>, CegarError> {
        let mut states = Vec::with_capacity(path.len());
        for &idx in path {
            if idx >= blocks.len() {
                return Err(CegarError::InvalidBlockIndex { index: idx, num_blocks: blocks.len() });
            }
            states.push(abstract_block(&blocks[idx], &self.predicates));
        }
        Ok(states)
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{BlockId, ConstValue, Operand, Place, Rvalue, SourceSpan, Statement, Terminator};

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn simple_blocks() -> Vec<BasicBlock> {
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                    span: span(),
                }],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        trust_types::BinOp::Lt,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(3)),
                    ),
                    span: span(),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(1, BlockId(2))],
                    otherwise: BlockId(3),
                    span: span(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ]
    }

    #[test]
    fn test_lazy_refine_path_basic() {
        let mut refiner = LazyRefiner::new(vec![]);
        let blocks = simple_blocks();
        let cex = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(-1)),
            ("y".to_string(), CounterexampleValue::Int(10)),
        ]);

        let new_preds = refiner.refine_path(&[0, 1], &blocks, &cex).unwrap();
        assert!(!new_preds.is_empty());
        assert_eq!(refiner.refinement_count(), 1);
    }

    #[test]
    fn test_lazy_refine_path_invalid_index() {
        let mut refiner = LazyRefiner::new(vec![]);
        let blocks = simple_blocks();
        let cex = Counterexample::new(vec![]);
        let result = refiner.refine_path(&[0, 99], &blocks, &cex);
        assert!(matches!(
            result,
            Err(CegarError::InvalidBlockIndex { index: 99, num_blocks: 4 })
        ));
    }

    #[test]
    fn test_lazy_refine_accumulates_predicates() {
        let mut refiner = LazyRefiner::new(vec![]);
        let blocks = simple_blocks();

        let cex1 = Counterexample::new(vec![
            ("a".to_string(), CounterexampleValue::Int(-5)),
        ]);
        let preds1 = refiner.refine_path(&[0, 1], &blocks, &cex1).unwrap();
        let count_after_1 = refiner.predicates().len();

        let cex2 = Counterexample::new(vec![
            ("b".to_string(), CounterexampleValue::Uint(100)),
        ]);
        let preds2 = refiner.refine_path(&[1, 2], &blocks, &cex2).unwrap();

        assert!(!preds1.is_empty());
        assert!(!preds2.is_empty());
        assert!(refiner.predicates().len() >= count_after_1);
        assert_eq!(refiner.refinement_count(), 2);
    }

    #[test]
    fn test_abstract_path_computes_states() {
        let refiner = LazyRefiner::new(vec![
            Predicate::comparison("_1", CmpOp::Ge, "0"),
        ]);
        let blocks = simple_blocks();
        let states = refiner.abstract_path(&[0, 2], &blocks).unwrap();
        assert_eq!(states.len(), 2);
    }

    #[test]
    fn test_abstract_path_invalid_index() {
        let refiner = LazyRefiner::new(vec![]);
        let blocks = simple_blocks();
        let result = refiner.abstract_path(&[10], &blocks);
        assert!(matches!(result, Err(CegarError::InvalidBlockIndex { .. })));
    }

    #[test]
    fn test_lazy_refiner_empty_path() {
        let mut refiner = LazyRefiner::new(vec![]);
        let blocks = simple_blocks();
        let cex = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(42)),
        ]);
        let new_preds = refiner.refine_path(&[], &blocks, &cex).unwrap();
        // Empty path should not extract many predicates (no blocks to walk).
        // But it still increments the refinement count.
        assert_eq!(refiner.refinement_count(), 1);
        assert!(new_preds.is_empty());
    }
}
