// trust-router counterexample replay via symbolic execution
//
// When a solver (e.g. z4) returns a counterexample, the abstract trace may be
// spurious due to over-approximation. This module replays the counterexample
// concretely through trust-symex's SymbolicExecutor to distinguish real bugs
// from spurious paths. Spurious paths produce UnsatPath data usable by CEGAR
// for predicate refinement.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use thiserror::Error;
use trust_symex::engine::SymbolicExecutor;
use trust_symex::path::PathConstraint;
use trust_symex::state::{SymbolicState, SymbolicValue};
use trust_types::{
    BasicBlock, Counterexample, CounterexampleValue, Formula, VerificationCondition,
};

/// Errors arising during counterexample replay.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ReplayError {
    #[error("symbolic execution failed: {0}")]
    SymexError(#[from] trust_symex::SymexError),

    #[error("no basic blocks provided for replay")]
    NoBlocks,

    #[error("block index {0} out of range (have {1} blocks)")]
    BlockOutOfRange(usize, usize),

    #[error("replay depth limit exceeded after {0} steps")]
    DepthLimitExceeded(usize),
}

/// Result of replaying a counterexample through concrete symbolic execution.
#[derive(Debug)]
pub enum ReplayResult {
    /// The counterexample is real: concrete execution confirms the violation.
    RealBug(ConcreteCounterexample),
    /// The counterexample is spurious: the path is infeasible.
    /// Contains the unsatisfiable path for CEGAR predicate refinement.
    Spurious(UnsatPath),
}

/// A confirmed concrete counterexample with the execution trace.
#[derive(Debug)]
pub struct ConcreteCounterexample {
    /// The original solver counterexample that was validated.
    pub counterexample: Counterexample,
    /// Final symbolic state after replay (all values concrete).
    pub final_state: SymbolicState,
    /// Blocks visited during replay.
    pub trace: Vec<usize>,
}

/// An unsatisfiable path discovered during replay.
///
/// When the solver's counterexample leads to an infeasible path through
/// the CFG, the path constraints and interpolant can be used by CEGAR
/// to refine the abstraction.
#[derive(Debug)]
pub struct UnsatPath {
    /// The path constraints that are unsatisfiable together.
    pub path: PathConstraint,
    /// Blocks visited before the path became infeasible.
    pub partial_trace: Vec<usize>,
    /// The formula representation of the infeasible path, suitable for
    /// Craig interpolation in trust-cegar.
    pub path_formula: Formula,
}

/// Configuration for counterexample replay.
#[derive(Debug, Clone)]
pub struct ReplayConfig {
    /// Maximum number of blocks to execute during replay.
    pub depth_limit: usize,
    /// Entry block index (usually 0).
    pub entry_block: usize,
}

impl Default for ReplayConfig {
    fn default() -> Self {
        Self { depth_limit: 1000, entry_block: 0 }
    }
}

/// Replay a solver counterexample through concrete symbolic execution.
///
/// Takes a counterexample (variable assignments from z4), the VC that
/// produced it, and the CFG blocks of the function under verification.
/// Executes the path concretely to determine if the bug is real or spurious.
///
/// # Errors
///
/// Returns `ReplayError` if the blocks are empty, indices are out of range,
/// or the depth limit is exceeded.
pub fn replay_counterexample(
    counterexample: &Counterexample,
    _vc: &VerificationCondition,
    blocks: &[BasicBlock],
    config: &ReplayConfig,
) -> Result<ReplayResult, ReplayError> {
    if blocks.is_empty() {
        return Err(ReplayError::NoBlocks);
    }
    if config.entry_block >= blocks.len() {
        return Err(ReplayError::BlockOutOfRange(config.entry_block, blocks.len()));
    }

    // Initialize the symbolic executor with concrete values from the counterexample.
    let mut executor = SymbolicExecutor::new(config.depth_limit);
    seed_state_from_counterexample(&mut executor.state, counterexample);

    let mut trace = Vec::new();
    let mut current_block = config.entry_block;

    loop {
        if current_block >= blocks.len() {
            return Err(ReplayError::BlockOutOfRange(current_block, blocks.len()));
        }

        trace.push(current_block);
        let block = &blocks[current_block];

        match executor.execute_block(block) {
            Ok(trust_symex::BlockResult::Continue(next)) => {
                current_block = next;
            }
            Ok(trust_symex::BlockResult::Fork(forks)) => {
                // With concrete inputs, try to find the feasible branch.
                match find_feasible_fork(&executor.state, &forks) {
                    Some(fork) => {
                        // Apply the fork's state and path, continue execution.
                        executor.state = fork.state.clone();
                        executor.path = fork.path.clone();
                        current_block = fork.next_block;
                    }
                    None => {
                        // No branch is feasible with these concrete inputs:
                        // the counterexample is spurious.
                        let path_formula = executor.path.to_formula();
                        return Ok(ReplayResult::Spurious(UnsatPath {
                            path: executor.path,
                            partial_trace: trace,
                            path_formula,
                        }));
                    }
                }
            }
            Ok(trust_symex::BlockResult::Terminated) => {
                // Execution completed. Check if final state is fully concrete
                // to confirm the bug is real.
                return Ok(confirm_or_spurious(
                    counterexample,
                    executor.state,
                    executor.path,
                    trace,
                ));
            }
            Err(trust_symex::SymexError::DepthLimitExceeded { depth, .. }) => {
                return Err(ReplayError::DepthLimitExceeded(depth));
            }
            Err(trust_symex::SymexError::UnreachableReached) => {
                // Hit unreachable during concrete replay: path is infeasible.
                let path_formula = executor.path.to_formula();
                return Ok(ReplayResult::Spurious(UnsatPath {
                    path: executor.path,
                    partial_trace: trace,
                    path_formula,
                }));
            }
            Err(e) => return Err(ReplayError::SymexError(e)),
        }
    }
}

/// Seed the symbolic state with concrete values from the counterexample.
fn seed_state_from_counterexample(state: &mut SymbolicState, cex: &Counterexample) {
    for (name, value) in &cex.assignments {
        let concrete = match value {
            CounterexampleValue::Bool(b) => SymbolicValue::Concrete(i128::from(*b)),
            CounterexampleValue::Int(n) => SymbolicValue::Concrete(*n),
            CounterexampleValue::Uint(n) => SymbolicValue::Concrete(*n as i128),
            CounterexampleValue::Float(_) => {
                // Floats: represent as a named symbol since we can't
                // losslessly represent them as i128.
                SymbolicValue::Symbol(format!("float_{name}"))
            }
            // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
            _ => continue,
        };
        state.set(name.clone(), concrete);
    }
}

/// When execution forks, find the branch that is feasible with concrete inputs.
///
/// Tries to evaluate each fork's latest path constraint concretely. If one
/// branch is clearly satisfiable, take it. Otherwise, prefer the first fork
/// (heuristic: match the solver's counterexample path).
fn find_feasible_fork<'a>(
    state: &SymbolicState,
    forks: &'a [trust_symex::ExecutionFork],
) -> Option<&'a trust_symex::ExecutionFork> {
    // Try to find a fork whose path constraints are all satisfiable
    // under concrete evaluation.
    for fork in forks {
        if is_path_feasible(state, &fork.path) {
            return Some(fork);
        }
    }
    // If we can't determine feasibility (some constraints are symbolic),
    // take the first fork as a heuristic.
    forks.first()
}

/// Check whether all path constraints evaluate to true under concrete state.
fn is_path_feasible(state: &SymbolicState, path: &PathConstraint) -> bool {
    for decision in path.decisions() {
        let val = trust_symex::state::eval(state, &decision.condition);
        match val {
            Some(v) => {
                let holds = v != 0;
                if holds != decision.taken {
                    return false;
                }
            }
            None => {
                // Can't evaluate: constraint involves unresolved symbols.
                // Conservatively assume feasible.
                return true;
            }
        }
    }
    true
}

/// After termination, decide whether the replay confirmed the bug.
fn confirm_or_spurious(
    counterexample: &Counterexample,
    final_state: SymbolicState,
    path: PathConstraint,
    trace: Vec<usize>,
) -> ReplayResult {
    // If the path is empty (no branches taken), the trace is trivially
    // confirmed. Otherwise, check that all path constraints hold.
    if path.is_empty() || all_constraints_concrete_true(&final_state, &path) {
        ReplayResult::RealBug(ConcreteCounterexample {
            counterexample: counterexample.clone(),
            final_state,
            trace,
        })
    } else {
        let path_formula = path.to_formula();
        ReplayResult::Spurious(UnsatPath { path, partial_trace: trace, path_formula })
    }
}

/// Check that all path constraints evaluate to true concretely.
fn all_constraints_concrete_true(state: &SymbolicState, path: &PathConstraint) -> bool {
    for decision in path.decisions() {
        match trust_symex::state::eval(state, &decision.condition) {
            Some(v) => {
                let holds = v != 0;
                if holds != decision.taken {
                    return false;
                }
            }
            None => return false,
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use trust_types::{
        BinOp, BlockId, ConstValue, Operand, Place, Rvalue, SourceSpan, Statement, Terminator,
        VcKind,
    };

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn simple_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: span(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        }
    }

    #[test]
    fn test_replay_real_bug_straight_line() {
        // A straight-line function: assign x = 42, then return.
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
                span: span(),
            }],
            terminator: Terminator::Return,
        }];

        let cex = Counterexample::new(vec![("_local0".into(), CounterexampleValue::Int(0))]);

        let result = replay_counterexample(&cex, &simple_vc(), &blocks, &ReplayConfig::default())
            .expect("replay should succeed");

        match result {
            ReplayResult::RealBug(concrete) => {
                assert_eq!(concrete.trace, vec![0]);
                assert_eq!(concrete.counterexample.assignments.len(), 1);
            }
            ReplayResult::Spurious(_) => panic!("expected RealBug for straight-line path"),
        }
    }

    #[test]
    fn test_replay_with_branch_concrete_inputs() {
        // Function with a branch: if _local0 == 1 then goto bb1 else bb2.
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
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ];

        // Counterexample says _local0 = 1, so we should take the true branch.
        let cex = Counterexample::new(vec![("_local0".into(), CounterexampleValue::Int(1))]);

        let result = replay_counterexample(&cex, &simple_vc(), &blocks, &ReplayConfig::default())
            .expect("replay should succeed");

        match result {
            ReplayResult::RealBug(concrete) => {
                // Should have visited block 0, then block 1.
                assert_eq!(concrete.trace, vec![0, 1]);
            }
            ReplayResult::Spurious(_) => panic!("expected RealBug with concrete branch"),
        }
    }

    #[test]
    fn test_replay_spurious_unreachable() {
        // Function where block 1 is unreachable.
        let blocks = vec![
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Unreachable },
        ];

        let cex = Counterexample::new(vec![]);

        let result = replay_counterexample(&cex, &simple_vc(), &blocks, &ReplayConfig::default())
            .expect("replay should succeed");

        match result {
            ReplayResult::Spurious(unsat) => {
                assert_eq!(unsat.partial_trace, vec![0, 1]);
            }
            ReplayResult::RealBug(_) => panic!("expected Spurious for unreachable path"),
        }
    }

    #[test]
    fn test_replay_error_no_blocks() {
        let cex = Counterexample::new(vec![]);
        let result = replay_counterexample(&cex, &simple_vc(), &[], &ReplayConfig::default());
        assert!(matches!(result, Err(ReplayError::NoBlocks)));
    }

    #[test]
    fn test_replay_error_entry_out_of_range() {
        let blocks =
            vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }];
        let cex = Counterexample::new(vec![]);
        let config = ReplayConfig { entry_block: 5, ..ReplayConfig::default() };
        let result = replay_counterexample(&cex, &simple_vc(), &blocks, &config);
        assert!(matches!(result, Err(ReplayError::BlockOutOfRange(5, 1))));
    }

    #[test]
    fn test_replay_depth_limit() {
        // Infinite loop: block 0 -> block 1 -> block 0.
        let blocks = vec![
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Goto(BlockId(0)) },
        ];
        let cex = Counterexample::new(vec![]);
        let config = ReplayConfig { depth_limit: 3, ..ReplayConfig::default() };
        let result = replay_counterexample(&cex, &simple_vc(), &blocks, &config);
        assert!(matches!(result, Err(ReplayError::DepthLimitExceeded(_))));
    }

    #[test]
    fn test_replay_seed_state_from_counterexample() {
        let cex = Counterexample::new(vec![
            ("x".into(), CounterexampleValue::Int(42)),
            ("y".into(), CounterexampleValue::Bool(true)),
            ("z".into(), CounterexampleValue::Uint(100)),
            ("f".into(), CounterexampleValue::Float(3.125)),
        ]);
        let mut state = SymbolicState::new();
        seed_state_from_counterexample(&mut state, &cex);

        assert_eq!(state.get("x").unwrap(), &SymbolicValue::Concrete(42));
        assert_eq!(state.get("y").unwrap(), &SymbolicValue::Concrete(1));
        assert_eq!(state.get("z").unwrap(), &SymbolicValue::Concrete(100));
        // Float becomes a symbol.
        assert!(matches!(state.get("f").unwrap(), SymbolicValue::Symbol(_)));
    }

    #[test]
    fn test_replay_with_computation() {
        // Block 0: _local2 = _local0 + _local1; goto bb1
        // Block 1: return
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(0)),
                        Operand::Copy(Place::local(1)),
                    ),
                    span: span(),
                }],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ];

        let cex = Counterexample::new(vec![
            ("_local0".into(), CounterexampleValue::Int(10)),
            ("_local1".into(), CounterexampleValue::Int(20)),
        ]);

        let result = replay_counterexample(&cex, &simple_vc(), &blocks, &ReplayConfig::default())
            .expect("replay should succeed");

        match result {
            ReplayResult::RealBug(concrete) => {
                assert_eq!(concrete.trace, vec![0, 1]);
                // The final state should have _local2 = BinOp(10, Add, 20).
                // With concrete inputs both sides resolve to Concrete values
                // wrapped in a BinOp node.
                let val = concrete.final_state.get("_local2").unwrap();
                let evaluated = trust_symex::state::eval(&concrete.final_state, val);
                assert_eq!(evaluated, Some(30));
            }
            ReplayResult::Spurious(_) => panic!("expected RealBug"),
        }
    }

    #[test]
    fn test_unsat_path_has_formula() {
        // Path that hits unreachable should produce a formula for CEGAR.
        let blocks =
            vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Unreachable }];
        let cex = Counterexample::new(vec![]);
        let result = replay_counterexample(&cex, &simple_vc(), &blocks, &ReplayConfig::default())
            .expect("replay should succeed");

        match result {
            ReplayResult::Spurious(unsat) => {
                // Empty path produces Bool(true) formula.
                assert!(matches!(unsat.path_formula, Formula::Bool(true)));
            }
            ReplayResult::RealBug(_) => panic!("expected Spurious"),
        }
    }
}
