// trust-debug/cfg.rs: Control flow graph analysis for security
//
// Builds and analyzes control flow graphs for security-relevant properties:
// - Dominance analysis (which checks guard which operations)
// - Loop detection (potential infinite loops / DoS vectors)
// - Path enumeration from entry to dangerous operations
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::*;

/// A security-relevant path through the CFG.
#[derive(Debug, Clone)]
pub(crate) struct SecurityPath {
    /// Ordered sequence of block IDs from entry to sink.
    pub blocks: Vec<BlockId>,
    /// Guards along the path (conditions that must be true).
    pub guards: Vec<GuardCondition>,
    /// What dangerous operation this path reaches.
    pub sink: PathSink,
}

/// What a security path leads to.
#[derive(Debug, Clone)]
pub(crate) enum PathSink {
    /// An indirect call (potential code injection).
    IndirectCall { dest_local: usize },
    /// A call to a dangerous function.
    DangerousCall { func_name: String },
    /// A memory write with attacker-influenced destination.
    TaintedWrite { dest_local: usize },
    /// An assertion that may panic.
    PanicSite { message: String },
}

/// Find all paths from the entry block to blocks containing calls to
/// functions matching the given patterns.
pub(crate) fn paths_to_calls(body: &VerifiableBody, patterns: &[&str]) -> Vec<SecurityPath> {
    let mut paths = Vec::new();
    let path_map = body.path_map();

    for entry in &path_map {
        let block = &body.blocks[entry.block.0];
        if let Terminator::Call { func, .. } = &block.terminator {
            for pattern in patterns {
                if func.contains(pattern) {
                    paths.push(SecurityPath {
                        blocks: vec![entry.block],
                        guards: entry.guards.clone(),
                        sink: PathSink::DangerousCall { func_name: func.clone() },
                    });
                }
            }
        }
    }

    paths
}

/// Find blocks that are only reachable through specific guards.
/// Useful for detecting bypass paths around security checks.
pub(crate) fn guarded_blocks(body: &VerifiableBody) -> FxHashMap<usize, Vec<GuardCondition>> {
    let mut result = FxHashMap::default();
    for entry in body.path_map() {
        if !entry.guards.is_empty() {
            result.insert(entry.block.0, entry.guards);
        }
    }
    result
}

/// Detect back-edges (loops) in the CFG. Each back-edge is a potential
/// DoS vector if the loop bound is attacker-influenced.
pub(crate) fn detect_back_edges(body: &VerifiableBody) -> Vec<(BlockId, BlockId)> {
    let mut back_edges = Vec::new();
    let mut visited = FxHashSet::default();
    let mut in_stack = FxHashSet::default();

    fn dfs(
        block_id: usize,
        blocks: &[BasicBlock],
        visited: &mut FxHashSet<usize>,
        in_stack: &mut FxHashSet<usize>,
        back_edges: &mut Vec<(BlockId, BlockId)>,
    ) {
        if !visited.insert(block_id) {
            return;
        }
        in_stack.insert(block_id);

        if let Some(block) = blocks.get(block_id) {
            for successor in all_successors(&block.terminator) {
                if in_stack.contains(&successor.0) {
                    back_edges.push((BlockId(block_id), successor));
                } else if !visited.contains(&successor.0) {
                    dfs(successor.0, blocks, visited, in_stack, back_edges);
                }
            }
        }

        in_stack.remove(&block_id);
    }

    if !body.blocks.is_empty() {
        dfs(0, &body.blocks, &mut visited, &mut in_stack, &mut back_edges);
    }

    back_edges
}

fn all_successors(terminator: &Terminator) -> Vec<BlockId> {
    match terminator {
        Terminator::Goto(target) => vec![*target],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs: Vec<_> = targets.iter().map(|(_, t)| *t).collect();
            succs.push(*otherwise);
            succs
        }
        Terminator::Return | Terminator::Unreachable => vec![],
        Terminator::Call { target, .. } => target.iter().copied().collect(),
        Terminator::Assert { target, .. } => vec![*target],
        Terminator::Drop { target, .. } => vec![*target],
        _ => vec![],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_body(blocks: Vec<BasicBlock>) -> VerifiableBody {
        VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks,
            arg_count: 0,
            return_ty: Ty::Unit,
        }
    }

    #[test]
    fn test_paths_to_dangerous_calls() {
        let body = make_body(vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: "std::process::Command::new".into(),
                    args: vec![],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ]);

        let paths = paths_to_calls(&body, &["Command::new"]);
        assert_eq!(paths.len(), 1);
        assert!(matches!(paths[0].sink, PathSink::DangerousCall { .. }));
    }

    #[test]
    fn test_detect_loops() {
        // bb0 -> bb1 -> bb2 -> bb1 (back edge)
        let body = make_body(vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(2)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(1)),
            },
        ]);

        let back_edges = detect_back_edges(&body);
        assert_eq!(back_edges.len(), 1);
        assert_eq!(back_edges[0], (BlockId(2), BlockId(1)));
    }

    #[test]
    fn test_guarded_blocks() {
        let body = make_body(vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(0)),
                    targets: vec![(1, BlockId(1))],
                    otherwise: BlockId(2),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ]);

        let guards = guarded_blocks(&body);
        assert!(guards.contains_key(&1));
        assert!(guards.contains_key(&2));
        assert!(!guards.contains_key(&0));
    }

    #[test]
    fn test_no_loops_in_linear_cfg() {
        let body = make_body(vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ]);

        let back_edges = detect_back_edges(&body);
        assert!(back_edges.is_empty());
    }
}
