// DFS-based loop detection for natural loops.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::*;

use crate::loop_analysis::LoopInfo;

/// Detect natural loops via DFS-based back-edge detection.
///
/// More precise than the block-ID heuristic in `loop_analysis::detect_loops`
/// because it correctly handles non-reducible control flow.
#[must_use]
pub(crate) fn detect_loops_dfs(func: &VerifiableFunction) -> Vec<LoopInfo> {
    let n = func.body.blocks.len();
    if n == 0 {
        return vec![];
    }

    let mut succs: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    for block in &func.body.blocks {
        let targets = block_successors_dfs(&block.terminator);
        succs.insert(block.id.0, targets);
    }

    let mut visited = vec![false; n];
    let mut on_stack = vec![false; n];
    let mut back_edges: Vec<(usize, usize)> = Vec::new();

    dfs_visit(
        func.body.blocks[0].id.0,
        &succs,
        &mut visited,
        &mut on_stack,
        &mut back_edges,
    );

    let mut loops = Vec::new();
    for (latch, header) in back_edges {
        let body = compute_natural_loop_body(header, latch, &succs, n);
        let body_set: FxHashSet<usize> = body.iter().copied().collect();

        let mut exit_blocks = Vec::new();
        for &bid in &body {
            if let Some(targets) = succs.get(&bid) {
                for &t in targets {
                    if !body_set.contains(&t) && !exit_blocks.contains(&BlockId(t)) {
                        exit_blocks.push(BlockId(t));
                    }
                }
            }
        }

        let body_blocks: Vec<BlockId> = body.into_iter().map(BlockId).collect();

        let mut loop_info = LoopInfo {
            header: BlockId(header),
            latch: BlockId(latch),
            body_blocks,
            exit_blocks,
            induction_vars: Vec::new(),
        };

        loop_info.induction_vars =
            crate::loop_analysis::find_induction_variables(&loop_info, func);

        loops.push(loop_info);
    }

    loops
}

/// Recursive DFS to find back-edges.
fn dfs_visit(
    node: usize,
    succs: &FxHashMap<usize, Vec<usize>>,
    visited: &mut [bool],
    on_stack: &mut [bool],
    back_edges: &mut Vec<(usize, usize)>,
) {
    if node >= visited.len() {
        return;
    }
    visited[node] = true;
    on_stack[node] = true;

    if let Some(targets) = succs.get(&node) {
        for &t in targets {
            if t >= visited.len() {
                continue;
            }
            if on_stack[t] {
                back_edges.push((node, t));
            } else if !visited[t] {
                dfs_visit(t, succs, visited, on_stack, back_edges);
            }
        }
    }

    on_stack[node] = false;
}

/// Compute the natural loop body via reverse reachability from latch to header.
fn compute_natural_loop_body(
    header: usize,
    latch: usize,
    succs: &FxHashMap<usize, Vec<usize>>,
    n: usize,
) -> Vec<usize> {
    let mut preds: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    for (&src, targets) in succs {
        for &dst in targets {
            preds.entry(dst).or_default().push(src);
        }
    }

    let mut body: FxHashSet<usize> = FxHashSet::default();
    body.insert(header);

    if header == latch {
        return body.into_iter().collect();
    }

    body.insert(latch);
    let mut worklist = vec![latch];

    while let Some(node) = worklist.pop() {
        if let Some(predecessors) = preds.get(&node) {
            for &pred in predecessors {
                if pred < n && !body.contains(&pred) {
                    body.insert(pred);
                    worklist.push(pred);
                }
            }
        }
    }

    let mut result: Vec<usize> = body.into_iter().collect();
    result.sort_unstable();
    result
}

/// Get all successor block IDs from a terminator.
fn block_successors_dfs(term: &Terminator) -> Vec<usize> {
    match term {
        Terminator::Goto(target) => vec![target.0],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs: Vec<usize> = targets.iter().map(|(_, t)| t.0).collect();
            succs.push(otherwise.0);
            succs
        }
        Terminator::Return | Terminator::Unreachable => vec![],
        Terminator::Call { target, .. } => target.iter().map(|t| t.0).collect(),
        Terminator::Assert { target, .. } => vec![target.0],
        Terminator::Drop { target, .. } => vec![target.0],
        _ => vec![],
    }
}
