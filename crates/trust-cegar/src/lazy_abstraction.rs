// trust-cegar: Lazy abstraction refinement with abstract reachability trees
//
// Implements the lazy abstraction paradigm from BLAST/CPAchecker: build an
// abstract reachability tree (ART) on-demand, refining predicates only along
// spurious counterexample paths. Unlike eager CEGAR which re-abstracts the
// entire program after refinement, lazy abstraction keeps already-explored
// subtrees intact and only re-explores from the refinement point.
//
// Reference: Henzinger et al., "Lazy Abstraction" (POPL 2002)
// CPAchecker: refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/
//
// Part of #311
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use trust_types::{BasicBlock, Counterexample, CounterexampleValue};

use crate::error::CegarError;
use crate::predicate::{AbstractState, CmpOp, Predicate, abstract_block};

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Expansion strategy for the abstract reachability tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
#[derive(Default)]
pub enum ExpansionStrategy {
    /// Depth-first exploration (default). Good for quickly finding deep bugs.
    #[default]
    DepthFirst,
    /// Breadth-first exploration. Good for finding shortest counterexamples.
    BreadthFirst,
    /// Expand the node with the fewest predicates first (coarsest abstraction).
    CoarsestFirst,
}


/// Configuration for lazy abstraction refinement.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct LazyAbstractionConfig {
    /// Maximum number of nodes in the ART before stopping.
    pub max_nodes: usize,
    /// Maximum number of refinement iterations.
    pub max_refinements: usize,
    /// Maximum tree depth before pruning.
    pub max_depth: usize,
    /// Expansion strategy for tree construction.
    pub strategy: ExpansionStrategy,
    /// Whether to reuse subtrees after refinement (true = lazy, false = eager).
    pub reuse_subtrees: bool,
}

impl Default for LazyAbstractionConfig {
    fn default() -> Self {
        Self {
            max_nodes: 10_000,
            max_refinements: 100,
            max_depth: 500,
            strategy: ExpansionStrategy::default(),
            reuse_subtrees: true,
        }
    }
}

// ---------------------------------------------------------------------------
// Tree node
// ---------------------------------------------------------------------------

/// Unique identifier for a node in the abstract reachability tree.
pub(crate) type NodeId = usize;

/// A node in the abstract reachability tree (ART).
///
/// Each node represents an abstract state at a specific program location (block).
/// Nodes store the predicates active at that point and links to parent/children.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TreeNode {
    /// Unique identifier within the ART.
    pub id: NodeId,
    /// Index of the basic block this node represents.
    pub block_idx: usize,
    /// Abstract state at this program point.
    pub state: AbstractState,
    /// Parent node (None for the root).
    pub parent: Option<NodeId>,
    /// Child node IDs.
    pub children: Vec<NodeId>,
    /// Predicates used for refinement at this node specifically.
    pub refinement_predicates: Vec<Predicate>,
    /// Depth in the tree (root = 0).
    pub depth: usize,
    /// Whether this node has been fully expanded.
    pub expanded: bool,
    /// Whether this node has been invalidated by refinement.
    pub invalidated: bool,
}

impl TreeNode {
    /// Create a new tree node.
    fn new(
        id: NodeId,
        block_idx: usize,
        state: AbstractState,
        parent: Option<NodeId>,
        depth: usize,
    ) -> Self {
        Self {
            id,
            block_idx,
            state,
            parent,
            children: Vec::new(),
            refinement_predicates: Vec::new(),
            depth,
            expanded: false,
            invalidated: false,
        }
    }
}

// ---------------------------------------------------------------------------
// Abstract reachability tree
// ---------------------------------------------------------------------------

/// Abstract reachability tree (ART) for lazy abstraction.
///
/// The ART is built incrementally: nodes are expanded on-demand, and
/// refinement only invalidates the subtree below the refinement point.
/// This avoids re-exploring parts of the state space that are unaffected
/// by new predicates.
#[derive(Debug, Clone)]
pub struct AbstractReachTree {
    /// All nodes in the tree, indexed by `NodeId`.
    nodes: Vec<TreeNode>,
    /// Worklist of node IDs to expand (frontier).
    worklist: Vec<NodeId>,
    /// Global predicates used across all nodes.
    pub(crate) global_predicates: Vec<Predicate>,
}

impl AbstractReachTree {
    /// Create a new ART rooted at the given block.
    #[must_use]
    pub fn new(root_block_idx: usize, initial_predicates: Vec<Predicate>) -> Self {
        let root_state = AbstractState::top();
        let root = TreeNode::new(0, root_block_idx, root_state, None, 0);
        Self {
            nodes: vec![root],
            worklist: vec![0],
            global_predicates: initial_predicates,
        }
    }

    /// Get a reference to a node by ID.
    #[must_use]
    pub fn node(&self, id: NodeId) -> Option<&TreeNode> {
        self.nodes.get(id)
    }

    /// Get a mutable reference to a node by ID.
    pub(crate) fn node_mut(&mut self, id: NodeId) -> Option<&mut TreeNode> {
        self.nodes.get_mut(id)
    }

    /// Number of nodes in the tree.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Number of nodes on the worklist (unexpanded frontier).
    #[must_use]
    pub fn worklist_len(&self) -> usize {
        self.worklist.len()
    }

    /// Whether the worklist is empty (all reachable states explored).
    #[must_use]
    pub fn is_fully_expanded(&self) -> bool {
        self.worklist.is_empty()
    }

    /// Add a child node to an existing parent.
    ///
    /// Returns the new node's ID.
    pub(crate) fn add_child(
        &mut self,
        parent_id: NodeId,
        block_idx: usize,
        state: AbstractState,
    ) -> NodeId {
        let depth = self.nodes.get(parent_id).map_or(0, |p| p.depth + 1);
        let new_id = self.nodes.len();
        let child = TreeNode::new(new_id, block_idx, state, Some(parent_id), depth);
        self.nodes.push(child);
        if let Some(parent) = self.nodes.get_mut(parent_id) {
            parent.children.push(new_id);
        }
        self.worklist.push(new_id);
        new_id
    }

    /// Extract the path from the root to a given node as a sequence of node IDs.
    #[must_use]
    pub fn path_to_root(&self, node_id: NodeId) -> Vec<NodeId> {
        let mut path = Vec::new();
        let mut current = Some(node_id);
        while let Some(id) = current {
            path.push(id);
            current = self.nodes.get(id).and_then(|n| n.parent);
        }
        path.reverse();
        path
    }

    /// Invalidate a subtree rooted at `node_id` (used after refinement).
    ///
    /// All descendants are marked invalidated and removed from the worklist.
    /// The node itself is re-added to the worklist for re-expansion.
    pub(crate) fn invalidate_subtree(&mut self, node_id: NodeId) {
        let mut stack = Vec::new();
        // Collect children to invalidate
        if let Some(node) = self.nodes.get(node_id) {
            stack.extend(node.children.iter().copied());
        }
        while let Some(id) = stack.pop() {
            if let Some(node) = self.nodes.get_mut(id) {
                node.invalidated = true;
                node.expanded = false;
                stack.extend(node.children.iter().copied());
            }
        }
        // Remove invalidated nodes from worklist
        self.worklist.retain(|id| {
            self.nodes.get(*id).is_some_and(|n| !n.invalidated)
        });
        // Clear the parent's children and re-add it to worklist
        if let Some(node) = self.nodes.get_mut(node_id) {
            node.children.clear();
            node.expanded = false;
        }
        if !self.worklist.contains(&node_id) {
            self.worklist.push(node_id);
        }
    }

    /// Pop the next node to expand from the worklist using the given strategy.
    pub(crate) fn pop_next(&mut self, strategy: ExpansionStrategy) -> Option<NodeId> {
        if self.worklist.is_empty() {
            return None;
        }
        match strategy {
            ExpansionStrategy::DepthFirst => self.worklist.pop(),
            ExpansionStrategy::BreadthFirst => Some(self.worklist.remove(0)),
            ExpansionStrategy::CoarsestFirst => {
                let (best_idx, _) = self
                    .worklist
                    .iter()
                    .enumerate()
                    .min_by_key(|(_, nid)| {
                        self.nodes.get(**nid).map_or(0, |n| n.state.len())
                    })?;
                Some(self.worklist.remove(best_idx))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Lazy abstraction refiner
// ---------------------------------------------------------------------------

/// Lazy abstraction refiner operating on an abstract reachability tree.
///
/// Combines tree-based exploration with on-demand refinement: when a
/// counterexample path is spurious, new predicates are added only at the
/// relevant program points, and only the affected subtree is re-explored.
#[derive(Debug)]
pub struct LazyAbstractionRefiner {
    /// The abstract reachability tree.
    tree: AbstractReachTree,
    /// Configuration.
    config: LazyAbstractionConfig,
    /// Number of refinements performed.
    refinement_count: usize,
    /// Total nodes expanded across all iterations.
    total_expansions: usize,
}

impl LazyAbstractionRefiner {
    /// Create a new lazy abstraction refiner.
    #[must_use]
    pub fn new(
        root_block_idx: usize,
        initial_predicates: Vec<Predicate>,
        config: LazyAbstractionConfig,
    ) -> Self {
        let tree = AbstractReachTree::new(root_block_idx, initial_predicates);
        Self {
            tree,
            config,
            refinement_count: 0,
            total_expansions: 0,
        }
    }

    /// Access the underlying ART.
    #[must_use]
    pub fn tree(&self) -> &AbstractReachTree {
        &self.tree
    }

    /// Number of refinements performed.
    #[must_use]
    pub fn refinement_count(&self) -> usize {
        self.refinement_count
    }

    /// Total node expansions performed.
    #[must_use]
    pub fn total_expansions(&self) -> usize {
        self.total_expansions
    }

    /// Expand a single node: compute successors using the current predicates.
    ///
    /// For each successor block of the node's block, computes the abstract
    /// state and adds a child node to the ART.
    ///
    /// # Arguments
    /// * `node_id` - The node to expand.
    /// * `blocks` - All basic blocks in the function.
    ///
    /// # Returns
    /// IDs of newly created child nodes.
    ///
    /// # Errors
    /// Returns `CegarError::InvalidBlockIndex` if the node's block index is invalid.
    pub fn expand_node(
        &mut self,
        node_id: NodeId,
        blocks: &[BasicBlock],
    ) -> Result<Vec<NodeId>, CegarError> {
        let (block_idx, depth) = {
            let node = self.tree.node(node_id).ok_or(CegarError::InvalidBlockIndex {
                index: node_id,
                num_blocks: self.tree.node_count(),
            })?;
            if node.expanded || node.invalidated {
                return Ok(Vec::new());
            }
            (node.block_idx, node.depth)
        };

        if block_idx >= blocks.len() {
            return Err(CegarError::InvalidBlockIndex {
                index: block_idx,
                num_blocks: blocks.len(),
            });
        }

        if depth >= self.config.max_depth {
            return Ok(Vec::new());
        }

        let block = &blocks[block_idx];

        // Compute successor block indices from the terminator.
        let successor_idxs = successor_blocks(block);

        // Clone predicates to avoid borrow conflict with tree mutation.
        let predicates_snapshot = self.tree.global_predicates.clone();

        let mut new_children = Vec::new();
        for succ_idx in successor_idxs {
            if succ_idx >= blocks.len() {
                continue;
            }
            // Compute abstract state at the successor using current predicates.
            let succ_state = abstract_block(&blocks[succ_idx], &predicates_snapshot);
            let child_id = self.tree.add_child(node_id, succ_idx, succ_state);
            new_children.push(child_id);
        }

        if let Some(node) = self.tree.node_mut(node_id) {
            node.expanded = true;
        }
        self.total_expansions += 1;

        Ok(new_children)
    }

    /// Refine predicates along a spurious counterexample path.
    ///
    /// Given a path of node IDs representing a spurious counterexample:
    /// 1. Walk the path, extracting interpolant predicates at each node.
    /// 2. Add new predicates to the global set and to the refinement point node.
    /// 3. Invalidate the subtree from the refinement point if `reuse_subtrees`.
    ///
    /// # Arguments
    /// * `path` - Node IDs along the counterexample path.
    /// * `blocks` - All basic blocks.
    /// * `cex` - The spurious counterexample.
    ///
    /// # Errors
    /// Returns `CegarError::RefinementStalled` if no new predicates are found.
    /// Returns `CegarError::MaxIterationsExceeded` if refinement limit reached.
    pub fn refine_path(
        &mut self,
        path: &[NodeId],
        blocks: &[BasicBlock],
        cex: &Counterexample,
    ) -> Result<Vec<Predicate>, CegarError> {
        if self.refinement_count >= self.config.max_refinements {
            return Err(CegarError::MaxIterationsExceeded {
                max: self.config.max_refinements,
            });
        }

        let mut new_predicates = Vec::new();
        let mut refinement_point: Option<NodeId> = None;

        let existing: BTreeSet<&Predicate> = self.tree.global_predicates.iter().collect();

        for &node_id in path {
            let block_idx = match self.tree.node(node_id) {
                Some(n) => n.block_idx,
                None => continue,
            };
            if block_idx >= blocks.len() {
                continue;
            }

            let state = abstract_block(&blocks[block_idx], &self.tree.global_predicates);
            let interpolants = extract_interpolants_from_cex(&state, cex);

            for pred in interpolants {
                if !existing.contains(&pred) && !new_predicates.contains(&pred) {
                    new_predicates.push(pred);
                    if refinement_point.is_none() {
                        refinement_point = Some(node_id);
                    }
                }
            }
        }

        if new_predicates.is_empty() {
            return Err(CegarError::RefinementStalled);
        }

        // Add new predicates globally.
        for pred in &new_predicates {
            if !self.tree.global_predicates.contains(pred) {
                self.tree.global_predicates.push(pred.clone());
            }
        }

        // Attach refinement predicates to the refinement point node.
        if let Some(rp) = refinement_point {
            if let Some(node) = self.tree.node_mut(rp) {
                node.refinement_predicates.extend(new_predicates.iter().cloned());
            }
            // Invalidate subtree if configured for lazy reuse.
            if self.config.reuse_subtrees {
                self.tree.invalidate_subtree(rp);
            }
        }

        self.refinement_count += 1;
        Ok(new_predicates)
    }

    /// Check if an abstract counterexample path is feasible (real).
    ///
    /// Walks the path, accumulating concrete constraints from the
    /// counterexample assignments, and checks for contradictions with
    /// the abstract states along the path.
    ///
    /// A path is considered infeasible (spurious) if any abstract state
    /// along the path contradicts the concrete assignments.
    ///
    /// # Arguments
    /// * `path` - Node IDs along the counterexample path.
    /// * `blocks` - All basic blocks.
    /// * `cex` - The counterexample to check.
    #[must_use]
    pub fn is_feasible(
        &self,
        path: &[NodeId],
        blocks: &[BasicBlock],
        cex: &Counterexample,
    ) -> bool {
        // A path is feasible if the concrete counterexample values are
        // consistent with the abstract states at every node on the path.
        for &node_id in path {
            let node = match self.tree.node(node_id) {
                Some(n) => n,
                None => return false,
            };
            if node.block_idx >= blocks.len() {
                return false;
            }

            let state = abstract_block(&blocks[node.block_idx], &self.tree.global_predicates);

            // Check each predicate in the abstract state against the cex.
            for pred in &state.predicates {
                if contradicts_counterexample(pred, cex) {
                    return false;
                }
            }
        }
        true
    }

    /// Run one step of the lazy abstraction loop: pick a node, expand it.
    ///
    /// Returns the expanded node ID and its children, or `None` if the
    /// worklist is empty.
    ///
    /// # Errors
    /// Returns `CegarError::InvalidBlockIndex` on block index issues.
    pub fn step(
        &mut self,
        blocks: &[BasicBlock],
    ) -> Result<Option<(NodeId, Vec<NodeId>)>, CegarError> {
        if self.tree.node_count() >= self.config.max_nodes {
            return Ok(None);
        }
        let node_id = match self.tree.pop_next(self.config.strategy) {
            Some(id) => id,
            None => return Ok(None),
        };
        let children = self.expand_node(node_id, blocks)?;
        Ok(Some((node_id, children)))
    }
}

// ---------------------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------------------

/// Extract successor block indices from a basic block's terminator.
fn successor_blocks(block: &BasicBlock) -> Vec<usize> {
    use trust_types::Terminator;
    match &block.terminator {
        Terminator::Goto(target) => vec![target.0],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs: Vec<usize> = targets.iter().map(|(_, bid)| bid.0).collect();
            succs.push(otherwise.0);
            succs
        }
        Terminator::Assert { target, .. } => vec![target.0],
        Terminator::Call { target, .. } => {
            target.iter().map(|t| t.0).collect()
        }
        Terminator::Drop { target, .. } => vec![target.0],
        Terminator::Return | Terminator::Unreachable => Vec::new(),
        _ => vec![],
    }
}

/// Extract interpolant predicates from the conflict between abstract state
/// and counterexample values (simplified Craig interpolation).
fn extract_interpolants_from_cex(
    state: &AbstractState,
    cex: &Counterexample,
) -> Vec<Predicate> {
    let mut interpolants = Vec::new();

    for (var_name, value) in &cex.assignments {
        match value {
            CounterexampleValue::Int(n) => {
                if *n < 0 {
                    let ge_zero = Predicate::comparison(var_name, CmpOp::Ge, "0");
                    if !state.contains(&ge_zero) {
                        interpolants.push(ge_zero);
                    }
                }
                let eq = Predicate::comparison(var_name, CmpOp::Eq, n.to_string());
                if !state.contains(&eq) {
                    interpolants.push(eq);
                }
            }
            CounterexampleValue::Uint(n) => {
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
            CounterexampleValue::Float(_) => {}
            _ => {},
        }
    }

    interpolants
}

/// Check if a predicate contradicts a concrete counterexample.
///
/// Returns true if the predicate's constraint is violated by the cex values.
fn contradicts_counterexample(pred: &Predicate, cex: &Counterexample) -> bool {
    match pred {
        Predicate::Comparison { lhs, op, rhs } => {
            let lhs_val = resolve_cex_value(lhs, cex);
            let rhs_val = resolve_cex_value(rhs, cex);
            match (lhs_val, rhs_val) {
                (Some(l), Some(r)) => !eval_cmp(*op, l, r),
                _ => false, // Unknown values: assume no contradiction.
            }
        }
        Predicate::Range { var, lo, hi } => {
            if let Some(v) = resolve_cex_value(var, cex) {
                v < *lo || v > *hi
            } else {
                false
            }
        }
        Predicate::NonNull(_) | Predicate::Custom(_) => false,
    }
}

/// Try to resolve a variable or constant string to an i128 value from the cex.
fn resolve_cex_value(name: &str, cex: &Counterexample) -> Option<i128> {
    // Try direct parse as integer constant.
    if let Ok(n) = name.parse::<i128>() {
        return Some(n);
    }
    // Look up in counterexample assignments.
    for (var, val) in &cex.assignments {
        if var == name {
            return match val {
                CounterexampleValue::Int(n) => Some(*n),
                CounterexampleValue::Uint(n) => i128::try_from(*n).ok(),
                CounterexampleValue::Bool(b) => Some(i128::from(*b)),
                CounterexampleValue::Float(_) => None,
                _ => None,
            };
        }
    }
    None
}

/// Evaluate a comparison operator on two i128 values.
fn eval_cmp(op: CmpOp, lhs: i128, rhs: i128) -> bool {
    match op {
        CmpOp::Lt => lhs < rhs,
        CmpOp::Le => lhs <= rhs,
        CmpOp::Gt => lhs > rhs,
        CmpOp::Ge => lhs >= rhs,
        CmpOp::Eq => lhs == rhs,
        CmpOp::Ne => lhs != rhs,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{
        BinOp, BlockId, ConstValue, Operand, Place, Rvalue, SourceSpan, Statement, Terminator,
    };

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    /// Build a simple 4-block CFG for testing:
    ///   bb0 (assign _1 = 0) -> bb1
    ///   bb1 (compare _1 < _3) -> bb2 or bb3
    ///   bb2 (return)
    ///   bb3 (return)
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
                        BinOp::Lt,
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
    fn test_art_new_has_root() {
        let art = AbstractReachTree::new(0, vec![]);
        assert_eq!(art.node_count(), 1);
        assert_eq!(art.worklist_len(), 1);
        let root = art.node(0).unwrap();
        assert_eq!(root.block_idx, 0);
        assert!(root.parent.is_none());
        assert_eq!(root.depth, 0);
    }

    #[test]
    fn test_art_add_child_and_path() {
        let mut art = AbstractReachTree::new(0, vec![]);
        let child1 = art.add_child(0, 1, AbstractState::top());
        let child2 = art.add_child(child1, 2, AbstractState::top());

        assert_eq!(art.node_count(), 3);
        assert_eq!(art.node(child2).unwrap().depth, 2);

        let path = art.path_to_root(child2);
        assert_eq!(path, vec![0, child1, child2]);
    }

    #[test]
    fn test_art_invalidate_subtree() {
        let mut art = AbstractReachTree::new(0, vec![]);
        let c1 = art.add_child(0, 1, AbstractState::top());
        let c2 = art.add_child(c1, 2, AbstractState::top());
        let _c3 = art.add_child(c2, 3, AbstractState::top());

        // Invalidate from c1 down.
        art.invalidate_subtree(c1);

        // c2, c3 should be invalidated.
        assert!(art.node(c2).unwrap().invalidated);
        // c1 should be back on the worklist.
        assert!(art.worklist.contains(&c1));
        assert!(!art.node(c1).unwrap().expanded);
    }

    #[test]
    fn test_expansion_strategy_depth_first() {
        let mut art = AbstractReachTree::new(0, vec![]);
        art.add_child(0, 1, AbstractState::top());
        art.add_child(0, 2, AbstractState::top());

        // DFS pops last added (node 2) first.
        let next = art.pop_next(ExpansionStrategy::DepthFirst).unwrap();
        assert_eq!(next, 2);
    }

    #[test]
    fn test_expansion_strategy_breadth_first() {
        let mut art = AbstractReachTree::new(0, vec![]);
        art.add_child(0, 1, AbstractState::top());
        art.add_child(0, 2, AbstractState::top());

        // BFS pops first added (root=0) first.
        let next = art.pop_next(ExpansionStrategy::BreadthFirst).unwrap();
        assert_eq!(next, 0);
    }

    #[test]
    fn test_refiner_expand_node_basic() {
        let blocks = simple_blocks();
        let config = LazyAbstractionConfig::default();
        let mut refiner = LazyAbstractionRefiner::new(0, vec![], config);

        // Expand root (bb0) -> should create child for bb1 (Goto target).
        let children = refiner.expand_node(0, &blocks).unwrap();
        assert_eq!(children.len(), 1);
        assert_eq!(refiner.tree().node(children[0]).unwrap().block_idx, 1);
        assert_eq!(refiner.total_expansions(), 1);
    }

    #[test]
    fn test_refiner_expand_switch_node() {
        let blocks = simple_blocks();
        let config = LazyAbstractionConfig::default();
        let mut refiner = LazyAbstractionRefiner::new(0, vec![], config);

        // Expand root, then expand the child (bb1 with SwitchInt -> bb2, bb3).
        let children_of_root = refiner.expand_node(0, &blocks).unwrap();
        let bb1_node = children_of_root[0];
        let children_of_bb1 = refiner.expand_node(bb1_node, &blocks).unwrap();

        // SwitchInt should produce children for bb2 and bb3.
        assert_eq!(children_of_bb1.len(), 2);
        let child_blocks: Vec<usize> = children_of_bb1
            .iter()
            .map(|&id| refiner.tree().node(id).unwrap().block_idx)
            .collect();
        assert!(child_blocks.contains(&2));
        assert!(child_blocks.contains(&3));
    }

    #[test]
    fn test_refiner_expand_invalid_block() {
        let blocks = simple_blocks();
        let config = LazyAbstractionConfig::default();
        let mut refiner = LazyAbstractionRefiner::new(99, vec![], config);

        let result = refiner.expand_node(0, &blocks);
        assert!(matches!(result, Err(CegarError::InvalidBlockIndex { .. })));
    }

    #[test]
    fn test_refiner_refine_path_adds_predicates() {
        let blocks = simple_blocks();
        let config = LazyAbstractionConfig::default();
        let mut refiner = LazyAbstractionRefiner::new(0, vec![], config);

        // Expand root and its child.
        let children = refiner.expand_node(0, &blocks).unwrap();
        let _grandchildren = refiner.expand_node(children[0], &blocks).unwrap();

        let cex = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(-5)),
            ("y".to_string(), CounterexampleValue::Uint(10)),
        ]);

        let path = vec![0, children[0]];
        let new_preds = refiner.refine_path(&path, &blocks, &cex).unwrap();

        assert!(!new_preds.is_empty());
        assert_eq!(refiner.refinement_count(), 1);
        assert!(!refiner.tree().global_predicates.is_empty());
    }

    #[test]
    fn test_refiner_refine_stalls_on_no_new_predicates() {
        let blocks = simple_blocks();
        let config = LazyAbstractionConfig::default();
        // Start with predicates that cover all possible interpolants for empty cex.
        let mut refiner = LazyAbstractionRefiner::new(0, vec![], config);

        let cex = Counterexample::new(vec![]);
        let path = vec![0];
        let result = refiner.refine_path(&path, &blocks, &cex);
        assert!(matches!(result, Err(CegarError::RefinementStalled)));
    }

    #[test]
    fn test_refiner_is_feasible_consistent_path() {
        let blocks = simple_blocks();
        let config = LazyAbstractionConfig::default();
        let refiner = LazyAbstractionRefiner::new(0, vec![], config);

        // Counterexample consistent with top (no predicates) is feasible.
        let cex = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(5)),
        ]);
        assert!(refiner.is_feasible(&[0], &blocks, &cex));
    }

    #[test]
    fn test_refiner_is_feasible_contradicting_predicate() {
        let blocks = simple_blocks();
        let config = LazyAbstractionConfig::default();
        // Add a predicate that x >= 0 holds.
        let preds = vec![Predicate::comparison("x", CmpOp::Ge, "0")];
        let refiner = LazyAbstractionRefiner::new(0, preds, config);

        // Counterexample with x = -1 contradicts x >= 0.
        let cex = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(-1)),
        ]);
        assert!(!refiner.is_feasible(&[0], &blocks, &cex));
    }

    #[test]
    fn test_refiner_step_expands_and_returns() {
        let blocks = simple_blocks();
        let config = LazyAbstractionConfig::default();
        let mut refiner = LazyAbstractionRefiner::new(0, vec![], config);

        let result = refiner.step(&blocks).unwrap();
        assert!(result.is_some());
        let (expanded_id, children) = result.unwrap();
        assert_eq!(expanded_id, 0);
        assert!(!children.is_empty());
    }

    #[test]
    fn test_refiner_max_refinements_exceeded() {
        let blocks = simple_blocks();
        let config = LazyAbstractionConfig {
            max_refinements: 1,
            ..LazyAbstractionConfig::default()
        };
        let mut refiner = LazyAbstractionRefiner::new(0, vec![], config);
        let _ = refiner.expand_node(0, &blocks).unwrap();

        let cex = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(-1)),
        ]);

        // First refinement should succeed.
        let r1 = refiner.refine_path(&[0], &blocks, &cex);
        assert!(r1.is_ok());

        // Second should fail with max exceeded.
        let r2 = refiner.refine_path(&[0], &blocks, &cex);
        assert!(matches!(r2, Err(CegarError::MaxIterationsExceeded { max: 1 })));
    }

    #[test]
    fn test_config_default_values() {
        let config = LazyAbstractionConfig::default();
        assert_eq!(config.max_nodes, 10_000);
        assert_eq!(config.max_refinements, 100);
        assert_eq!(config.max_depth, 500);
        assert_eq!(config.strategy, ExpansionStrategy::DepthFirst);
        assert!(config.reuse_subtrees);
    }

    #[test]
    fn test_contradicts_counterexample_range() {
        let pred = Predicate::range("x", 0, 100);
        let cex_in = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(50)),
        ]);
        let cex_out = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(200)),
        ]);
        assert!(!contradicts_counterexample(&pred, &cex_in));
        assert!(contradicts_counterexample(&pred, &cex_out));
    }

    #[test]
    fn test_eval_cmp_all_ops() {
        assert!(eval_cmp(CmpOp::Lt, 1, 2));
        assert!(!eval_cmp(CmpOp::Lt, 2, 1));
        assert!(eval_cmp(CmpOp::Le, 1, 1));
        assert!(eval_cmp(CmpOp::Gt, 3, 2));
        assert!(eval_cmp(CmpOp::Ge, 2, 2));
        assert!(eval_cmp(CmpOp::Eq, 5, 5));
        assert!(eval_cmp(CmpOp::Ne, 5, 6));
    }
}
