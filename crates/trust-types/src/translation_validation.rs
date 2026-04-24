// trust-types: Translation validation shared types
//
// Core types for translation validation — proving that compiled code
// (post-optimization MIR or machine code) refines pre-optimization MIR semantics.
//
// These types live in trust-types so both trust-vcgen and trust-transval
// (the authoritative translation validation crate) can use them without
// circular dependencies. See tRust #458.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::FxHashMap;

use crate::{
    BlockId, Formula, Sort, SourceSpan, Ty, VcKind, VerifiableBody, VerifiableFunction,
    VerificationCondition,
};

/// Error type for translation validation operations.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum TranslationValidationError {
    /// Source and target functions have incompatible signatures.
    #[error("signature mismatch: source has {source_args} args, target has {target_args}")]
    SignatureMismatch { source_args: usize, target_args: usize },

    /// A source block has no corresponding target block in the simulation relation.
    #[error("unmapped source block {0:?} has no target correspondence")]
    UnmappedBlock(BlockId),

    /// The simulation relation is invalid (e.g., maps to nonexistent blocks).
    #[error("invalid simulation relation: {0}")]
    InvalidRelation(String),

    /// Source or target function body is empty.
    #[error("empty function body: {0}")]
    EmptyBody(String),

    /// Target block does not exist (tRust #163: typed variant replaces InvalidRelation format string).
    #[error("target block {block:?} does not exist in target function")]
    InvalidTargetBlock { block: BlockId },

    /// Target local index out of range (tRust #163: typed variant replaces InvalidRelation format string).
    #[error("target local index {index} out of range (target has {num_locals} locals)")]
    InvalidTargetLocal { index: usize, num_locals: usize },
}

/// A single translation validation check between a source and target program point.
///
/// Each check asserts that the target behavior at `target_point` refines the
/// source behavior at `source_point` under the simulation relation's variable mapping.
#[derive(Debug, Clone)]
pub struct TranslationCheck {
    /// Source (MIR) program point.
    pub source_point: BlockId,
    /// Target (optimized/compiled) program point.
    pub target_point: BlockId,
    /// What this check validates.
    pub kind: CheckKind,
    /// The formula asserting refinement at this point.
    pub formula: Formula,
    /// Human-readable description.
    pub description: String,
}

/// What aspect of translation a check validates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckKind {
    /// Control flow: target preserves source CFG reachability.
    ControlFlow,
    /// Data flow: target assignments refine source assignments.
    DataFlow,
    /// Termination: target terminates if source terminates.
    Termination,
    /// Return value: target return matches source return.
    ReturnValue,
}

/// A simulation relation mapping source program points and variables to target ones.
///
/// This is the "glue" between source (pre-optimization MIR) and target
/// (post-optimization MIR or machine code). A valid simulation relation must:
///   1. Map every reachable source block to at least one target block.
///   2. Map source locals to target locals (or expressions over target locals).
///   3. Preserve the entry and return points.
#[derive(Debug, Clone)]
pub struct SimulationRelation {
    /// Maps source block IDs to target block IDs.
    pub block_map: FxHashMap<BlockId, BlockId>,
    /// Maps source local variable indices to target local variable indices.
    pub variable_map: FxHashMap<usize, usize>,
    /// Optional: maps source locals to target formula expressions (for
    /// optimizations that restructure variables, e.g., constant folding).
    pub expression_map: FxHashMap<usize, Formula>,
}

impl SimulationRelation {
    /// Create a new empty simulation relation.
    #[must_use]
    pub fn new() -> Self {
        Self {
            block_map: FxHashMap::default(),
            variable_map: FxHashMap::default(),
            expression_map: FxHashMap::default(),
        }
    }

    /// Create an identity simulation relation for a function.
    ///
    /// Maps each block and variable to itself. Used as a starting point
    /// or for validating trivial transformations.
    #[must_use]
    pub fn identity(func: &VerifiableFunction) -> Self {
        let block_map: FxHashMap<BlockId, BlockId> =
            func.body.blocks.iter().map(|bb| (bb.id, bb.id)).collect();

        let variable_map: FxHashMap<usize, usize> =
            func.body.locals.iter().map(|local| (local.index, local.index)).collect();

        Self { block_map, variable_map, expression_map: FxHashMap::default() }
    }

    /// Validate that the simulation relation is well-formed with respect to
    /// source and target functions.
    pub fn validate(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> Result<(), TranslationValidationError> {
        // Check that all source blocks have a mapping.
        for block in &source.body.blocks {
            if !self.block_map.contains_key(&block.id) {
                return Err(TranslationValidationError::UnmappedBlock(block.id));
            }
        }

        // Check that all mapped target blocks actually exist.
        let target_block_ids: Vec<BlockId> = target.body.blocks.iter().map(|bb| bb.id).collect();
        for target_id in self.block_map.values() {
            if !target_block_ids.contains(target_id) {
                return Err(TranslationValidationError::InvalidTargetBlock { block: *target_id });
            }
        }

        // Check that mapped variables exist in the target.
        for target_idx in self.variable_map.values() {
            if *target_idx >= target.body.locals.len() {
                return Err(TranslationValidationError::InvalidTargetLocal {
                    index: *target_idx,
                    num_locals: target.body.locals.len(),
                });
            }
        }

        Ok(())
    }

    /// Look up the target expression for a source local.
    ///
    /// Prefers `expression_map` (for optimized representations), falls back
    /// to `variable_map` (direct local-to-local mapping).
    #[must_use]
    pub fn resolve_variable(
        &self,
        source_local: usize,
        target: &VerifiableFunction,
    ) -> Option<Formula> {
        // Check expression map first (handles constant folding, etc.)
        if let Some(expr) = self.expression_map.get(&source_local) {
            return Some(expr.clone());
        }

        // Fall back to direct variable mapping.
        if let Some(&target_local) = self.variable_map.get(&source_local) {
            let decl = target.body.locals.get(target_local)?;
            let fallback = format!("_{}", target_local);
            let name = decl.name.as_deref().unwrap_or(&fallback);
            let sort = match &decl.ty {
                Ty::Bool => Sort::Bool,
                Ty::Int { .. } => Sort::Int,
                other => Sort::from_ty(other),
            };
            return Some(Formula::Var(name.to_string(), sort));
        }

        None
    }
}

impl Default for SimulationRelation {
    fn default() -> Self {
        Self::new()
    }
}

/// A refinement verification condition: asserts that the target program
/// refines the source program at a particular point.
#[derive(Debug, Clone)]
pub struct RefinementVc {
    /// The translation check that generated this VC.
    pub check: TranslationCheck,
    /// The source function name.
    pub source_function: String,
    /// The target function name.
    pub target_function: String,
}

impl RefinementVc {
    /// Convert to a standard `VerificationCondition` for solver dispatch.
    #[must_use]
    pub fn to_vc(&self) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::RefinementViolation {
                spec_file: self.source_function.clone(),
                action: format!(
                    "{:?} check at source {:?} -> target {:?}",
                    self.check.kind, self.check.source_point, self.check.target_point
                ),
            },
            function: crate::Symbol::intern(&self.target_function),
            location: SourceSpan::default(),
            formula: self.check.formula.clone(),
            contract_metadata: None,
        }
    }
}

/// Infer an identity simulation relation between two functions with the same structure.
///
/// This is a convenience for when source and target have the same block count
/// and local count — common for minor optimizations like constant folding
/// within blocks.
#[must_use]
pub fn infer_identity_relation(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
) -> Option<SimulationRelation> {
    if source.body.blocks.len() != target.body.blocks.len() {
        return None;
    }

    let block_map: FxHashMap<BlockId, BlockId> = source
        .body
        .blocks
        .iter()
        .zip(target.body.blocks.iter())
        .map(|(s, t)| (s.id, t.id))
        .collect();

    let local_count = source.body.locals.len().min(target.body.locals.len());
    let variable_map: FxHashMap<usize, usize> = (0..local_count).map(|i| (i, i)).collect();

    Some(SimulationRelation { block_map, variable_map, expression_map: FxHashMap::default() })
}

/// Detect back-edges in the CFG (header, latch) pairs.
pub fn detect_back_edges(body: &VerifiableBody) -> Vec<(BlockId, BlockId)> {
    let mut edges = Vec::new();
    for block in &body.blocks {
        for succ in block_successors_list(&block.terminator) {
            if succ.0 <= block.id.0 && block.id.0 > 0 {
                edges.push((succ, block.id));
            }
        }
    }
    edges
}

/// Get all successor block IDs from a terminator.
pub fn block_successors_list(term: &crate::Terminator) -> Vec<BlockId> {
    #[allow(unreachable_patterns)] // wildcard kept for #[non_exhaustive] forward compat
    match term {
        crate::Terminator::Goto(target) => vec![*target],
        crate::Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs: Vec<BlockId> = targets.iter().map(|(_, b)| *b).collect();
            succs.push(*otherwise);
            succs
        }
        crate::Terminator::Return | crate::Terminator::Unreachable => vec![],
        crate::Terminator::Call { target, .. } => target.iter().copied().collect(),
        crate::Terminator::Assert { target, .. } => vec![*target],
        crate::Terminator::Drop { target, .. } => vec![*target],
        _ => vec![],
    }
}
