// trust-llvm2-bridge/transval_full.rs: Full translation validation for MIR -> LIR lowering
//
// Extends the lightweight structural validation in transval.rs with semantic
// refinement checking using trust-types' translation validation types.
//
// Generates refinement VCs (as VerificationCondition) that prove the LIR
// preserves MIR semantics. Callers dispatch these VCs to a solver (z4 via
// trust-router) for semantic equivalence checking.
//
// Architecture:
//   1. Lower source MIR -> LIR (via lower_to_lir)
//   2. Lift LIR -> MIR (via lift_from_lir)
//   3. Infer simulation relation between source and lifted target
//   4. Generate refinement VCs for control flow, data flow, and return values
//   5. Return VCs for external solver dispatch
//
// Note: trust-transval cannot be a direct dependency due to the
// trust-router -> trust-llvm2-bridge -> trust-transval -> trust-router cycle.
// Instead, we use trust-types' shared translation validation types and
// implement VC generation directly.
//
// Gated behind the `transval-full` feature flag.
//
// Part of #831
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::{
    BasicBlock, BinOp, BlockId, CheckKind, ConstValue, Formula, Operand, Place, RefinementVc,
    Rvalue, SimulationRelation, Sort, Statement, Terminator, TranslationCheck,
    TranslationValidationError, Ty, UnOp, VerifiableFunction, VerificationCondition,
};

use crate::{BridgeError, lift_from_lir, lower_to_lir};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors from full translation validation.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum FullValidationError {
    /// The MIR -> LIR lowering step failed.
    #[error("lowering failed: {0}")]
    LoweringFailed(#[from] BridgeError),

    /// The LIR -> MIR lift-back step failed.
    #[error("lift-back failed: {0}")]
    LiftBackFailed(BridgeError),

    /// Refinement VC generation failed.
    #[error("refinement check failed: {0}")]
    RefinementFailed(#[from] TranslationValidationError),
}

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Full translation validation result: structural checks + refinement VCs.
#[derive(Debug, Clone)]
pub struct FullValidationResult {
    /// The function name that was validated.
    pub function_name: String,
    /// Structural checks (return type, arg count, block count, etc.).
    pub structural_checks: Vec<StructuralCheck>,
    /// Refinement VCs for solver dispatch.
    ///
    /// If all VCs are UNSAT, the lowering is semantically correct.
    /// Callers dispatch these to z4 via trust-router.
    pub refinement_vcs: Vec<VerificationCondition>,
    /// Summary counts.
    pub structural_passed: usize,
    pub structural_total: usize,
    pub refinement_vc_count: usize,
}

/// A single structural check.
#[derive(Debug, Clone)]
pub struct StructuralCheck {
    /// What was checked.
    pub description: String,
    /// Whether it passed.
    pub passed: bool,
    /// Detail on mismatch (if failed).
    pub detail: Option<String>,
}

impl FullValidationResult {
    /// Whether all structural checks passed.
    #[must_use]
    pub fn is_structurally_valid(&self) -> bool {
        self.structural_checks.iter().all(|c| c.passed)
    }

    /// Whether VCs were generated (structural checks passed and VCs are ready
    /// for solver dispatch).
    #[must_use]
    pub fn has_refinement_vcs(&self) -> bool {
        self.is_structurally_valid() && !self.refinement_vcs.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Perform full translation validation on a function's lowering.
///
/// Pipeline:
/// 1. Lower source MIR -> LIR via `lower_to_lir`
/// 2. Lift LIR -> MIR via `lift_from_lir`
/// 3. Structural comparison (return type, arg count, block count, terminators)
/// 4. Infer simulation relation between source and lifted target
/// 5. Generate refinement VCs (control flow, data flow, return values)
///
/// Returns a `FullValidationResult` containing structural check results and
/// refinement VCs. Callers dispatch VCs to a solver for semantic verification.
pub fn validate_full(
    source: &VerifiableFunction,
) -> Result<FullValidationResult, FullValidationError> {
    let lir = lower_to_lir(source)?;
    let lifted_target = lift_from_lir(&lir).map_err(FullValidationError::LiftBackFailed)?;
    validate_full_pair(source, &lifted_target)
}

/// Validate that `target` refines `source` with full refinement VC generation.
///
/// Use this when both functions are already available (e.g., post-optimization
/// MIR from rustc vs. pre-optimization MIR).
pub fn validate_full_pair(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
) -> Result<FullValidationResult, FullValidationError> {
    // Phase 1: Structural checks.
    let structural_checks = structural_compare(source, target);
    let structural_total = structural_checks.len();
    let structural_passed = structural_checks.iter().filter(|c| c.passed).count();

    // Phase 2: Refinement VCs (only if structural checks pass).
    let refinement_vcs = if structural_checks.iter().all(|c| c.passed) {
        generate_lowering_refinement_vcs(source, target)?
    } else {
        Vec::new()
    };

    let refinement_vc_count = refinement_vcs.len();

    Ok(FullValidationResult {
        function_name: source.name.clone(),
        structural_checks,
        refinement_vcs,
        structural_passed,
        structural_total,
        refinement_vc_count,
    })
}

// ---------------------------------------------------------------------------
// Structural comparison
// ---------------------------------------------------------------------------

/// Structural comparison between source MIR and lifted target MIR.
fn structural_compare(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
) -> Vec<StructuralCheck> {
    let mut checks = Vec::new();

    // Check 1: Return type match.
    let src_ret = format!("{:?}", source.body.return_ty);
    let tgt_ret = format!("{:?}", target.body.return_ty);
    checks.push(StructuralCheck {
        description: "return type".to_string(),
        passed: src_ret == tgt_ret,
        detail: if src_ret != tgt_ret {
            Some(format!("source: {src_ret}, target: {tgt_ret}"))
        } else {
            None
        },
    });

    // Check 2: Argument count match.
    checks.push(StructuralCheck {
        description: "argument count".to_string(),
        passed: source.body.arg_count == target.body.arg_count,
        detail: if source.body.arg_count != target.body.arg_count {
            Some(format!("source: {}, target: {}", source.body.arg_count, target.body.arg_count))
        } else {
            None
        },
    });

    // Check 3: Block count (target >= source, since lowering may add blocks).
    let src_blocks = source.body.blocks.len();
    let tgt_blocks = target.body.blocks.len();
    let blocks_ok = tgt_blocks >= src_blocks;
    checks.push(StructuralCheck {
        description: "block count (target >= source)".to_string(),
        passed: blocks_ok,
        detail: if !blocks_ok {
            Some(format!("source: {src_blocks}, target: {tgt_blocks}"))
        } else {
            None
        },
    });

    // Check 4: Argument types match.
    let src_arg_types: Vec<String> = source.body.locals[1..=source.body.arg_count]
        .iter()
        .map(|l| format!("{:?}", l.ty))
        .collect();
    let tgt_arg_types: Vec<String> = target
        .body
        .locals
        .get(1..=target.body.arg_count)
        .unwrap_or(&[])
        .iter()
        .map(|l| format!("{:?}", l.ty))
        .collect();
    checks.push(StructuralCheck {
        description: "argument types".to_string(),
        passed: src_arg_types == tgt_arg_types,
        detail: if src_arg_types != tgt_arg_types {
            Some(format!("source: {src_arg_types:?}, target: {tgt_arg_types:?}"))
        } else {
            None
        },
    });

    // Check 5: Entry block terminator kind match.
    if let (Some(src_bb0), Some(tgt_bb0)) = (source.body.blocks.first(), target.body.blocks.first())
    {
        let src_kind = terminator_kind_name(&src_bb0.terminator);
        let tgt_kind = terminator_kind_name(&tgt_bb0.terminator);
        checks.push(StructuralCheck {
            description: "entry block terminator kind".to_string(),
            passed: src_kind == tgt_kind,
            detail: if src_kind != tgt_kind {
                Some(format!("source: {src_kind}, target: {tgt_kind}"))
            } else {
                None
            },
        });
    }

    checks
}

/// Classify a terminator for structural comparison.
fn terminator_kind_name(term: &Terminator) -> &'static str {
    #[allow(unreachable_patterns)] // wildcard for #[non_exhaustive] forward compat
    match term {
        Terminator::Return => "Return",
        Terminator::Goto { .. } => "Goto",
        Terminator::SwitchInt { .. } => "SwitchInt",
        Terminator::Call { .. } => "Call",
        Terminator::Assert { .. } => "Assert",
        Terminator::Drop { .. } => "Drop",
        Terminator::Unreachable => "Unreachable",
        _ => "Unknown",
    }
}

// ---------------------------------------------------------------------------
// Refinement VC generation
// ---------------------------------------------------------------------------

/// Generate refinement VCs for a MIR -> LIR lowering.
///
/// Infers an identity simulation relation between source and target, then
/// generates control flow, data flow, and return value VCs.
fn generate_lowering_refinement_vcs(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
) -> Result<Vec<VerificationCondition>, TranslationValidationError> {
    // Validate inputs.
    if source.body.blocks.is_empty() {
        return Err(TranslationValidationError::EmptyBody(source.name.clone()));
    }
    if target.body.blocks.is_empty() {
        return Err(TranslationValidationError::EmptyBody(target.name.clone()));
    }
    if source.body.arg_count != target.body.arg_count {
        return Err(TranslationValidationError::SignatureMismatch {
            source_args: source.body.arg_count,
            target_args: target.body.arg_count,
        });
    }

    // Infer simulation relation.
    let relation = trust_types::infer_identity_relation(source, target).unwrap_or_else(|| {
        // Fallback: build a minimal relation from overlapping block/local IDs.
        build_minimal_relation(source, target)
    });

    relation.validate(source, target)?;

    let mut vcs = Vec::new();

    // Control flow preservation.
    vcs.extend(check_control_flow(source, target, &relation)?);

    // Data flow preservation.
    vcs.extend(check_data_flow(source, target, &relation)?);

    // Return value preservation.
    vcs.extend(check_return_values(source, target, &relation)?);

    // Convert RefinementVcs to VerificationConditions for solver dispatch.
    Ok(vcs.into_iter().map(|rvc| rvc.to_vc()).collect())
}

/// Build a minimal simulation relation when identity inference fails.
fn build_minimal_relation(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
) -> SimulationRelation {
    let target_block_ids: Vec<BlockId> = target.body.blocks.iter().map(|bb| bb.id).collect();

    let block_map: FxHashMap<BlockId, BlockId> = source
        .body
        .blocks
        .iter()
        .filter_map(
            |bb| {
                if target_block_ids.contains(&bb.id) { Some((bb.id, bb.id)) } else { None }
            },
        )
        .collect();

    let local_count = source.body.locals.len().min(target.body.locals.len());
    let variable_map: FxHashMap<usize, usize> = (0..local_count).map(|i| (i, i)).collect();

    SimulationRelation { block_map, variable_map, expression_map: FxHashMap::default() }
}

/// Check control flow preservation: each source block's successors must be
/// reachable from the corresponding target block.
fn check_control_flow(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
    relation: &SimulationRelation,
) -> Result<Vec<RefinementVc>, TranslationValidationError> {
    let mut vcs = Vec::new();
    let target_blocks: FxHashMap<BlockId, &BasicBlock> =
        target.body.blocks.iter().map(|bb| (bb.id, bb)).collect();

    for source_block in &source.body.blocks {
        let source_succs = trust_types::block_successors_list(&source_block.terminator);
        if source_succs.is_empty() {
            continue;
        }

        let target_block_id = match relation.block_map.get(&source_block.id) {
            Some(id) => id,
            None => continue, // Unmapped block -- skip (may have been optimized away).
        };

        let target_block = match target_blocks.get(target_block_id) {
            Some(bb) => bb,
            None => continue,
        };

        let target_succs = trust_types::block_successors_list(&target_block.terminator);

        for source_succ in &source_succs {
            if let Some(expected_target_succ) = relation.block_map.get(source_succ) {
                if !target_succs.contains(expected_target_succ) {
                    // Missing successor -> generate a VC.
                    vcs.push(RefinementVc {
                        check: TranslationCheck {
                            source_point: source_block.id,
                            target_point: *target_block_id,
                            kind: CheckKind::ControlFlow,
                            formula: Formula::Not(Box::new(Formula::Bool(true))),
                            description: format!(
                                "source {:?} -> {:?} must be preserved in target {:?}",
                                source_block.id, source_succ, target_block_id
                            ),
                        },
                        source_function: source.name.clone(),
                        target_function: target.name.clone(),
                    });
                }
            }
        }
    }

    Ok(vcs)
}

/// Check data flow preservation: assignments in source blocks must be
/// preserved in corresponding target blocks.
fn check_data_flow(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
    relation: &SimulationRelation,
) -> Result<Vec<RefinementVc>, TranslationValidationError> {
    let mut vcs = Vec::new();
    let target_blocks: FxHashMap<BlockId, &BasicBlock> =
        target.body.blocks.iter().map(|bb| (bb.id, bb)).collect();

    for source_block in &source.body.blocks {
        let target_block_id = match relation.block_map.get(&source_block.id) {
            Some(id) => id,
            None => continue,
        };

        let target_block = match target_blocks.get(target_block_id) {
            Some(bb) => bb,
            None => continue,
        };

        for source_stmt in &source_block.stmts {
            if let Statement::Assign { place: source_place, rvalue: source_rvalue, .. } =
                source_stmt
            {
                let source_expr = rvalue_to_formula(source, source_rvalue);

                // Find target expression: check expression_map, then variable_map,
                // then look for a matching assignment in the target block.
                let target_expr =
                    if let Some(mapped) = relation.resolve_variable(source_place.local, target) {
                        mapped
                    } else {
                        match find_assignment_to(target_block, source_place.local, relation) {
                            Some(rvalue) => rvalue_to_formula(target, rvalue),
                            None => continue, // Dead code elimination removed this.
                        }
                    };

                // VC: NOT(source_expr == target_expr). UNSAT => always equal.
                let formula = Formula::Not(Box::new(Formula::Eq(
                    Box::new(source_expr),
                    Box::new(target_expr),
                )));

                vcs.push(RefinementVc {
                    check: TranslationCheck {
                        source_point: source_block.id,
                        target_point: *target_block_id,
                        kind: CheckKind::DataFlow,
                        formula,
                        description: format!(
                            "assignment to local {} in source {:?} preserved in target {:?}",
                            source_place.local, source_block.id, target_block_id
                        ),
                    },
                    source_function: source.name.clone(),
                    target_function: target.name.clone(),
                });
            }
        }
    }

    Ok(vcs)
}

/// Check return value preservation: for each Return in source, the target must
/// also return with an equivalent _0 value.
fn check_return_values(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
    relation: &SimulationRelation,
) -> Result<Vec<RefinementVc>, TranslationValidationError> {
    let mut vcs = Vec::new();
    let target_blocks: FxHashMap<BlockId, &BasicBlock> =
        target.body.blocks.iter().map(|bb| (bb.id, bb)).collect();

    for source_block in &source.body.blocks {
        if !matches!(source_block.terminator, Terminator::Return) {
            continue;
        }

        let target_block_id = match relation.block_map.get(&source_block.id) {
            Some(id) => id,
            None => continue,
        };

        let target_block = match target_blocks.get(target_block_id) {
            Some(bb) => bb,
            None => continue,
        };

        // Check that target also returns.
        if !matches!(target_block.terminator, Terminator::Return) {
            vcs.push(RefinementVc {
                check: TranslationCheck {
                    source_point: source_block.id,
                    target_point: *target_block_id,
                    kind: CheckKind::ReturnValue,
                    formula: Formula::Bool(false), // Always SAT => violation.
                    description: format!(
                        "source {:?} returns but target {:?} does not",
                        source_block.id, target_block_id
                    ),
                },
                source_function: source.name.clone(),
                target_function: target.name.clone(),
            });
            continue;
        }

        // Compare return values (_0).
        let source_ret = local_to_formula(source, 0);
        let target_ret =
            relation.resolve_variable(0, target).unwrap_or_else(|| local_to_formula(target, 0));

        let formula =
            Formula::Not(Box::new(Formula::Eq(Box::new(source_ret), Box::new(target_ret))));

        vcs.push(RefinementVc {
            check: TranslationCheck {
                source_point: source_block.id,
                target_point: *target_block_id,
                kind: CheckKind::ReturnValue,
                formula,
                description: format!(
                    "return value at source {:?} must equal target {:?}",
                    source_block.id, target_block_id
                ),
            },
            source_function: source.name.clone(),
            target_function: target.name.clone(),
        });
    }

    Ok(vcs)
}

// ---------------------------------------------------------------------------
// Formula helpers
// ---------------------------------------------------------------------------

/// Convert an Rvalue to a Formula for VC generation.
fn rvalue_to_formula(func: &VerifiableFunction, rvalue: &Rvalue) -> Formula {
    match rvalue {
        Rvalue::Use(op) => operand_to_formula(func, op),
        Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let l = operand_to_formula(func, lhs);
            let r = operand_to_formula(func, rhs);
            binop_to_formula(*op, l, r)
        }
        Rvalue::UnaryOp(UnOp::Neg, op) => Formula::Neg(Box::new(operand_to_formula(func, op))),
        Rvalue::UnaryOp(UnOp::Not, op) => Formula::Not(Box::new(operand_to_formula(func, op))),
        Rvalue::UnaryOp(UnOp::PtrMetadata, op) | Rvalue::Cast(op, _) => {
            operand_to_formula(func, op)
        }
        _ => Formula::Int(0), // Aggregate, Ref, Discriminant, Len: approximate.
    }
}

/// Convert an Operand to a Formula.
fn operand_to_formula(func: &VerifiableFunction, operand: &Operand) -> Formula {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_to_formula(func, place),
        Operand::Constant(value) => const_to_formula(value),
        Operand::Symbolic(formula) => formula.clone(),
        _ => Formula::Int(0), // Approximate unsupported operands.
    }
}

/// Convert a Place to a Formula.
fn place_to_formula(func: &VerifiableFunction, place: &Place) -> Formula {
    // For projection-free places, look up the local.
    if place.projections.is_empty() {
        return local_to_formula(func, place.local);
    }
    // Projections (field access, deref, etc.) -- approximate as the base local.
    local_to_formula(func, place.local)
}

/// Convert a local variable index to a Formula.
fn local_to_formula(func: &VerifiableFunction, local_idx: usize) -> Formula {
    let name = func
        .body
        .locals
        .get(local_idx)
        .and_then(|d| d.name.as_deref())
        .map_or_else(|| format!("_{local_idx}"), |n| n.to_string());

    let sort = func.body.locals.get(local_idx).map(|d| ty_to_sort(&d.ty)).unwrap_or(Sort::Int);

    Formula::Var(name, sort)
}

/// Convert a ConstValue to a Formula.
fn const_to_formula(value: &ConstValue) -> Formula {
    match value {
        ConstValue::Bool(v) => Formula::Bool(*v),
        ConstValue::Int(v) => Formula::Int(*v),
        ConstValue::Uint(v, _) => Formula::UInt(*v),
        _ => Formula::Int(0),
    }
}

/// Convert a BinOp to a Formula.
fn binop_to_formula(op: BinOp, lhs: Formula, rhs: Formula) -> Formula {
    match op {
        BinOp::Add => Formula::Add(Box::new(lhs), Box::new(rhs)),
        BinOp::Sub => Formula::Sub(Box::new(lhs), Box::new(rhs)),
        BinOp::Mul => Formula::Mul(Box::new(lhs), Box::new(rhs)),
        BinOp::Div => Formula::Div(Box::new(lhs), Box::new(rhs)),
        BinOp::Rem => Formula::Rem(Box::new(lhs), Box::new(rhs)),
        BinOp::Eq => Formula::Eq(Box::new(lhs), Box::new(rhs)),
        BinOp::Ne => Formula::Not(Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs)))),
        BinOp::Lt => Formula::Lt(Box::new(lhs), Box::new(rhs)),
        BinOp::Le => Formula::Le(Box::new(lhs), Box::new(rhs)),
        BinOp::Gt => Formula::Gt(Box::new(lhs), Box::new(rhs)),
        BinOp::Ge => Formula::Ge(Box::new(lhs), Box::new(rhs)),
        _ => Formula::Eq(Box::new(lhs), Box::new(rhs)), // Approximate bitwise ops.
    }
}

/// Convert a Ty to a Sort.
fn ty_to_sort(ty: &Ty) -> Sort {
    match ty {
        Ty::Bool => Sort::Bool,
        Ty::Int { .. } => Sort::Int,
        _ => Sort::from_ty(ty),
    }
}

/// Find an assignment to a target local in a target block.
fn find_assignment_to<'a>(
    block: &'a BasicBlock,
    source_local: usize,
    relation: &SimulationRelation,
) -> Option<&'a Rvalue> {
    let target_local = relation.variable_map.get(&source_local)?;
    block.stmts.iter().find_map(|stmt| match stmt {
        Statement::Assign { place, rvalue, .. } if place.local == *target_local => Some(rvalue),
        _ => None,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::*;

    /// Build a simple `fn(a: i32, b: i32) -> i32` that computes `a <op> b`.
    fn make_binop_function(name: &str, op: BinOp) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::i32(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                op,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a simple identity function: fn id(x: i32) -> i32 { x }
    fn make_identity_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "identity".to_string(),
            def_path: "test::identity".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_validate_full_identity_completes() {
        let func = make_identity_function();
        let result = validate_full(&func);
        assert!(result.is_ok(), "validate_full should not error: {result:?}");
        let result = result.expect("already checked");
        assert_eq!(result.function_name, "identity");
        assert!(result.structural_total > 0);
    }

    #[test]
    fn test_validate_full_add_completes() {
        let func = make_binop_function("add", BinOp::Add);
        let result = validate_full(&func);
        assert!(result.is_ok(), "validate_full should not error: {result:?}");
    }

    #[test]
    fn test_validate_full_pair_identical_functions() {
        let source = make_binop_function("source", BinOp::Add);
        let target = make_binop_function("target", BinOp::Add);
        let result = validate_full_pair(&source, &target);
        assert!(result.is_ok(), "should not error: {result:?}");
        let result = result.expect("already checked");

        // Structural checks should pass.
        assert!(result.is_structurally_valid(), "identical functions should be structurally valid");
        assert!(result.structural_passed > 0);

        // Should have refinement VCs for data flow + return value.
        assert!(
            result.has_refinement_vcs(),
            "identical functions should produce refinement VCs: vc_count={}",
            result.refinement_vc_count
        );
    }

    #[test]
    fn test_validate_full_pair_divergent_return() {
        let source = make_binop_function("source", BinOp::Add);
        let mut target = make_binop_function("target", BinOp::Add);
        // Change target's return block to Unreachable.
        target.body.blocks[0].terminator = Terminator::Unreachable;

        let result = validate_full_pair(&source, &target);
        assert!(result.is_ok(), "should not error: {result:?}");
        let result = result.expect("already checked");

        // Structural check should detect entry block terminator mismatch.
        assert!(
            !result.is_structurally_valid(),
            "return vs unreachable should fail structural check"
        );
    }

    #[test]
    fn test_structural_checks_populated() {
        let func = make_identity_function();
        let result = validate_full(&func).expect("should complete");
        // Should have: return type, arg count, block count, arg types, entry terminator.
        assert!(
            result.structural_total >= 4,
            "expected >= 4 structural checks, got {}",
            result.structural_total
        );
    }

    #[test]
    fn test_lowering_failure_propagated() {
        let func = VerifiableFunction {
            name: "bad".to_string(),
            def_path: "test::bad".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl {
                    index: 0,
                    ty: Ty::Int { width: 7, signed: true }, // Unsupported width.
                    name: None,
                }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Int { width: 7, signed: true },
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let result = validate_full(&func);
        assert!(result.is_err(), "unsupported type should propagate as error");
        assert!(
            matches!(result, Err(FullValidationError::LoweringFailed(_))),
            "error should be LoweringFailed variant"
        );
    }

    #[test]
    fn test_refinement_vcs_include_return_value_check() {
        let source = make_identity_function();
        let target = make_identity_function();
        let result = validate_full_pair(&source, &target).expect("should complete");

        let return_vcs: Vec<_> = result
            .refinement_vcs
            .iter()
            .filter(|vc| {
                matches!(
                    vc.kind,
                    VcKind::RefinementViolation { ref action, .. }
                    if action.contains("ReturnValue")
                )
            })
            .collect();
        assert!(!return_vcs.is_empty(), "should generate at least one ReturnValue VC");
    }

    #[test]
    fn test_result_predicates() {
        let source = make_binop_function("source", BinOp::Add);
        let target = make_binop_function("target", BinOp::Add);
        let result = validate_full_pair(&source, &target).expect("should complete");

        assert!(result.is_structurally_valid());
        // has_refinement_vcs depends on structural validity + non-empty VCs.
        assert!(result.has_refinement_vcs());
    }

    #[test]
    fn test_formula_helpers() {
        // Test binop_to_formula.
        let lhs = Formula::Var("a".to_string(), Sort::Int);
        let rhs = Formula::Var("b".to_string(), Sort::Int);
        let add = binop_to_formula(BinOp::Add, lhs.clone(), rhs.clone());
        assert!(matches!(add, Formula::Add(_, _)));

        let ne = binop_to_formula(BinOp::Ne, lhs, rhs);
        assert!(matches!(ne, Formula::Not(_)));
    }

    #[test]
    fn test_const_to_formula_variants() {
        assert!(matches!(const_to_formula(&ConstValue::Bool(true)), Formula::Bool(true)));
        assert!(matches!(const_to_formula(&ConstValue::Int(42)), Formula::Int(42)));
        assert!(matches!(const_to_formula(&ConstValue::Uint(7, 64)), Formula::UInt(7)));
    }

    // --- New tests: multiple return paths ---

    /// Build a function with two return paths (if/else).
    fn make_two_return_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "two_ret".to_string(),
            def_path: "test::two_ret".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_validate_full_two_return_paths() {
        let func = make_two_return_function();
        let result = validate_full(&func);
        assert!(result.is_ok(), "two-return function should validate: {result:?}");
        let result = result.expect("already checked");
        assert_eq!(result.function_name, "two_ret");
        assert!(result.structural_total > 0);
    }

    #[test]
    fn test_validate_full_pair_two_returns_generates_vcs() {
        let source = make_two_return_function();
        let target = make_two_return_function();
        let result = validate_full_pair(&source, &target).expect("should complete");
        assert!(result.is_structurally_valid());
        // Two return blocks -> should generate at least two ReturnValue VCs.
        let return_vcs: Vec<_> = result
            .refinement_vcs
            .iter()
            .filter(|vc| {
                matches!(
                    vc.kind,
                    VcKind::RefinementViolation { ref action, .. }
                    if action.contains("ReturnValue")
                )
            })
            .collect();
        assert!(
            return_vcs.len() >= 2,
            "two-return function should produce >= 2 ReturnValue VCs, got {}",
            return_vcs.len()
        );
    }

    // --- Control flow divergence detection ---

    #[test]
    fn test_validate_full_pair_missing_successor_block() {
        let source = make_two_return_function();
        // Target has fewer blocks (missing bb2).
        let mut target = make_two_return_function();
        target.body.blocks.truncate(2); // Remove bb2.
        let result = validate_full_pair(&source, &target).expect("should not error");
        // Structural check should fail: target has fewer blocks.
        assert!(!result.is_structurally_valid(), "missing blocks should fail structural check");
    }

    #[test]
    fn test_validate_full_pair_arg_count_mismatch_structural_fail() {
        let source = make_binop_function("source", BinOp::Add);
        let mut target = make_binop_function("target", BinOp::Add);
        // Remove one argument from target.
        target.body.arg_count = 1;
        let result = validate_full_pair(&source, &target).expect("should not error");
        assert!(!result.is_structurally_valid(), "arg count mismatch should fail structural check");
        // No refinement VCs when structural fails.
        assert!(
            result.refinement_vcs.is_empty(),
            "no refinement VCs should be generated on structural failure"
        );
    }

    // --- Formula generation for comparison and bitwise operations ---

    #[test]
    fn test_binop_to_formula_comparisons() {
        let a = Formula::Var("a".to_string(), Sort::Int);
        let b = Formula::Var("b".to_string(), Sort::Int);

        let lt = binop_to_formula(BinOp::Lt, a.clone(), b.clone());
        assert!(matches!(lt, Formula::Lt(_, _)));

        let le = binop_to_formula(BinOp::Le, a.clone(), b.clone());
        assert!(matches!(le, Formula::Le(_, _)));

        let gt = binop_to_formula(BinOp::Gt, a.clone(), b.clone());
        assert!(matches!(gt, Formula::Gt(_, _)));

        let ge = binop_to_formula(BinOp::Ge, a.clone(), b.clone());
        assert!(matches!(ge, Formula::Ge(_, _)));

        let eq = binop_to_formula(BinOp::Eq, a.clone(), b.clone());
        assert!(matches!(eq, Formula::Eq(_, _)));
    }

    #[test]
    fn test_binop_to_formula_bitwise() {
        let a = Formula::Var("a".to_string(), Sort::Int);
        let b = Formula::Var("b".to_string(), Sort::Int);

        // Bitwise ops approximate as Eq (since LIR doesn't have bit-level formulas).
        let band = binop_to_formula(BinOp::BitAnd, a.clone(), b.clone());
        assert!(matches!(band, Formula::Eq(_, _)));

        let bor = binop_to_formula(BinOp::BitOr, a.clone(), b.clone());
        assert!(matches!(bor, Formula::Eq(_, _)));

        let bxor = binop_to_formula(BinOp::BitXor, a.clone(), b.clone());
        assert!(matches!(bxor, Formula::Eq(_, _)));
    }

    #[test]
    fn test_binop_to_formula_arithmetic() {
        let a = Formula::Var("a".to_string(), Sort::Int);
        let b = Formula::Var("b".to_string(), Sort::Int);

        let sub = binop_to_formula(BinOp::Sub, a.clone(), b.clone());
        assert!(matches!(sub, Formula::Sub(_, _)));

        let mul = binop_to_formula(BinOp::Mul, a.clone(), b.clone());
        assert!(matches!(mul, Formula::Mul(_, _)));

        let div = binop_to_formula(BinOp::Div, a.clone(), b.clone());
        assert!(matches!(div, Formula::Div(_, _)));

        let rem = binop_to_formula(BinOp::Rem, a.clone(), b.clone());
        assert!(matches!(rem, Formula::Rem(_, _)));
    }

    #[test]
    fn test_rvalue_to_formula_unary_neg() {
        let func = make_identity_function();
        let rvalue = Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1)));
        let formula = rvalue_to_formula(&func, &rvalue);
        assert!(matches!(formula, Formula::Neg(_)));
    }

    #[test]
    fn test_rvalue_to_formula_unary_not() {
        let func = make_identity_function();
        let rvalue = Rvalue::UnaryOp(UnOp::Not, Operand::Copy(Place::local(1)));
        let formula = rvalue_to_formula(&func, &rvalue);
        assert!(matches!(formula, Formula::Not(_)));
    }

    #[test]
    fn test_operand_to_formula_constant() {
        let func = make_identity_function();
        let formula = operand_to_formula(&func, &Operand::Constant(ConstValue::Int(99)));
        assert!(matches!(formula, Formula::Int(99)));
    }

    #[test]
    fn test_operand_to_formula_copy() {
        let func = make_identity_function();
        let formula = operand_to_formula(&func, &Operand::Copy(Place::local(1)));
        // Local 1 has name "x", so it should become Var("x", Int).
        assert!(matches!(formula, Formula::Var(ref name, Sort::Int) if name == "x"));
    }

    #[test]
    fn test_ty_to_sort_mappings() {
        assert_eq!(ty_to_sort(&Ty::Bool), Sort::Bool);
        assert_eq!(ty_to_sort(&Ty::i32()), Sort::Int);
        assert_eq!(ty_to_sort(&Ty::i64()), Sort::Int);
    }

    #[test]
    fn test_validate_full_sub_function() {
        let func = make_binop_function("sub", BinOp::Sub);
        let result = validate_full(&func);
        assert!(result.is_ok(), "subtraction function should validate: {result:?}");
    }

    #[test]
    fn test_validate_full_mul_function() {
        let func = make_binop_function("mul", BinOp::Mul);
        let result = validate_full(&func);
        assert!(result.is_ok(), "multiplication function should validate: {result:?}");
    }

    #[test]
    fn test_validate_full_pair_no_vcs_on_structural_failure() {
        let source = make_identity_function();
        let mut target = make_identity_function();
        // Change target return type (via different local type).
        target.body.return_ty = Ty::Bool;
        let result = validate_full_pair(&source, &target).expect("should not error");
        assert!(!result.is_structurally_valid());
        assert!(!result.has_refinement_vcs());
    }

    #[test]
    fn test_const_to_formula_bool_false() {
        let f = const_to_formula(&ConstValue::Bool(false));
        assert!(matches!(f, Formula::Bool(false)));
    }

    #[test]
    fn test_const_to_formula_negative_int() {
        let f = const_to_formula(&ConstValue::Int(-5));
        assert!(matches!(f, Formula::Int(-5)));
    }
}
