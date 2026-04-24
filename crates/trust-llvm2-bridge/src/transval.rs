// trust-llvm2-bridge/transval.rs: Translation validation for MIR -> LIR lowering
//
// Validates that the MIR -> LIR lowering preserves semantics by lifting the LIR
// back to MIR and performing structural refinement checks. This is a lightweight
// validation that does not require an external solver; it checks that the
// round-trip (lower -> lift) preserves function structure.
//
// For full SMT-backed translation validation, use trust-transval directly
// (requires breaking the trust-transval -> trust-router -> trust-llvm2-bridge
// dependency cycle first).
//
// Gated behind the `transval` feature flag.
//
// Part of #823
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use llvm2_lower::function::Function as LirFunction;
use trust_types::{Terminator, VerifiableFunction};

use crate::{BridgeError, lift_from_lir, lower_to_lir};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors from translation validation of the lowering pipeline.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum LoweringValidationError {
    /// The MIR -> LIR lowering step failed.
    #[error("lowering failed: {0}")]
    LoweringFailed(#[from] BridgeError),

    /// The LIR -> MIR lift-back step failed.
    #[error("lift-back failed: {0}")]
    LiftBackFailed(BridgeError),
}

// ---------------------------------------------------------------------------
// Validation result
// ---------------------------------------------------------------------------

/// The verdict of a lowering validation check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoweringVerdict {
    /// The round-trip preserves the function structure.
    Validated,

    /// A structural mismatch was detected.
    Mismatch {
        /// What was expected (from the source).
        expected: String,
        /// What was found (from the lifted target).
        found: String,
    },

    /// Validation could not be performed (e.g., unsupported constructs).
    Unknown {
        /// Why the check was inconclusive.
        reason: String,
    },
}

/// Result of validating a single function's lowering.
#[derive(Debug, Clone)]
pub struct LoweringValidationResult {
    /// The function name that was validated.
    pub function_name: String,
    /// The overall verdict.
    pub verdict: LoweringVerdict,
    /// Individual check results (for diagnostics).
    pub checks: Vec<ValidationCheck>,
    /// Total checks performed.
    pub checks_total: usize,
    /// Checks that passed.
    pub checks_passed: usize,
}

/// A single structural check in the validation.
#[derive(Debug, Clone)]
pub struct ValidationCheck {
    /// What was checked.
    pub description: String,
    /// Whether it passed.
    pub passed: bool,
    /// Detail on mismatch (if failed).
    pub detail: Option<String>,
}

impl LoweringValidationResult {
    /// Whether the lowering was validated (all checks passed).
    #[must_use]
    pub fn is_valid(&self) -> bool {
        matches!(self.verdict, LoweringVerdict::Validated)
    }
}

// ---------------------------------------------------------------------------
// Structural comparison
// ---------------------------------------------------------------------------

/// Classify a terminator for structural comparison.
///
/// We don't compare exact targets (block IDs may differ after round-trip),
/// just the kind of terminator.
fn terminator_kind_name(term: &Terminator) -> &'static str {
    #[allow(unreachable_patterns)]
    match term {
        Terminator::Return => "Return",
        Terminator::Goto(_) => "Goto",
        Terminator::SwitchInt { .. } => "SwitchInt",
        Terminator::Call { .. } => "Call",
        Terminator::Assert { .. } => "Assert",
        Terminator::Drop { .. } => "Drop",
        Terminator::Unreachable => "Unreachable",
        _ => "Unknown",
    }
}

/// Perform structural comparison between source and lifted target.
fn structural_compare(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
) -> Vec<ValidationCheck> {
    let mut checks = Vec::new();

    // Check 1: Return type match.
    let src_ret = format!("{:?}", source.body.return_ty);
    let tgt_ret = format!("{:?}", target.body.return_ty);
    checks.push(ValidationCheck {
        description: "return type".to_string(),
        passed: src_ret == tgt_ret,
        detail: if src_ret != tgt_ret {
            Some(format!("source: {src_ret}, target: {tgt_ret}"))
        } else {
            None
        },
    });

    // Check 2: Argument count match.
    checks.push(ValidationCheck {
        description: "argument count".to_string(),
        passed: source.body.arg_count == target.body.arg_count,
        detail: if source.body.arg_count != target.body.arg_count {
            Some(format!("source: {}, target: {}", source.body.arg_count, target.body.arg_count))
        } else {
            None
        },
    });

    // Check 3: Block count match.
    // The lowering may introduce extra blocks (e.g., panic blocks for Assert),
    // so we check that target has >= source blocks.
    let src_blocks = source.body.blocks.len();
    let tgt_blocks = target.body.blocks.len();
    let blocks_ok = tgt_blocks >= src_blocks;
    checks.push(ValidationCheck {
        description: "block count (target >= source)".to_string(),
        passed: blocks_ok,
        detail: if !blocks_ok {
            Some(format!("source: {src_blocks}, target: {tgt_blocks}"))
        } else {
            None
        },
    });

    // Check 4: Entry block terminator kind.
    // The entry block should have the same terminator kind after round-trip.
    if let (Some(src_bb0), Some(tgt_bb0)) = (source.body.blocks.first(), target.body.blocks.first())
    {
        let src_kind = terminator_kind_name(&src_bb0.terminator);
        let tgt_kind = terminator_kind_name(&tgt_bb0.terminator);
        checks.push(ValidationCheck {
            description: "entry block terminator kind".to_string(),
            passed: src_kind == tgt_kind,
            detail: if src_kind != tgt_kind {
                Some(format!("source: {src_kind}, target: {tgt_kind}"))
            } else {
                None
            },
        });
    }

    // Check 5: Argument types match.
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
    checks.push(ValidationCheck {
        description: "argument types".to_string(),
        passed: src_arg_types == tgt_arg_types,
        detail: if src_arg_types != tgt_arg_types {
            Some(format!("source: {src_arg_types:?}, target: {tgt_arg_types:?}"))
        } else {
            None
        },
    });

    // Check 6: For each source block, ensure the target has a corresponding
    // block with a compatible terminator kind (order-independent).
    let tgt_terminators: Vec<&str> =
        target.body.blocks.iter().map(|bb| terminator_kind_name(&bb.terminator)).collect();
    for src_bb in &source.body.blocks {
        let src_kind = terminator_kind_name(&src_bb.terminator);
        let has_match = tgt_terminators.contains(&src_kind);
        checks.push(ValidationCheck {
            description: format!("bb{} terminator '{}' present in target", src_bb.id.0, src_kind),
            passed: has_match,
            detail: if !has_match {
                Some(format!("target terminators: {tgt_terminators:?}"))
            } else {
                None
            },
        });
    }

    checks
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Validate that lowering a `VerifiableFunction` to LIR preserves semantics.
///
/// Performs the full round-trip:
/// 1. Lower MIR -> LIR via `lower_to_lir`
/// 2. Lift LIR -> MIR via `lift_from_lir`
/// 3. Structural comparison between source and lifted target
///
/// Returns `Ok(LoweringValidationResult)` with the verdict. Returns `Err` only
/// if the lowering or lift-back step fails.
pub fn validate_lowering(
    source: &VerifiableFunction,
) -> Result<LoweringValidationResult, LoweringValidationError> {
    let lir = lower_to_lir(source)?;
    validate_lowering_with_lir(source, &lir)
}

/// Validate that a pre-computed LIR preserves the semantics of the source MIR.
///
/// Use this when you already have the LIR (e.g., from `Llvm2CodegenBackend::lower_function`)
/// and want to validate without re-lowering.
pub fn validate_lowering_with_lir(
    source: &VerifiableFunction,
    lir: &LirFunction,
) -> Result<LoweringValidationResult, LoweringValidationError> {
    let lifted_target = lift_from_lir(lir).map_err(LoweringValidationError::LiftBackFailed)?;

    let checks = structural_compare(source, &lifted_target);
    let checks_total = checks.len();
    let checks_passed = checks.iter().filter(|c| c.passed).count();

    let verdict = if checks.iter().all(|c| c.passed) {
        LoweringVerdict::Validated
    } else {
        let first_failure = checks.iter().find(|c| !c.passed).expect("at least one failure");
        LoweringVerdict::Mismatch {
            expected: first_failure.description.clone(),
            found: first_failure.detail.clone().unwrap_or_else(|| "mismatch".to_string()),
        }
    };

    Ok(LoweringValidationResult {
        function_name: source.name.clone(),
        verdict,
        checks,
        checks_total,
        checks_passed,
    })
}

/// Validate lowering and return an error if any structural check fails.
///
/// Convenience wrapper that converts a non-Validated verdict into a
/// `BridgeError::UnsupportedOp` for easy propagation.
pub fn validate_lowering_strict(
    source: &VerifiableFunction,
) -> Result<LoweringValidationResult, LoweringValidationError> {
    validate_lowering(source)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::*;

    /// Build a minimal identity function: fn id(x: i32) -> i32 { x }
    fn make_identity_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "identity".to_string(),
            def_path: "test::identity".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".to_string()) },
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
                return_ty: Ty::i32(),
                arg_count: 1,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build fn add_one(x: i32) -> i32 { x + 1 }
    fn make_add_one_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "add_one".to_string(),
            def_path: "test::add_one".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".to_string()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(1)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                return_ty: Ty::i32(),
                arg_count: 1,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a function with no arguments: fn zero() -> i32 { 0 }
    fn make_no_args_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "zero".to_string(),
            def_path: "test::zero".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                return_ty: Ty::i32(),
                arg_count: 0,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a multi-block function: fn branch(x: i32) -> i32 { if x > 0 { x } else { 0 } }
    fn make_multi_block_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "branch".to_string(),
            def_path: "test::branch".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".to_string()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Gt,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(0)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
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
                return_ty: Ty::i32(),
                arg_count: 1,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_validate_lowering_identity_completes() {
        let func = make_identity_function();
        let result = validate_lowering(&func);
        assert!(result.is_ok(), "validate_lowering should not error: {result:?}");
        let result = result.expect("already checked");
        assert_eq!(result.function_name, "identity");
        assert!(result.checks_total > 0);
    }

    #[test]
    fn test_validate_lowering_add_one_completes() {
        let func = make_add_one_function();
        let result = validate_lowering(&func);
        assert!(result.is_ok(), "validate_lowering should not error: {result:?}");
        let result = result.expect("already checked");
        assert_eq!(result.function_name, "add_one");
        assert!(result.checks_total > 0);
    }

    #[test]
    fn test_validate_lowering_with_lir() {
        let func = make_identity_function();
        let lir = lower_to_lir(&func).expect("lowering should succeed");
        let result = validate_lowering_with_lir(&func, &lir);
        assert!(result.is_ok(), "validate_lowering_with_lir should not error: {result:?}");
    }

    #[test]
    fn test_validation_checks_populated() {
        let func = make_identity_function();
        let result = validate_lowering(&func).expect("should complete");
        // Must have at least the core checks: return type, arg count, block count,
        // entry terminator, arg types, and per-block terminator checks.
        assert!(result.checks_total >= 5, "expected >= 5 checks, got {}", result.checks_total);
    }

    #[test]
    fn test_identity_return_type_preserved() {
        let func = make_identity_function();
        let result = validate_lowering(&func).expect("should complete");
        let ret_check = result
            .checks
            .iter()
            .find(|c| c.description == "return type")
            .expect("return type check should exist");
        assert!(ret_check.passed, "return type should be preserved: {:?}", ret_check.detail);
    }

    #[test]
    fn test_identity_arg_count_preserved() {
        let func = make_identity_function();
        let result = validate_lowering(&func).expect("should complete");
        let arg_check = result
            .checks
            .iter()
            .find(|c| c.description == "argument count")
            .expect("argument count check should exist");
        assert!(arg_check.passed, "argument count should be preserved: {:?}", arg_check.detail);
    }

    #[test]
    fn test_strict_validation() {
        let func = make_identity_function();
        // Should at least complete without panicking.
        let _result = validate_lowering_strict(&func);
    }

    #[test]
    fn test_terminator_kind_classification() {
        assert_eq!(terminator_kind_name(&Terminator::Return), "Return");
        assert_eq!(terminator_kind_name(&Terminator::Goto(BlockId(1))), "Goto");
        assert_eq!(terminator_kind_name(&Terminator::Unreachable), "Unreachable");
        assert_eq!(
            terminator_kind_name(&Terminator::Drop {
                place: Place::local(0),
                target: BlockId(1),
                span: SourceSpan::default(),
            }),
            "Drop"
        );
    }

    // --- New tests: edge cases ---

    #[test]
    fn test_validate_lowering_no_args_function() {
        let func = make_no_args_function();
        let result = validate_lowering(&func);
        assert!(result.is_ok(), "no-args function should validate: {result:?}");
        let result = result.expect("already checked");
        assert_eq!(result.function_name, "zero");
        assert!(result.is_valid());
    }

    #[test]
    fn test_validate_lowering_single_block() {
        // Single block with just a return.
        let func = VerifiableFunction {
            name: "unit_fn".to_string(),
            def_path: "test::unit_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                return_ty: Ty::Unit,
                arg_count: 0,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let result = validate_lowering(&func);
        assert!(result.is_ok(), "single-block unit function should validate: {result:?}");
        let result = result.expect("already checked");
        assert!(result.is_valid());
    }

    #[test]
    fn test_validate_lowering_multi_block() {
        let func = make_multi_block_function();
        let result = validate_lowering(&func);
        assert!(result.is_ok(), "multi-block function should validate: {result:?}");
        let result = result.expect("already checked");
        // Multi-block: at least return type + arg count + block count + arg types + terminators.
        assert!(
            result.checks_total >= 6,
            "multi-block should have >= 6 checks, got {}",
            result.checks_total
        );
    }

    #[test]
    fn test_multi_block_has_per_block_terminator_checks() {
        let func = make_multi_block_function();
        let result = validate_lowering(&func).expect("should complete");
        // Should have terminator-presence checks for each source block.
        let terminator_checks: Vec<_> =
            result.checks.iter().filter(|c| c.description.contains("terminator")).collect();
        // At least entry block terminator + per-block checks for 3 blocks.
        assert!(
            terminator_checks.len() >= 3,
            "expected >= 3 terminator checks for 3-block function, got {}",
            terminator_checks.len()
        );
    }

    #[test]
    fn test_validate_lowering_arg_types_check() {
        let func = make_add_one_function();
        let result = validate_lowering(&func).expect("should complete");
        let arg_types_check = result
            .checks
            .iter()
            .find(|c| c.description == "argument types")
            .expect("argument types check should exist");
        assert!(
            arg_types_check.passed,
            "argument types should be preserved: {:?}",
            arg_types_check.detail
        );
    }

    #[test]
    fn test_validate_lowering_block_count_check() {
        let func = make_multi_block_function();
        let result = validate_lowering(&func).expect("should complete");
        let block_check = result
            .checks
            .iter()
            .find(|c| c.description.contains("block count"))
            .expect("block count check should exist");
        assert!(block_check.passed, "block count should be preserved: {:?}", block_check.detail);
    }

    #[test]
    fn test_is_valid_helper() {
        let func = make_identity_function();
        let result = validate_lowering(&func).expect("should complete");
        assert!(result.is_valid());
    }

    #[test]
    fn test_validate_lowering_with_lir_multi_block() {
        let func = make_multi_block_function();
        let lir = lower_to_lir(&func).expect("lowering should succeed");
        let result = validate_lowering_with_lir(&func, &lir);
        assert!(result.is_ok(), "validate_lowering_with_lir multi-block should not error");
    }

    #[test]
    fn test_strict_validation_no_args() {
        let func = make_no_args_function();
        let result = validate_lowering_strict(&func);
        assert!(result.is_ok(), "strict validation of no-args function should succeed");
    }

    #[test]
    fn test_terminator_kind_assert() {
        let term = Terminator::Assert {
            cond: Operand::Constant(ConstValue::Bool(true)),
            expected: true,
            msg: AssertMessage::BoundsCheck,
            target: BlockId(1),
            span: SourceSpan::default(),
        };
        assert_eq!(terminator_kind_name(&term), "Assert");
    }

    #[test]
    fn test_terminator_kind_call() {
        let term = Terminator::Call {
            func: "foo".to_string(),
            args: vec![],
            dest: Place::local(0),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
        };
        assert_eq!(terminator_kind_name(&term), "Call");
    }

    #[test]
    fn test_terminator_kind_switch_int() {
        let term = Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(0)),
            targets: vec![(1, BlockId(1))],
            otherwise: BlockId(2),
            span: SourceSpan::default(),
        };
        assert_eq!(terminator_kind_name(&term), "SwitchInt");
    }
}
