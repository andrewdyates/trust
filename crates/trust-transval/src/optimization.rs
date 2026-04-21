// trust-transval: Optimization pass validator
//
// Validates known MIR optimization passes by applying pass-specific strategies.
// Each optimization type has tailored simulation relation construction and
// VC generation that accounts for the optimization's semantics.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::error::TransvalError;
use crate::refinement::{RefinementChecker, ValidationResult};
use crate::simulation::SimulationRelationBuilder;

/// Known MIR optimization passes.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[non_exhaustive]
pub enum OptimizationPass {
    /// Replaces expressions with compile-time constants.
    ConstantFolding,
    /// Removes assignments whose results are never used.
    DeadCodeElimination,
    /// Replaces function calls with the callee body.
    Inlining,
    /// Substitutes copies: `_2 = _1; use _2` -> `use _1`.
    CopyPropagation,
    /// Replaces expensive operations with cheaper equivalents (e.g., `x * 2` -> `x << 1`).
    StrengthReduction,
    /// An unrecognized or custom optimization.
    Other(String),
}

impl std::fmt::Display for OptimizationPass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ConstantFolding => write!(f, "constant_folding"),
            Self::DeadCodeElimination => write!(f, "dead_code_elimination"),
            Self::Inlining => write!(f, "inlining"),
            Self::CopyPropagation => write!(f, "copy_propagation"),
            Self::StrengthReduction => write!(f, "strength_reduction"),
            Self::Other(name) => write!(f, "other({name})"),
        }
    }
}

/// Validates specific optimization passes with tailored strategies.
#[derive(Debug, Clone, Default)]
pub struct OptimizationPassValidator;

impl OptimizationPassValidator {
    /// Create a new validator.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self
    }

    /// Validate that an optimization pass preserved semantics.
    ///
    /// Uses pass-specific strategies for building simulation relations and
    /// analyzing the transformation.
    pub(crate) fn validate_pass(
        &self,
        pass: &OptimizationPass,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> Result<ValidationResult, TransvalError> {
        match pass {
            OptimizationPass::ConstantFolding => self.validate_constant_folding(source, target),
            OptimizationPass::DeadCodeElimination => self.validate_dce(source, target),
            OptimizationPass::CopyPropagation => self.validate_copy_propagation(source, target),
            OptimizationPass::StrengthReduction => {
                // Generic check: strength reduction preserves values.
                self.validate_generic(source, target)
            }
            OptimizationPass::Inlining => {
                // Inlining changes block count significantly; use generic.
                self.validate_generic(source, target)
            }
            OptimizationPass::Other(name) => {
                // Unknown optimization: fall back to generic refinement check.
                let result = self.validate_generic(source, target)?;
                if result.checks_total == 0 {
                    return Err(TransvalError::UnsupportedOptimization(name.clone()));
                }
                Ok(result)
            }
        }
    }

    /// Detect which optimizations were likely applied between source and target.
    ///
    /// Heuristic analysis comparing function structure.
    #[must_use]
    pub(crate) fn detect_pass(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> Vec<OptimizationPass> {
        let mut detected = Vec::new();

        // DCE: target has fewer statements than source.
        let source_stmts: usize = source.body.blocks.iter().map(|b| b.stmts.len()).sum();
        let target_stmts: usize = target.body.blocks.iter().map(|b| b.stmts.len()).sum();
        if target_stmts < source_stmts {
            detected.push(OptimizationPass::DeadCodeElimination);
        }

        // Constant folding: target has more constants than source.
        let source_consts = count_constants(&source.body);
        let target_consts = count_constants(&target.body);
        if target_consts > source_consts {
            detected.push(OptimizationPass::ConstantFolding);
        }

        // Copy propagation: target has fewer Use(Copy) rvalues.
        let source_copies = count_copy_uses(&source.body);
        let target_copies = count_copy_uses(&target.body);
        if target_copies < source_copies {
            detected.push(OptimizationPass::CopyPropagation);
        }

        // Inlining: target has more blocks and locals than source.
        if target.body.blocks.len() > source.body.blocks.len()
            && target.body.locals.len() > source.body.locals.len()
        {
            detected.push(OptimizationPass::Inlining);
        }

        detected
    }

    /// Validate constant folding: build expression map for folded constants.
    fn validate_constant_folding(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> Result<ValidationResult, TransvalError> {
        // For constant folding, expressions change but values should be preserved.
        // We look for assignments in the source that become constants in the target.
        let mut builder = SimulationRelationBuilder::new();

        // Find source assignments that were folded to constants in target.
        for (sb, tb) in source.body.blocks.iter().zip(target.body.blocks.iter()) {
            for (ss, ts) in sb.stmts.iter().zip(tb.stmts.iter()) {
                if let (
                    Statement::Assign { place: sp, rvalue: sr, .. },
                    Statement::Assign { rvalue: Rvalue::Use(Operand::Constant(cv)), .. },
                ) = (ss, ts)
                {
                    // Source had a complex rvalue, target folded to constant.
                    if !matches!(sr, Rvalue::Use(Operand::Constant(_))) {
                        let formula = const_to_formula(cv);
                        builder = builder.with_expression(sp.local, formula);
                    }
                }
            }
        }

        let relation = builder.build_from_functions(source, target)?;
        let checker = RefinementChecker::new();
        checker.check_with_relation(source, target, &relation)
    }

    /// Validate DCE: check that non-dead assignments are preserved.
    fn validate_dce(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> Result<ValidationResult, TransvalError> {
        // DCE removes dead assignments. The key property is that all
        // live assignments and the return value are preserved.
        // We can use a standard refinement check since DCE only removes code.
        let checker = RefinementChecker::new().skip_termination();
        checker.check(source, target)
    }

    /// Validate copy propagation: ensure substituted values are equivalent.
    fn validate_copy_propagation(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> Result<ValidationResult, TransvalError> {
        // Copy propagation replaces `_x = _y; use _x` with `use _y`.
        // A standard refinement check validates this since the simulation
        // relation maps the same locals.
        let checker = RefinementChecker::new();
        checker.check(source, target)
    }

    /// Generic validation: no pass-specific strategy.
    fn validate_generic(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> Result<ValidationResult, TransvalError> {
        let checker = RefinementChecker::new();
        checker.check(source, target)
    }
}

/// Convert a constant value to a formula.
///
/// tRust #458: ConstValue is #[non_exhaustive] — unknown variants produce an
/// unconstrained symbolic variable instead of panicking.
fn const_to_formula(cv: &ConstValue) -> Formula {
    match cv {
        ConstValue::Bool(b) => Formula::Bool(*b),
        ConstValue::Int(n) => Formula::Int(*n),
        ConstValue::Uint(n, _) => match i128::try_from(*n) {
            Ok(n) => Formula::Int(n),
            Err(_) => Formula::UInt(*n),
        },
        ConstValue::Float(_) => Formula::Int(0), // Approximate.
        ConstValue::Unit => Formula::Bool(true),
        // tRust #458: Unknown variant — produce an unconstrained symbolic variable.
        _ => Formula::Var("__unknown_const".to_string(), trust_types::Sort::Int),
    }
}

/// Count constant operands in a function body.
fn count_constants(body: &VerifiableBody) -> usize {
    body.blocks
        .iter()
        .flat_map(|b| b.stmts.iter())
        .filter(|s| {
            matches!(s, Statement::Assign { rvalue: Rvalue::Use(Operand::Constant(_)), .. })
        })
        .count()
}

/// Count Use(Copy(_)) rvalues (copy propagation candidates).
fn count_copy_uses(body: &VerifiableBody) -> usize {
    body.blocks
        .iter()
        .flat_map(|b| b.stmts.iter())
        .filter(|s| matches!(s, Statement::Assign { rvalue: Rvalue::Use(Operand::Copy(_)), .. }))
        .count()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::refinement::ValidationVerdict;

    fn add_function(name: &str) -> VerifiableFunction {
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
                                BinOp::Add,
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

    fn constant_folded_target() -> VerifiableFunction {
        VerifiableFunction {
            name: "target".to_string(),
            def_path: "test::target".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // Folded: _2 = _1 (instead of _2 = _1 + 0)
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
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
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn add_zero_source() -> VerifiableFunction {
        VerifiableFunction {
            name: "source".to_string(),
            def_path: "test::source".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
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
                                Operand::Constant(ConstValue::Int(0)),
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
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn dce_pair() -> (VerifiableFunction, VerifiableFunction) {
        let source = VerifiableFunction {
            name: "source".to_string(),
            def_path: "test::source".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // Dead assignment.
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(99))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let target = VerifiableFunction {
            name: "target".to_string(),
            def_path: "test::target".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // Dead assignment removed.
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        (source, target)
    }

    #[test]
    fn test_validate_identical_functions() {
        let source = add_function("source");
        let target = add_function("target");
        let validator = OptimizationPassValidator::new();

        let result = validator
            .validate_pass(&OptimizationPass::Other("identity".into()), &source, &target)
            .unwrap();
        assert_eq!(result.verdict, ValidationVerdict::Validated);
    }

    #[test]
    fn test_validate_dce() {
        let (source, target) = dce_pair();
        let validator = OptimizationPassValidator::new();

        let result = validator
            .validate_pass(&OptimizationPass::DeadCodeElimination, &source, &target)
            .unwrap();
        // DCE should produce VCs for the remaining live assignments.
        assert!(result.checks_total > 0);
    }

    #[test]
    fn test_validate_constant_folding() {
        let source = add_zero_source();
        let target = constant_folded_target();
        let validator = OptimizationPassValidator::new();

        let result =
            validator.validate_pass(&OptimizationPass::ConstantFolding, &source, &target).unwrap();
        assert!(result.checks_total > 0);
    }

    #[test]
    fn test_validate_copy_propagation() {
        let source = add_function("source");
        let target = add_function("target");
        let validator = OptimizationPassValidator::new();

        let result =
            validator.validate_pass(&OptimizationPass::CopyPropagation, &source, &target).unwrap();
        assert_eq!(result.verdict, ValidationVerdict::Validated);
    }

    #[test]
    fn test_detect_pass_dce() {
        let (source, target) = dce_pair();
        let validator = OptimizationPassValidator::new();

        let detected = validator.detect_pass(&source, &target);
        assert!(
            detected.contains(&OptimizationPass::DeadCodeElimination),
            "should detect DCE, got: {detected:?}"
        );
    }

    #[test]
    fn test_detect_pass_empty_for_identical() {
        let source = add_function("source");
        let target = add_function("target");
        let validator = OptimizationPassValidator::new();

        let detected = validator.detect_pass(&source, &target);
        // Identical functions: no optimizations detected.
        assert!(
            detected.is_empty(),
            "identical functions should detect no optimizations, got: {detected:?}"
        );
    }

    #[test]
    fn test_optimization_pass_display() {
        assert_eq!(OptimizationPass::ConstantFolding.to_string(), "constant_folding");
        assert_eq!(OptimizationPass::DeadCodeElimination.to_string(), "dead_code_elimination");
        assert_eq!(OptimizationPass::Other("custom".into()).to_string(), "other(custom)");
    }

    #[test]
    fn test_const_to_formula_values() {
        assert_eq!(const_to_formula(&ConstValue::Int(42)), Formula::Int(42));
        assert_eq!(const_to_formula(&ConstValue::Bool(true)), Formula::Bool(true));
        assert_eq!(const_to_formula(&ConstValue::Uint(7, 64)), Formula::Int(7));
    }
}
