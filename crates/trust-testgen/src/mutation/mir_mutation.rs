// trust-testgen/mutation/mir_mutation.rs: MIR-level mutation generation
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{BinOp, ConstValue, Operand, Rvalue, Statement, UnOp, VerifiableFunction};

use super::types::{MirMutant, MutationResult, MutationType};
use crate::GeneratedTest;

/// Generator for mutation testing targets.
pub struct MutationGenerator;

impl MutationGenerator {
    /// Generate all possible mutants for the given source code.
    #[must_use]
    pub fn generate_mutants(source: &str) -> Vec<super::types::Mutant> {
        super::source_mutation::generate_mutants(source)
    }

    /// Generate MIR-level mutants for a `VerifiableFunction`.
    #[must_use]
    pub fn generate_mir_mutants(func: &VerifiableFunction) -> Vec<MirMutant> {
        generate_mutants_from_func(func)
    }

    /// Calculate the mutation score using structural analysis.
    ///
    /// The mutation score is the fraction of mutants that would be detected
    /// ("killed") by the given test suite. A test kills a mutant if its
    /// assertions structurally constrain the operation being mutated.
    #[must_use]
    pub fn mutation_score(tests: &[GeneratedTest], mutants: &[super::types::Mutant]) -> f64 {
        super::source_mutation::mutation_score(tests, mutants)
    }

    /// Calculate the mutation score using the original heuristic (string containment).
    #[must_use]
    pub fn mutation_score_heuristic(tests: &[GeneratedTest], mutants: &[super::types::Mutant]) -> f64 {
        super::source_mutation::mutation_score_heuristic(tests, mutants)
    }

    /// Calculate the mutation score for MIR-level mutants.
    ///
    /// Returns the fraction of mutants that have `MutationResult::Killed`.
    #[must_use]
    pub fn mir_mutation_score(mutants: &[MirMutant]) -> f64 {
        mir_mutation_score(mutants)
    }
}

/// Generate MIR-level mutants from a `VerifiableFunction`.
///
/// Walks the function's basic blocks and statements, generating mutants
/// for each mutable construct: operator replacements, constant shifts,
/// operand swaps, and unary operation changes.
#[must_use]
pub fn generate_mutants_from_func(func: &VerifiableFunction) -> Vec<MirMutant> {
    let mut mutants = Vec::new();

    for (block_idx, block) in func.body.blocks.iter().enumerate() {
        for (stmt_idx, stmt) in block.stmts.iter().enumerate() {
            match stmt {
                Statement::Assign { place, rvalue, span } => {
                    // Generate operator replacement mutants
                    generate_rvalue_mutants(
                        &mut mutants,
                        block_idx,
                        stmt_idx,
                        place,
                        rvalue,
                        span,
                    );
                }
                Statement::Nop => {}
                _ => {},
            }
        }
    }

    mutants
}

/// Generate mutants for an Rvalue in a statement.
fn generate_rvalue_mutants(
    mutants: &mut Vec<MirMutant>,
    block_idx: usize,
    stmt_idx: usize,
    place: &trust_types::Place,
    rvalue: &Rvalue,
    span: &trust_types::SourceSpan,
) {
    match rvalue {
        Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let is_checked = matches!(rvalue, Rvalue::CheckedBinaryOp(..));

            // Arithmetic operator replacement
            for alt_op in alternative_ops(*op) {
                let mutated_rvalue = if is_checked {
                    Rvalue::CheckedBinaryOp(alt_op, lhs.clone(), rhs.clone())
                } else {
                    Rvalue::BinaryOp(alt_op, lhs.clone(), rhs.clone())
                };
                let mutation_type = if op.is_arithmetic() && alt_op.is_arithmetic() {
                    MutationType::ArithOp
                } else if op.is_comparison() && alt_op.is_comparison() {
                    MutationType::CompOp
                } else {
                    MutationType::BoolOp
                };
                mutants.push(MirMutant {
                    block_idx,
                    stmt_idx,
                    mutation_type,
                    original_desc: format!("{op:?}"),
                    mutated_desc: format!("{alt_op:?}"),
                    mutated_stmt: Statement::Assign {
                        place: place.clone(),
                        rvalue: mutated_rvalue,
                        span: span.clone(),
                    },
                    result: MutationResult::Survived,
                });
            }

            // Operand swap (for non-commutative operators)
            if !op.is_commutative() {
                let swapped_rvalue = if is_checked {
                    Rvalue::CheckedBinaryOp(*op, rhs.clone(), lhs.clone())
                } else {
                    Rvalue::BinaryOp(*op, rhs.clone(), lhs.clone())
                };
                mutants.push(MirMutant {
                    block_idx,
                    stmt_idx,
                    mutation_type: MutationType::ArithOp,
                    original_desc: format!("{op:?}(lhs, rhs)"),
                    mutated_desc: format!("{op:?}(rhs, lhs)"),
                    mutated_stmt: Statement::Assign {
                        place: place.clone(),
                        rvalue: swapped_rvalue,
                        span: span.clone(),
                    },
                    result: MutationResult::Survived,
                });
            }
        }

        Rvalue::UnaryOp(op, operand) => {
            // Negate <-> Not swap (only meaningful for Not/Neg)
            // tRust: #386 — PtrMetadata has no meaningful swap target.
            if let Some(alt_op) = match op {
                UnOp::Not => Some(UnOp::Neg),
                UnOp::Neg => Some(UnOp::Not),
                UnOp::PtrMetadata => None,
                _ => None,
            } {
                mutants.push(MirMutant {
                    block_idx,
                    stmt_idx,
                    mutation_type: MutationType::ConditionNegation,
                    original_desc: format!("{op:?}"),
                    mutated_desc: format!("{alt_op:?}"),
                    mutated_stmt: Statement::Assign {
                        place: place.clone(),
                        rvalue: Rvalue::UnaryOp(alt_op, operand.clone()),
                        span: span.clone(),
                    },
                    result: MutationResult::Survived,
                });
            }

            // Remove unary: replace with identity
            mutants.push(MirMutant {
                block_idx,
                stmt_idx,
                mutation_type: MutationType::ConditionNegation,
                original_desc: format!("{op:?}(operand)"),
                mutated_desc: "operand".into(),
                mutated_stmt: Statement::Assign {
                    place: place.clone(),
                    rvalue: Rvalue::Use(operand.clone()),
                    span: span.clone(),
                },
                result: MutationResult::Survived,
            });
        }

        Rvalue::Use(Operand::Constant(cv)) => {
            // Boundary shift for constants
            for mutated_cv in shift_constant(cv) {
                mutants.push(MirMutant {
                    block_idx,
                    stmt_idx,
                    mutation_type: MutationType::BoundaryShift,
                    original_desc: format!("{cv:?}"),
                    mutated_desc: format!("{mutated_cv:?}"),
                    mutated_stmt: Statement::Assign {
                        place: place.clone(),
                        rvalue: Rvalue::Use(Operand::Constant(mutated_cv)),
                        span: span.clone(),
                    },
                    result: MutationResult::Survived,
                });
            }
        }

        _ => {}
    }
}

/// Return alternative operators for a given BinOp.
pub(super) fn alternative_ops(op: BinOp) -> Vec<BinOp> {
    match op {
        BinOp::Add => vec![BinOp::Sub, BinOp::Mul],
        BinOp::Sub => vec![BinOp::Add],
        BinOp::Mul => vec![BinOp::Div, BinOp::Add],
        BinOp::Div => vec![BinOp::Mul],
        BinOp::Rem => vec![BinOp::Div],
        BinOp::Eq => vec![BinOp::Ne],
        BinOp::Ne => vec![BinOp::Eq],
        BinOp::Lt => vec![BinOp::Le, BinOp::Ge],
        BinOp::Le => vec![BinOp::Lt, BinOp::Gt],
        BinOp::Gt => vec![BinOp::Ge, BinOp::Le],
        BinOp::Ge => vec![BinOp::Gt, BinOp::Lt],
        BinOp::BitAnd => vec![BinOp::BitOr],
        BinOp::BitOr => vec![BinOp::BitAnd],
        BinOp::BitXor => vec![BinOp::BitAnd, BinOp::BitOr],
        BinOp::Shl => vec![BinOp::Shr],
        BinOp::Shr => vec![BinOp::Shl],
        // tRust #383: Cmp is three-way comparison; no simple mutation alternative.
        BinOp::Cmp => vec![],
        _ => vec![],
    }
}

/// Generate shifted constant values for boundary mutation.
pub(super) fn shift_constant(cv: &ConstValue) -> Vec<ConstValue> {
    match cv {
        ConstValue::Int(n) => {
            let mut results = vec![ConstValue::Int(n.wrapping_add(1))];
            if *n > 0 {
                results.push(ConstValue::Int(n - 1));
            }
            if *n != 0 {
                results.push(ConstValue::Int(0));
            }
            results
        }
        ConstValue::Uint(n, w) => {
            let mut results = vec![ConstValue::Uint(n.wrapping_add(1), *w)];
            if *n > 0 {
                results.push(ConstValue::Uint(n - 1, *w));
            }
            if *n != 0 {
                results.push(ConstValue::Uint(0, *w));
            }
            results
        }
        ConstValue::Bool(b) => vec![ConstValue::Bool(!b)],
        _ => vec![],
    }
}

/// Calculate the mutation score for MIR-level mutants.
#[must_use]
pub fn mir_mutation_score(mutants: &[MirMutant]) -> f64 {
    if mutants.is_empty() {
        return 1.0;
    }
    let killed = mutants.iter().filter(|m| m.result.is_killed()).count();
    killed as f64 / mutants.len() as f64
}

// ---------------------------------------------------------------------------
// BinOp helper trait extensions
// ---------------------------------------------------------------------------

pub(super) trait BinOpExt {
    fn is_arithmetic(&self) -> bool;
    fn is_comparison(&self) -> bool;
    fn is_commutative(&self) -> bool;
}

impl BinOpExt for BinOp {
    fn is_arithmetic(&self) -> bool {
        matches!(
            self,
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem
        )
    }

    fn is_comparison(&self) -> bool {
        matches!(
            self,
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
        )
    }

    fn is_commutative(&self) -> bool {
        matches!(
            self,
            BinOp::Add
                | BinOp::Mul
                | BinOp::Eq
                | BinOp::Ne
                | BinOp::BitAnd
                | BinOp::BitOr
                | BinOp::BitXor
        )
    }
}
