// Pattern-based invariant inference strategies.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::loop_analysis::{InductionVar, LoopInfo, StepDirection};

use super::{InvariantCandidate, InvariantPattern};
use trust_types::fx::FxHashSet;

/// Counter loop: when we have init, step, and bound, generate `init <= var <= bound`.
pub(crate) fn infer_counter_loop(
    loop_info: &LoopInfo,
    ivar: &InductionVar,
) -> Vec<InvariantCandidate> {
    let mut candidates = Vec::new();
    let var = Formula::Var(ivar.name.clone(), Sort::Int);

    match (ivar.direction, &ivar.init, &ivar.bound) {
        // Ascending with both init and bound: init <= var <= bound
        (StepDirection::Ascending, Some(init), Some(bound)) => {
            let lower = Formula::Le(Box::new(init.clone()), Box::new(var.clone()));
            let upper = Formula::Le(Box::new(var), Box::new(bound.clone()));
            candidates.push(InvariantCandidate {
                expression: Formula::And(vec![lower, upper]),
                confidence: 0.90,
                pattern: InvariantPattern::CounterLoop,
                loop_header: loop_info.header,
            });
        }
        // Ascending with init only: init <= var
        (StepDirection::Ascending, Some(init), None) => {
            candidates.push(InvariantCandidate {
                expression: Formula::Le(Box::new(init.clone()), Box::new(var)),
                confidence: 0.75,
                pattern: InvariantPattern::CounterLoop,
                loop_header: loop_info.header,
            });
        }
        // Ascending with bound only: var <= bound
        (StepDirection::Ascending, None, Some(bound)) => {
            candidates.push(InvariantCandidate {
                expression: Formula::Le(Box::new(var), Box::new(bound.clone())),
                confidence: 0.70,
                pattern: InvariantPattern::CounterLoop,
                loop_header: loop_info.header,
            });
        }
        // Descending with bound: var >= bound
        (StepDirection::Descending, _, Some(bound)) => {
            candidates.push(InvariantCandidate {
                expression: Formula::Ge(Box::new(var), Box::new(bound.clone())),
                confidence: 0.85,
                pattern: InvariantPattern::CounterLoop,
                loop_header: loop_info.header,
            });
        }
        // Descending with no bound but unsigned type: var >= 0
        (StepDirection::Descending, _, None) => {
            candidates.push(InvariantCandidate {
                expression: Formula::Ge(Box::new(var), Box::new(Formula::Int(0))),
                confidence: 0.60,
                pattern: InvariantPattern::CounterLoop,
                loop_header: loop_info.header,
            });
        }
        _ => {}
    }

    candidates
}

/// Accumulator pattern: scan all variables in loop body assigned as
/// `var = var + expr` where `expr` is non-constant (accumulating a variable).
///
/// When the variable is unsigned, initialized to 0, and only added to,
/// generate `var >= 0`.
pub(crate) fn infer_accumulators(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Vec<InvariantCandidate> {
    let mut candidates = Vec::new();
    let mut seen = FxHashSet::default();

    for block_id in &loop_info.body_blocks {
        let Some(block) = func.body.blocks.get(block_id.0) else {
            continue;
        };
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                if !place.projections.is_empty() {
                    continue;
                }
                let local_idx = place.local;
                if seen.contains(&local_idx) {
                    continue;
                }
                let Some(decl) = func.body.locals.get(local_idx) else {
                    continue;
                };
                if !decl.ty.is_integer() || decl.ty.is_signed() {
                    continue;
                }

                // Check: var = var + other (non-constant operand)
                let is_accum = matches!(
                    rvalue,
                    Rvalue::BinaryOp(BinOp::Add, Operand::Copy(src), other)
                    | Rvalue::BinaryOp(BinOp::Add, other, Operand::Copy(src))
                        if src.local == local_idx
                            && src.projections.is_empty()
                            && !matches!(other, Operand::Constant(_))
                );

                if !is_accum {
                    continue;
                }

                // Check if initialized to 0 before the loop
                if !find_init_before_loop(func, loop_info, local_idx) {
                    continue;
                }

                seen.insert(local_idx);
                let var_name = decl
                    .name
                    .clone()
                    .unwrap_or_else(|| format!("_{local_idx}"));
                let var = Formula::Var(var_name, Sort::Int);
                candidates.push(InvariantCandidate {
                    expression: Formula::Ge(Box::new(var), Box::new(Formula::Int(0))),
                    confidence: 0.80,
                    pattern: InvariantPattern::Accumulator,
                    loop_header: loop_info.header,
                });
            }
        }
    }

    candidates
}

/// Check if a variable is initialized to 0 before the loop header.
fn find_init_before_loop(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    local_idx: usize,
) -> bool {
    for block in &func.body.blocks {
        if block.id.0 >= loop_info.header.0 {
            break;
        }
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt
                && place.local == local_idx && place.projections.is_empty()
                    && let Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64)))
                    | Rvalue::Use(Operand::Constant(ConstValue::Int(0))) = rvalue
                    {
                        return true;
                    }
        }
    }
    false
}

/// Array iteration pattern: detect index variable used with Projection::Index
/// and Rvalue::Len on the same array, generate `0 <= i < len`.
pub(crate) fn infer_array_iteration(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Vec<InvariantCandidate> {
    let mut candidates = Vec::new();

    for block_id in &loop_info.body_blocks {
        let Some(block) = func.body.blocks.get(block_id.0) else {
            continue;
        };
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt {
                for (idx_local, array_place) in extract_index_accesses(rvalue) {
                    let Some(idx_decl) = func.body.locals.get(idx_local) else {
                        continue;
                    };
                    if !idx_decl.ty.is_integer() {
                        continue;
                    }

                    let idx_name = idx_decl
                        .name
                        .clone()
                        .unwrap_or_else(|| format!("_{idx_local}"));

                    if let Some(len_var) = find_len_variable(func, &array_place) {
                        let idx = Formula::Var(idx_name.clone(), Sort::Int);
                        // 0 <= i AND i < len
                        let lower = Formula::Le(Box::new(Formula::Int(0)), Box::new(idx.clone()));
                        let upper = Formula::Lt(
                            Box::new(idx),
                            Box::new(Formula::Var(len_var, Sort::Int)),
                        );
                        candidates.push(InvariantCandidate {
                            expression: Formula::And(vec![lower, upper]),
                            confidence: 0.92,
                            pattern: InvariantPattern::ArrayIteration,
                            loop_header: loop_info.header,
                        });
                    }
                }
            }
        }
    }

    candidates
}

/// Binary search pattern: detect `low` and `high` variables where the loop
/// condition is `low < high` (or `low <= high`), generate `low <= high`.
///
/// Heuristic: look for two induction variables where one is named "low"/"left"/"lo"
/// and the other "high"/"right"/"hi", or where the header comparison involves
/// two induction variables compared with Lt/Le.
pub(crate) fn infer_binary_search(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Vec<InvariantCandidate> {
    let mut candidates = Vec::new();
    let header_block = match func.body.blocks.get(loop_info.header.0) {
        Some(bb) => bb,
        None => return candidates,
    };

    // Look for a comparison between two locals in the header
    for stmt in &header_block.stmts {
        if let Statement::Assign { rvalue, .. } = stmt {
            let (lhs_local, rhs_local) = match rvalue {
                Rvalue::BinaryOp(BinOp::Lt | BinOp::Le, Operand::Copy(lhs), Operand::Copy(rhs)) => {
                    (lhs.local, rhs.local)
                }
                _ => continue,
            };

            // Both must be induction variables (or at least integer locals)
            let lhs_is_ivar = loop_info.induction_vars.iter().any(|v| v.local_idx == lhs_local);
            let rhs_name = func
                .body
                .locals
                .get(rhs_local)
                .and_then(|d| d.name.as_deref());

            // Check for binary search naming pattern
            let lhs_name = func
                .body
                .locals
                .get(lhs_local)
                .and_then(|d| d.name.as_deref());
            let is_binary_search_pattern = matches!(
                (lhs_name, rhs_name),
                (Some("low"), Some("high"))
                    | (Some("lo"), Some("hi"))
                    | (Some("left"), Some("right"))
                    | (Some("l"), Some("r"))
            );

            // Also consider: two different variables compared, at least one is an ivar,
            // and the loop body modifies both
            let rhs_is_ivar = loop_info.induction_vars.iter().any(|v| v.local_idx == rhs_local);
            let is_two_ivar_search = lhs_is_ivar && rhs_is_ivar && lhs_local != rhs_local;

            if is_binary_search_pattern || is_two_ivar_search {
                let lhs_var_name = func
                    .body
                    .locals
                    .get(lhs_local)
                    .and_then(|d| d.name.clone())
                    .unwrap_or_else(|| format!("_{lhs_local}"));
                let rhs_var_name = func
                    .body
                    .locals
                    .get(rhs_local)
                    .and_then(|d| d.name.clone())
                    .unwrap_or_else(|| format!("_{rhs_local}"));

                // Invariant: low <= high (maintains search space validity)
                let lhs = Formula::Var(lhs_var_name, Sort::Int);
                let rhs = Formula::Var(rhs_var_name, Sort::Int);
                let confidence = if is_binary_search_pattern { 0.88 } else { 0.65 };

                candidates.push(InvariantCandidate {
                    expression: Formula::Le(Box::new(lhs), Box::new(rhs)),
                    confidence,
                    pattern: InvariantPattern::BinarySearch,
                    loop_header: loop_info.header,
                });
            }
        }
    }

    candidates
}

/// Extract user-annotated invariants from contracts.
pub(crate) fn extract_user_invariants(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Vec<InvariantCandidate> {
    func.contracts
        .iter()
        .filter(|c| matches!(c.kind, ContractKind::Invariant))
        .map(|c| InvariantCandidate {
            expression: Formula::Var(c.body.clone(), Sort::Bool),
            confidence: 1.0,
            pattern: InvariantPattern::UserAnnotated,
            loop_header: loop_info.header,
        })
        .collect()
}

// --- Helpers ---

/// Extract (index_local, array_place) pairs from index accesses in an rvalue.
pub(super) fn extract_index_accesses(rvalue: &Rvalue) -> Vec<(usize, Place)> {
    let mut accesses = Vec::new();
    let operands: Vec<&Operand> = match rvalue {
        Rvalue::Use(op) => vec![op],
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => vec![a, b],
        Rvalue::UnaryOp(_, op) => vec![op],
        Rvalue::Cast(op, _) => vec![op],
        Rvalue::Aggregate(_, ops) => ops.iter().collect(),
        _ => vec![],
    };

    for op in operands {
        if let Operand::Copy(place) | Operand::Move(place) = op {
            for proj in &place.projections {
                if let Projection::Index(idx_local) = proj {
                    let array_place = Place {
                        local: place.local,
                        projections: place
                            .projections
                            .iter()
                            .filter(|p| !matches!(p, Projection::Index(_)))
                            .cloned()
                            .collect(),
                    };
                    accesses.push((*idx_local, array_place));
                }
            }
        }
    }

    accesses
}

/// Find a Len variable for a given array/slice place.
pub(super) fn find_len_variable(func: &VerifiableFunction, array_place: &Place) -> Option<String> {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign {
                place: dest,
                rvalue: Rvalue::Len(len_place),
                ..
            } = stmt
                && len_place.local == array_place.local {
                    let decl = func.body.locals.get(dest.local)?;
                    return Some(
                        decl.name
                            .clone()
                            .unwrap_or_else(|| format!("_{}", dest.local)),
                    );
                }
        }
    }
    None
}
