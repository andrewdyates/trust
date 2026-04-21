// Abstract interpretation bridge: fixpoint-based invariant inference.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;

use trust_types::*;

use crate::abstract_interp::{self, AbstractDomain, Interval, IntervalDomain};

use super::{InvariantCandidate, InvariantPattern};

/// Infer loop invariants using abstract interpretation (interval domain).
///
/// Runs the fixpoint computation from `abstract_interp` and extracts
/// interval-based invariants at loop headers.
#[must_use]
pub(crate) fn infer_invariant_abstract(
    func: &VerifiableFunction,
) -> Vec<InvariantCandidate> {
    let mut initial = IntervalDomain::top();
    for (idx, decl) in func.body.locals.iter().enumerate() {
        if idx == 0 || idx > func.body.arg_count {
            continue;
        }
        if decl.ty.is_integer() && !decl.ty.is_signed() {
            let name = decl
                .name
                .clone()
                .unwrap_or_else(|| format!("_{idx}"));
            initial.set(name, Interval::new(0, i128::MAX));
        }
    }

    let result = abstract_interp::fixpoint(func, initial);
    let widen_points: FxHashSet<BlockId> = abstract_interp::detect_widen_points(func)
        .into_iter()
        .map(|wp| wp.block)
        .collect();

    let mut candidates = Vec::new();

    for block_id in &widen_points {
        let Some(state) = result.block_states.get(block_id) else {
            continue;
        };
        if state.is_unreachable {
            continue;
        }

        for (var_name, interval) in &state.vars {
            if interval.is_bottom() {
                continue;
            }

            if interval.lo != i128::MIN && interval.lo >= 0 {
                candidates.push(InvariantCandidate {
                    expression: Formula::Ge(
                        Box::new(Formula::Var(var_name.clone(), Sort::Int)),
                        Box::new(Formula::Int(interval.lo)),
                    ),
                    confidence: 0.70,
                    pattern: InvariantPattern::CounterLoop,
                    loop_header: *block_id,
                });
            }

            if interval.hi != i128::MAX {
                candidates.push(InvariantCandidate {
                    expression: Formula::Le(
                        Box::new(Formula::Var(var_name.clone(), Sort::Int)),
                        Box::new(Formula::Int(interval.hi)),
                    ),
                    confidence: 0.70,
                    pattern: InvariantPattern::CounterLoop,
                    loop_header: *block_id,
                });
            }
        }
    }

    candidates.sort_by(|a, b| {
        b.confidence
            .partial_cmp(&a.confidence)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    candidates
}
