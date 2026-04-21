// Counterexample-guided invariant inference.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::*;

use crate::loop_analysis::LoopInfo;

use super::{InvariantCandidate, InvariantPattern};

/// A counterexample: a mapping from variable names to concrete values.
pub(crate) type Counterexample = FxHashMap<String, i128>;

/// Infer invariant candidates from a counterexample.
///
/// Given variable values from a counterexample trace, generates candidate
/// invariants by observing patterns:
/// - For each unsigned variable with non-negative value: `var >= 0`
/// - For induction variables with init/bound: `init <= var` and `var <= bound`
/// - For pairs of variables: ordering relationships `var1 <= var2`
#[must_use]
pub(crate) fn infer_from_counterexample(
    cex: &Counterexample,
    loop_info: &LoopInfo,
    func: &VerifiableFunction,
) -> Vec<InvariantCandidate> {
    let mut candidates = Vec::new();

    // Non-negativity for unsigned variables.
    for (name, value) in cex {
        if *value >= 0 {
            let is_unsigned = func.body.locals.iter().any(|d| {
                d.name.as_deref() == Some(name) && d.ty.is_integer() && !d.ty.is_signed()
            });
            if is_unsigned {
                candidates.push(InvariantCandidate {
                    expression: Formula::Ge(
                        Box::new(Formula::Var(name.clone(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    confidence: 0.50,
                    pattern: InvariantPattern::CounterLoop,
                    loop_header: loop_info.header,
                });
            }
        }
    }

    // Induction variable bounds from CEX.
    for ivar in &loop_info.induction_vars {
        let Some(ivar_val) = cex.get(&ivar.name) else { continue };

        if let Some(Formula::Int(init_val)) = &ivar.init
            && *ivar_val >= *init_val {
                candidates.push(InvariantCandidate {
                    expression: Formula::Le(
                        Box::new(Formula::Int(*init_val)),
                        Box::new(Formula::Var(ivar.name.clone(), Sort::Int)),
                    ),
                    confidence: 0.55,
                    pattern: InvariantPattern::CounterLoop,
                    loop_header: loop_info.header,
                });
            }

        if let Some(Formula::Var(bound_name, _)) = &ivar.bound
            && let Some(bound_val) = cex.get(bound_name)
                && *ivar_val <= *bound_val {
                    candidates.push(InvariantCandidate {
                        expression: Formula::Le(
                            Box::new(Formula::Var(ivar.name.clone(), Sort::Int)),
                            Box::new(Formula::Var(bound_name.clone(), Sort::Int)),
                        ),
                        confidence: 0.55,
                        pattern: InvariantPattern::CounterLoop,
                        loop_header: loop_info.header,
                    });
                }
    }

    // Pairwise variable ordering from CEX values.
    let mut vars: Vec<(&String, &i128)> = cex.iter().collect();
    vars.sort_by_key(|&(name, _)| name.clone());
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            let (name_a, val_a) = vars[i];
            let (name_b, val_b) = vars[j];
            if val_a <= val_b {
                candidates.push(InvariantCandidate {
                    expression: Formula::Le(
                        Box::new(Formula::Var(name_a.clone(), Sort::Int)),
                        Box::new(Formula::Var(name_b.clone(), Sort::Int)),
                    ),
                    confidence: 0.40,
                    pattern: InvariantPattern::CounterLoop,
                    loop_header: loop_info.header,
                });
            }
            if val_b <= val_a {
                candidates.push(InvariantCandidate {
                    expression: Formula::Le(
                        Box::new(Formula::Var(name_b.clone(), Sort::Int)),
                        Box::new(Formula::Var(name_a.clone(), Sort::Int)),
                    ),
                    confidence: 0.40,
                    pattern: InvariantPattern::CounterLoop,
                    loop_header: loop_info.header,
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
