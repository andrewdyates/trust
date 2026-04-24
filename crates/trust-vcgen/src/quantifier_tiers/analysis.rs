// trust-vcgen/quantifier_tiers/analysis.rs: Pre-processing pass (#183)
//
// Classification, skolemization, instantiation, simplification,
// and quantifier analysis.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort};

use super::eliminator::{apply_tier_strategy, has_quantifiers};
use super::finite_domain::substitute;
use super::presburger::free_vars;
use super::types::{QuantifierConfig, QuantifierStats, QuantifierTier, SolverStrategy};

/// Analyze the quantifier structure of a formula.
///
/// Counts forall/exists quantifiers, computes maximum nesting depth,
/// and detects quantifier alternation (a forall nested under an exists
/// or vice versa).
#[must_use]
pub fn analyze_quantifiers(formula: &Formula) -> QuantifierStats {
    let mut stats = QuantifierStats::default();
    analyze_quantifiers_rec(formula, 0, None, &mut stats);
    stats
}

/// Quantifier polarity for alternation detection.
#[derive(Clone, Copy, PartialEq, Eq)]
enum QPolarity {
    Forall,
    Exists,
}

fn analyze_quantifiers_rec(
    formula: &Formula,
    depth: usize,
    parent_polarity: Option<QPolarity>,
    stats: &mut QuantifierStats,
) {
    match formula {
        Formula::Forall(_, body) => {
            stats.num_forall += 1;
            let new_depth = depth + 1;
            if new_depth > stats.max_nesting_depth {
                stats.max_nesting_depth = new_depth;
            }
            if parent_polarity == Some(QPolarity::Exists) {
                stats.has_alternation = true;
            }
            analyze_quantifiers_rec(body, new_depth, Some(QPolarity::Forall), stats);
        }
        Formula::Exists(_, body) => {
            stats.num_exists += 1;
            let new_depth = depth + 1;
            if new_depth > stats.max_nesting_depth {
                stats.max_nesting_depth = new_depth;
            }
            if parent_polarity == Some(QPolarity::Forall) {
                stats.has_alternation = true;
            }
            analyze_quantifiers_rec(body, new_depth, Some(QPolarity::Exists), stats);
        }
        _ => {
            for child in formula.children() {
                analyze_quantifiers_rec(child, depth, parent_polarity, stats);
            }
        }
    }
}

/// Classify the quantifier structure of a formula into a tier.
///
/// This is a standalone top-level function (unlike `QuantifierEliminator::classify`
/// which requires bindings). Walks the formula to determine the overall tier:
/// - `QuantifierFree`: no quantifiers present
/// - `FiniteUnrolling`: all quantifiers range over finite, statically-known domains
/// - `DecidableArithmetic`: all quantifiers are in Presburger arithmetic (LIA)
/// - `Full`: at least one quantifier is in a non-decidable fragment
#[must_use]
pub fn classify_quantifiers(formula: &Formula) -> QuantifierTier {
    if !has_quantifiers(formula) {
        return QuantifierTier::QuantifierFree;
    }
    let config = QuantifierConfig::default();
    let strategy = apply_tier_strategy(formula, &config);
    match strategy {
        SolverStrategy::QuantifierFree => QuantifierTier::QuantifierFree,
        SolverStrategy::Unroll => QuantifierTier::FiniteUnrolling,
        SolverStrategy::DecidableTheory => QuantifierTier::DecidableArithmetic,
        SolverStrategy::FullQuantifier => QuantifierTier::Full,
    }
}

/// Skolemize a formula: eliminate existential quantifiers by replacing
/// bound variables with Skolem function applications.
///
/// For an existential `exists x. P(x)` appearing under universal quantifiers
/// `forall y1, ..., yn`, the bound variable `x` is replaced with a fresh
/// Skolem function `skolem_x(y1, ..., yn)`. If there are no enclosing
/// universals, a Skolem constant `skolem_x` is introduced.
///
/// This is sound for satisfiability: `exists x. P(x)` is satisfiable iff
/// `P(skolem_x)` is satisfiable (for the appropriate Skolem function).
#[must_use]
pub fn skolemize(formula: &Formula) -> Formula {
    let mut counter = 0;
    skolemize_rec(formula, &[], &mut counter)
}

fn skolemize_rec(
    formula: &Formula,
    enclosing_universals: &[(trust_types::Symbol, Sort)],
    counter: &mut usize,
) -> Formula {
    match formula {
        Formula::Forall(bindings, body) => {
            // Accumulate universal bindings for Skolem function arguments.
            let mut extended = enclosing_universals.to_vec();
            extended.extend(bindings.iter().cloned());
            let new_body = skolemize_rec(body, &extended, counter);
            Formula::Forall(bindings.clone(), Box::new(new_body))
        }
        Formula::Exists(bindings, body) => {
            // Replace each existentially bound variable with a Skolem term.
            let mut current_body = *body.clone();
            for (var_name, var_sort) in bindings {
                *counter += 1;
                let skolem_name = format!("skolem_{var_name}_{}", *counter);
                let skolem_term = if enclosing_universals.is_empty() {
                    // Skolem constant.
                    Formula::Var(skolem_name, var_sort.clone())
                } else {
                    // Skolem function: we represent it as a fresh variable
                    // whose name encodes the dependency on universals.
                    let arg_names: Vec<&str> =
                        enclosing_universals.iter().map(|(n, _)| n.as_str()).collect();
                    Formula::Var(
                        format!("{skolem_name}({})", arg_names.join(",")),
                        var_sort.clone(),
                    )
                };
                current_body = substitute(&current_body, var_name.as_str(), &skolem_term);
            }
            // Continue skolemizing in the (now existential-free) body.
            skolemize_rec(&current_body, enclosing_universals, counter)
        }
        // Recurse through connectives.
        Formula::Not(inner) => {
            Formula::Not(Box::new(skolemize_rec(inner, enclosing_universals, counter)))
        }
        Formula::And(cs) => Formula::And(
            cs.iter().map(|c| skolemize_rec(c, enclosing_universals, counter)).collect(),
        ),
        Formula::Or(cs) => Formula::Or(
            cs.iter().map(|c| skolemize_rec(c, enclosing_universals, counter)).collect(),
        ),
        Formula::Implies(a, b) => Formula::Implies(
            Box::new(skolemize_rec(a, enclosing_universals, counter)),
            Box::new(skolemize_rec(b, enclosing_universals, counter)),
        ),
        Formula::Ite(c, t, e) => Formula::Ite(
            Box::new(skolemize_rec(c, enclosing_universals, counter)),
            Box::new(skolemize_rec(t, enclosing_universals, counter)),
            Box::new(skolemize_rec(e, enclosing_universals, counter)),
        ),
        // Leaves and non-connective nodes pass through unchanged.
        other => other.clone(),
    }
}

/// Instantiate a universally quantified formula with concrete terms.
///
/// For `Forall([(x1, s1), (x2, s2), ...], body)`, substitutes each
/// bound variable `xi` with the corresponding term from `terms`.
/// If `terms` is shorter than the binding list, remaining variables
/// stay bound. If `terms` is longer, extra terms are ignored.
///
/// For non-`Forall` formulas, returns the formula unchanged.
#[must_use]
pub fn instantiate_universal(formula: &Formula, terms: &[Formula]) -> Formula {
    match formula {
        Formula::Forall(bindings, body) => {
            let mut result = *body.clone();
            let instantiation_count = bindings.len().min(terms.len());

            for i in 0..instantiation_count {
                result = substitute(&result, bindings[i].0.as_str(), &terms[i]);
            }

            if instantiation_count < bindings.len() {
                // Some bindings remain -- rewrap with remaining quantifiers.
                Formula::Forall(bindings[instantiation_count..].to_vec(), Box::new(result))
            } else {
                result
            }
        }
        other => other.clone(),
    }
}

/// Simplify quantified formulas by removing vacuous quantifiers and
/// merging nested same-kind quantifiers.
///
/// Transformations applied (recursively, bottom-up):
/// 1. **Vacuous quantifier removal**: `forall x. P` where `x` is not free in `P`
///    becomes just `P`. Same for `exists x. P`.
/// 2. **Nested merge**: `forall x. forall y. P` becomes `forall x, y. P`.
///    Same for `exists x. exists y. P`.
/// 3. **Empty binding removal**: `forall(). P` becomes `P`.
#[must_use]
pub fn simplify_quantified(formula: &Formula) -> Formula {
    // Bottom-up: simplify children first, then simplify self.
    let simplified_children = match formula {
        Formula::Not(inner) => Formula::Not(Box::new(simplify_quantified(inner))),
        Formula::And(cs) => Formula::And(cs.iter().map(simplify_quantified).collect()),
        Formula::Or(cs) => Formula::Or(cs.iter().map(simplify_quantified).collect()),
        Formula::Implies(a, b) => {
            Formula::Implies(Box::new(simplify_quantified(a)), Box::new(simplify_quantified(b)))
        }
        Formula::Ite(c, t, e) => Formula::Ite(
            Box::new(simplify_quantified(c)),
            Box::new(simplify_quantified(t)),
            Box::new(simplify_quantified(e)),
        ),
        Formula::Eq(a, b) => {
            Formula::Eq(Box::new(simplify_quantified(a)), Box::new(simplify_quantified(b)))
        }
        Formula::Forall(bindings, body) => {
            Formula::Forall(bindings.clone(), Box::new(simplify_quantified(body)))
        }
        Formula::Exists(bindings, body) => {
            Formula::Exists(bindings.clone(), Box::new(simplify_quantified(body)))
        }
        other => other.clone(),
    };

    // Now apply quantifier-specific simplifications at this level.
    match &simplified_children {
        Formula::Forall(bindings, body) => simplify_forall(bindings, body),
        Formula::Exists(bindings, body) => simplify_exists(bindings, body),
        other => other.clone(),
    }
}

/// Simplify a `Forall` node after children are already simplified.
fn simplify_forall(bindings: &[(trust_types::Symbol, Sort)], body: &Formula) -> Formula {
    if bindings.is_empty() {
        return body.clone();
    }

    let body_free = free_vars(body);
    let non_vacuous: Vec<(trust_types::Symbol, Sort)> =
        bindings.iter().filter(|(name, _)| body_free.contains(name.as_str())).cloned().collect();

    if non_vacuous.is_empty() {
        return body.clone();
    }

    // Merge nested same-kind: forall x. forall y. P => forall x, y. P
    if let Formula::Forall(inner_bindings, inner_body) = body {
        let mut merged = non_vacuous;
        merged.extend(inner_bindings.iter().cloned());
        return Formula::Forall(merged, inner_body.clone());
    }

    if non_vacuous.len() == bindings.len() {
        Formula::Forall(bindings.to_vec(), Box::new(body.clone()))
    } else {
        Formula::Forall(non_vacuous, Box::new(body.clone()))
    }
}

/// Simplify an `Exists` node after children are already simplified.
fn simplify_exists(bindings: &[(trust_types::Symbol, Sort)], body: &Formula) -> Formula {
    if bindings.is_empty() {
        return body.clone();
    }

    let body_free = free_vars(body);
    let non_vacuous: Vec<(trust_types::Symbol, Sort)> =
        bindings.iter().filter(|(name, _)| body_free.contains(name.as_str())).cloned().collect();

    if non_vacuous.is_empty() {
        return body.clone();
    }

    // Merge nested same-kind: exists x. exists y. P => exists x, y. P
    if let Formula::Exists(inner_bindings, inner_body) = body {
        let mut merged = non_vacuous;
        merged.extend(inner_bindings.iter().cloned());
        return Formula::Exists(merged, inner_body.clone());
    }

    if non_vacuous.len() == bindings.len() {
        Formula::Exists(bindings.to_vec(), Box::new(body.clone()))
    } else {
        Formula::Exists(non_vacuous, Box::new(body.clone()))
    }
}
