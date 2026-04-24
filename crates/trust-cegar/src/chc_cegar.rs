// tRust: CHC/Spacer integration with the CEGAR refinement loop
//
// Uses CHC-derived loop invariants as refinement predicates in the CEGAR loop.
// When a counterexample involves a loop, we:
// 1. Encode the loop as a CHC system
// 2. Invoke Spacer to find an invariant
// 3. If found, add the invariant predicates to the CEGAR predicate set
// 4. If Spacer times out, fall back to bounded loop unrolling
//
// This bridges the gap between CEGAR (predicate refinement) and
// CHC solving (invariant synthesis), combining the strengths of both.
//
// Reference: Bjorner, Gurfinkel, "Horn-clause solvers" (2015)
// Reference: refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort};

use crate::chc::{ChcSystem, LoopEncoding, encode_loop};
use crate::error::CegarError;
use crate::invariant_extract::{LoopInvariant, extract_invariants};
use crate::predicate::Predicate;
use crate::spacer::{SpacerConfig, SpacerResult, chc_to_smtlib2, parse_spacer_response};

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Strategy for handling loops in the CEGAR loop.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
#[derive(Default)]
pub enum LoopStrategy {
    /// Use CHC/Spacer to infer invariants. Fall back to bounded unrolling on timeout.
    #[default]
    ChcWithFallback,
    /// Only use CHC/Spacer (fail if Spacer times out).
    ChcOnly,
    /// Only use bounded unrolling (no Spacer invocation).
    BoundedUnrolling { depth: usize },
}

/// Configuration for CHC-CEGAR integration.
#[derive(Debug, Clone)]
pub struct ChcCegarConfig {
    /// Strategy for handling loops.
    pub loop_strategy: LoopStrategy,
    /// Spacer engine configuration.
    pub spacer_config: SpacerConfig,
    /// Bounded unrolling depth for the fallback.
    pub fallback_unroll_depth: usize,
}

impl Default for ChcCegarConfig {
    fn default() -> Self {
        Self {
            loop_strategy: LoopStrategy::ChcWithFallback,
            spacer_config: SpacerConfig::default(),
            fallback_unroll_depth: 10,
        }
    }
}

// ---------------------------------------------------------------------------
// CHC-CEGAR integration
// ---------------------------------------------------------------------------

/// Result of attempting to refine the CEGAR loop using CHC/Spacer.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ChcRefinementResult {
    /// Spacer found an invariant. Contains the new predicates and the invariant.
    InvariantFound {
        /// New predicates to add to the CEGAR loop.
        new_predicates: Vec<Predicate>,
        /// The full loop invariant.
        invariant: LoopInvariant,
    },
    /// Spacer proved the property is violated (CHC system is unsatisfiable).
    PropertyViolated,
    /// Spacer timed out or returned unknown. Caller should fall back.
    Timeout { reason: String },
    /// Fell back to bounded unrolling.
    BoundedFallback {
        /// The unrolling depth used.
        depth: usize,
        /// Unrolled formula.
        unrolled_formula: Formula,
    },
}

/// Attempt to infer a loop invariant using CHC/Spacer and integrate
/// the result into the CEGAR predicate set.
///
/// # Arguments
/// * `encoding` - The loop structure to encode.
/// * `config` - CHC-CEGAR configuration.
/// * `solver_output` - If provided, use this as the Spacer output (for testing).
///   If None, generates the SMT-LIB2 script for external invocation.
///
/// # Returns
/// A `ChcRefinementResult` indicating what happened.
///
/// # Errors
/// Returns `CegarError` on encoding or parsing failures.
pub fn refine_with_chc(
    encoding: &LoopEncoding,
    config: &ChcCegarConfig,
    solver_output: Option<&str>,
) -> Result<ChcRefinementResult, CegarError> {
    match &config.loop_strategy {
        LoopStrategy::BoundedUnrolling { depth } => {
            let unrolled = bounded_unroll(encoding, *depth);
            Ok(ChcRefinementResult::BoundedFallback { depth: *depth, unrolled_formula: unrolled })
        }
        LoopStrategy::ChcOnly | LoopStrategy::ChcWithFallback => {
            // Encode the loop as a CHC system.
            let system = encode_loop(encoding)?;

            // If we have solver output, parse it. Otherwise, return the script.
            if let Some(output) = solver_output {
                let result = parse_spacer_response(output)?;
                return process_spacer_result(&result, encoding, config);
            }

            // Generate the script (caller will invoke the solver externally).
            let _script = chc_to_smtlib2(&system)?;
            // In a real integration, we'd invoke z4 here. For now, return Timeout
            // indicating the caller needs to invoke the solver.
            Ok(ChcRefinementResult::Timeout {
                reason: "solver not invoked (script generated)".to_string(),
            })
        }
    }
}

/// Process a Spacer result into a CEGAR refinement result.
fn process_spacer_result(
    result: &SpacerResult,
    encoding: &LoopEncoding,
    config: &ChcCegarConfig,
) -> Result<ChcRefinementResult, CegarError> {
    match result {
        SpacerResult::Sat { interpretations } => {
            // Build variable map from Spacer parameter names to original names.
            let variable_map: Vec<(String, String, Sort)> = encoding
                .variables
                .iter()
                .enumerate()
                .map(|(idx, (name, sort))| {
                    let spacer_name = format!("x!{idx}");
                    (spacer_name, name.clone(), sort.clone())
                })
                .collect();

            let invariants = extract_invariants(interpretations, &variable_map)?;

            if let Some(inv) = invariants.into_iter().next() {
                let new_predicates = inv.predicates.clone();
                Ok(ChcRefinementResult::InvariantFound { new_predicates, invariant: inv })
            } else {
                // Spacer returned sat but no interpretations.
                Ok(ChcRefinementResult::Timeout {
                    reason: "Spacer returned sat but no predicate interpretations".to_string(),
                })
            }
        }
        SpacerResult::Unsat => Ok(ChcRefinementResult::PropertyViolated),
        SpacerResult::Unknown { reason } => {
            if config.loop_strategy == LoopStrategy::ChcWithFallback {
                let unrolled = bounded_unroll(encoding, config.fallback_unroll_depth);
                Ok(ChcRefinementResult::BoundedFallback {
                    depth: config.fallback_unroll_depth,
                    unrolled_formula: unrolled,
                })
            } else {
                Ok(ChcRefinementResult::Timeout { reason: reason.clone() })
            }
        }
    }
}

/// Generate the SMT-LIB2 script for a loop's CHC system.
///
/// This is the entry point for callers that want to invoke z4 externally.
///
/// # Errors
/// Returns `CegarError` on encoding or generation failures.
pub fn generate_chc_script(encoding: &LoopEncoding) -> Result<String, CegarError> {
    let system = encode_loop(encoding)?;
    chc_to_smtlib2(&system)
}

/// Get the CHC system for a loop (for inspection/testing).
///
/// # Errors
/// Returns `CegarError` on encoding failures.
pub fn get_chc_system(encoding: &LoopEncoding) -> Result<ChcSystem, CegarError> {
    encode_loop(encoding)
}

// ---------------------------------------------------------------------------
// Bounded unrolling fallback
// ---------------------------------------------------------------------------

/// Bounded loop unrolling: replaces the loop with `depth` copies of the body.
///
/// Produces a formula: `pre /\ body_0 /\ body_1 /\ ... /\ body_{depth-1} /\ post`
/// where each body_i connects variables from step i to step i+1.
///
/// This is sound for bug-finding but not for verification (may miss bugs
/// beyond the unroll depth).
#[must_use]
pub fn bounded_unroll(encoding: &LoopEncoding, depth: usize) -> Formula {
    if depth == 0 {
        // Zero unrolling: just precondition /\ postcondition
        return Formula::And(vec![encoding.precondition.clone(), encoding.postcondition.clone()]);
    }

    let mut conjuncts = Vec::new();

    // Precondition over the initial variables.
    conjuncts.push(encoding.precondition.clone());

    // For each unrolling step, create a copy of the body constraint
    // with renamed variables (step_i -> step_{i+1}).
    for step in 0..depth {
        let step_constraint = rename_for_step(
            &encoding.body_constraint,
            &encoding.variables,
            &encoding.primed_variables,
            step,
        );
        conjuncts.push(step_constraint);
    }

    // Postcondition over the final-step variables.
    let final_post = rename_vars_with_step(&encoding.postcondition, &encoding.variables, depth);
    conjuncts.push(final_post);

    Formula::And(conjuncts)
}

/// Rename variables in a body constraint for a specific unrolling step.
///
/// Step 0: vars -> vars_0, primed -> vars_1
/// Step k: vars -> vars_k, primed -> vars_{k+1}
fn rename_for_step(
    formula: &Formula,
    variables: &[(String, Sort)],
    primed_variables: &[(String, Sort)],
    step: usize,
) -> Formula {
    let mut result = formula.clone();

    // Rename primed variables first (to avoid conflicts).
    for (primed_name, _) in primed_variables {
        let target = format!("{primed_name}__step_{}", step + 1);
        result = rename_var(&result, primed_name, &target);
    }

    // Rename original variables.
    for (var_name, _) in variables {
        let target = if step == 0 {
            var_name.clone() // Step 0 uses the original names
        } else {
            format!("{var_name}__step_{step}")
        };
        result = rename_var(&result, var_name, &target);
    }

    result
}

/// Rename variables in a formula to use step-specific names.
fn rename_vars_with_step(formula: &Formula, variables: &[(String, Sort)], step: usize) -> Formula {
    let mut result = formula.clone();
    for (var_name, _) in variables {
        if step == 0 {
            // No renaming needed for step 0.
            continue;
        }
        let target = format!("{var_name}__step_{step}");
        result = rename_var(&result, var_name, &target);
    }
    result
}

/// Rename a single variable in a formula.
fn rename_var(formula: &Formula, from: &str, to: &str) -> Formula {
    match formula {
        Formula::Var(name, sort) => {
            if name == from {
                Formula::Var(to.to_string(), sort.clone())
            } else {
                formula.clone()
            }
        }
        Formula::Not(inner) => Formula::Not(Box::new(rename_var(inner, from, to))),
        Formula::Neg(inner) => Formula::Neg(Box::new(rename_var(inner, from, to))),
        Formula::And(children) => {
            Formula::And(children.iter().map(|c| rename_var(c, from, to)).collect())
        }
        Formula::Or(children) => {
            Formula::Or(children.iter().map(|c| rename_var(c, from, to)).collect())
        }
        Formula::Implies(a, b) => {
            Formula::Implies(Box::new(rename_var(a, from, to)), Box::new(rename_var(b, from, to)))
        }
        Formula::Eq(a, b) => {
            Formula::Eq(Box::new(rename_var(a, from, to)), Box::new(rename_var(b, from, to)))
        }
        Formula::Lt(a, b) => {
            Formula::Lt(Box::new(rename_var(a, from, to)), Box::new(rename_var(b, from, to)))
        }
        Formula::Le(a, b) => {
            Formula::Le(Box::new(rename_var(a, from, to)), Box::new(rename_var(b, from, to)))
        }
        Formula::Gt(a, b) => {
            Formula::Gt(Box::new(rename_var(a, from, to)), Box::new(rename_var(b, from, to)))
        }
        Formula::Ge(a, b) => {
            Formula::Ge(Box::new(rename_var(a, from, to)), Box::new(rename_var(b, from, to)))
        }
        Formula::Add(a, b) => {
            Formula::Add(Box::new(rename_var(a, from, to)), Box::new(rename_var(b, from, to)))
        }
        Formula::Sub(a, b) => {
            Formula::Sub(Box::new(rename_var(a, from, to)), Box::new(rename_var(b, from, to)))
        }
        Formula::Mul(a, b) => {
            Formula::Mul(Box::new(rename_var(a, from, to)), Box::new(rename_var(b, from, to)))
        }
        Formula::Div(a, b) => {
            Formula::Div(Box::new(rename_var(a, from, to)), Box::new(rename_var(b, from, to)))
        }
        Formula::Rem(a, b) => {
            Formula::Rem(Box::new(rename_var(a, from, to)), Box::new(rename_var(b, from, to)))
        }
        Formula::Ite(c, t, e) => Formula::Ite(
            Box::new(rename_var(c, from, to)),
            Box::new(rename_var(t, from, to)),
            Box::new(rename_var(e, from, to)),
        ),
        // Literals: no renaming needed.
        _ => formula.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicate::CmpOp;

    fn counting_loop_encoding() -> LoopEncoding {
        LoopEncoding {
            invariant_name: "Inv_loop_0".into(),
            variables: vec![("x".into(), Sort::Int)],
            primed_variables: vec![("x_prime".into(), Sort::Int)],
            precondition: Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            body_constraint: Formula::And(vec![
                Formula::Lt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(10)),
                ),
                Formula::Eq(
                    Box::new(Formula::Var("x_prime".into(), Sort::Int)),
                    Box::new(Formula::Add(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(1)),
                    )),
                ),
            ]),
            exit_condition: Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
            postcondition: Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
        }
    }

    #[test]
    fn test_refine_with_chc_invariant_found() {
        let encoding = counting_loop_encoding();
        let config = ChcCegarConfig::default();

        // Simulate Spacer finding an invariant: 0 <= x <= 10
        let solver_output = r#"sat
(model
  (define-fun Inv_loop_0 ((x!0 Int)) Bool
    (and (>= x!0 0) (<= x!0 10)))
)"#;

        let result =
            refine_with_chc(&encoding, &config, Some(solver_output)).expect("should refine");

        match result {
            ChcRefinementResult::InvariantFound { new_predicates, invariant } => {
                assert_eq!(invariant.loop_name, "Inv_loop_0");
                assert!(!new_predicates.is_empty());
                // Should contain x >= 0 and x <= 10
                assert!(
                    new_predicates.iter().any(|p| *p == Predicate::comparison("x", CmpOp::Ge, "0"))
                );
                assert!(
                    new_predicates
                        .iter()
                        .any(|p| *p == Predicate::comparison("x", CmpOp::Le, "10"))
                );
            }
            other => panic!("expected InvariantFound, got: {:?}", other),
        }
    }

    #[test]
    fn test_refine_with_chc_property_violated() {
        let encoding = counting_loop_encoding();
        let config = ChcCegarConfig::default();

        let result =
            refine_with_chc(&encoding, &config, Some("unsat\n")).expect("should handle unsat");
        assert_eq!(result, ChcRefinementResult::PropertyViolated);
    }

    #[test]
    fn test_refine_with_chc_timeout_with_fallback() {
        let encoding = counting_loop_encoding();
        let config = ChcCegarConfig {
            loop_strategy: LoopStrategy::ChcWithFallback,
            fallback_unroll_depth: 5,
            ..Default::default()
        };

        let result = refine_with_chc(&encoding, &config, Some("unknown\ntimeout\n"))
            .expect("should fallback");

        match result {
            ChcRefinementResult::BoundedFallback { depth, .. } => {
                assert_eq!(depth, 5);
            }
            other => panic!("expected BoundedFallback, got: {:?}", other),
        }
    }

    #[test]
    fn test_refine_with_chc_timeout_chc_only() {
        let encoding = counting_loop_encoding();
        let config = ChcCegarConfig { loop_strategy: LoopStrategy::ChcOnly, ..Default::default() };

        let result = refine_with_chc(&encoding, &config, Some("unknown\ntimeout\n"))
            .expect("should timeout");

        match result {
            ChcRefinementResult::Timeout { reason } => {
                assert_eq!(reason, "timeout");
            }
            other => panic!("expected Timeout, got: {:?}", other),
        }
    }

    #[test]
    fn test_refine_with_chc_bounded_only() {
        let encoding = counting_loop_encoding();
        let config = ChcCegarConfig {
            loop_strategy: LoopStrategy::BoundedUnrolling { depth: 3 },
            ..Default::default()
        };

        let result = refine_with_chc(&encoding, &config, None).expect("should unroll");

        match result {
            ChcRefinementResult::BoundedFallback { depth, .. } => {
                assert_eq!(depth, 3);
            }
            other => panic!("expected BoundedFallback, got: {:?}", other),
        }
    }

    #[test]
    fn test_generate_chc_script() {
        let encoding = counting_loop_encoding();
        let script = generate_chc_script(&encoding).expect("should generate");
        assert!(script.contains("(set-logic HORN)"));
        assert!(script.contains("Inv_loop_0"));
        assert!(script.contains("(check-sat)"));
    }

    #[test]
    fn test_get_chc_system() {
        let encoding = counting_loop_encoding();
        let system = get_chc_system(&encoding).expect("should get system");
        assert_eq!(system.num_predicates(), 1);
        assert_eq!(system.num_clauses(), 3);
    }

    #[test]
    fn test_bounded_unroll_zero_depth() {
        let encoding = counting_loop_encoding();
        let formula = bounded_unroll(&encoding, 0);
        match formula {
            Formula::And(parts) => {
                assert_eq!(parts.len(), 2); // pre + post
            }
            other => panic!("expected And, got: {:?}", other),
        }
    }

    #[test]
    fn test_bounded_unroll_one_step() {
        let encoding = counting_loop_encoding();
        let formula = bounded_unroll(&encoding, 1);
        match formula {
            Formula::And(parts) => {
                assert_eq!(parts.len(), 3); // pre + 1 body + post
            }
            other => panic!("expected And, got: {:?}", other),
        }
    }

    #[test]
    fn test_bounded_unroll_three_steps() {
        let encoding = counting_loop_encoding();
        let formula = bounded_unroll(&encoding, 3);
        match formula {
            Formula::And(parts) => {
                assert_eq!(parts.len(), 5); // pre + 3 body + post
            }
            other => panic!("expected And, got: {:?}", other),
        }
    }

    #[test]
    fn test_rename_var_basic() {
        let formula = Formula::Var("x".into(), Sort::Int);
        let renamed = rename_var(&formula, "x", "y");
        assert_eq!(renamed, Formula::Var("y".into(), Sort::Int));
    }

    #[test]
    fn test_rename_var_no_match() {
        let formula = Formula::Var("z".into(), Sort::Int);
        let renamed = rename_var(&formula, "x", "y");
        assert_eq!(renamed, Formula::Var("z".into(), Sort::Int));
    }

    #[test]
    fn test_rename_var_in_comparison() {
        let formula =
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10)));
        let renamed = rename_var(&formula, "x", "x__step_1");
        assert_eq!(
            renamed,
            Formula::Lt(
                Box::new(Formula::Var("x__step_1".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            )
        );
    }

    #[test]
    fn test_chc_cegar_config_default() {
        let config = ChcCegarConfig::default();
        assert_eq!(config.loop_strategy, LoopStrategy::ChcWithFallback);
        assert_eq!(config.fallback_unroll_depth, 10);
    }

    #[test]
    fn test_loop_strategy_default() {
        assert_eq!(LoopStrategy::default(), LoopStrategy::ChcWithFallback);
    }

    #[test]
    fn test_refine_with_chc_no_solver_output() {
        let encoding = counting_loop_encoding();
        let config = ChcCegarConfig::default();

        let result = refine_with_chc(&encoding, &config, None).expect("should return timeout");
        match result {
            ChcRefinementResult::Timeout { reason } => {
                assert!(reason.contains("not invoked"));
            }
            other => panic!("expected Timeout, got: {:?}", other),
        }
    }
}
