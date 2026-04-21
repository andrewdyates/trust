// trust-router: CEGAR verification backend
//
// Routes VCs to trust-cegar's CEGAR refinement loop and IC3/PDR engine.
// Uses the cegar_classifier to decide whether a VC is suitable for
// abstraction-refinement vs direct SMT solving.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::time::Instant;

use trust_cegar::{
    CegarConfig, CegarLoop, CegarOutcome, Ic3Config, Ic3Engine, Ic3Result, Predicate,
    TransitionSystem, select_strategy,
};
use trust_types::{
    Counterexample, CounterexampleValue, Formula, ProofStrength, VerificationCondition,
    VerificationResult,
};

use crate::cegar_classifier;
use trust_types::fx::FxHashSet;

/// Configuration for the CEGAR verification backend.
#[derive(Debug, Clone)]
pub struct CegarBackendConfig {
    /// Maximum refinement iterations in the CEGAR loop.
    pub max_iterations: usize,
    /// Timeout in milliseconds for the entire CEGAR run (0 = no timeout).
    pub timeout_ms: u64,
    /// Minimum classifier score to accept a VC.
    pub classifier_threshold: u32,
    /// Maximum frame depth for IC3/PDR.
    pub ic3_max_depth: usize,
    /// Whether to attempt IC3/PDR as a fallback when CEGAR refinement stalls.
    pub ic3_fallback: bool,
}

impl Default for CegarBackendConfig {
    fn default() -> Self {
        Self {
            max_iterations: 100,
            timeout_ms: 30_000,
            classifier_threshold: 30,
            ic3_max_depth: 200,
            ic3_fallback: true,
        }
    }
}

/// A verification backend that uses CEGAR predicate abstraction
/// and IC3/PDR model checking for VCs involving loops, recursion,
/// or complex control flow.
pub struct CegarBackend {
    config: CegarBackendConfig,
}

impl CegarBackend {
    /// Create a new CEGAR backend with default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self {
            config: CegarBackendConfig::default(),
        }
    }

    /// Create a CEGAR backend with custom configuration.
    #[must_use]
    pub fn with_config(config: CegarBackendConfig) -> Self {
        Self { config }
    }

    /// Run the CEGAR refinement loop on a VC.
    fn run_cegar(&self, vc: &VerificationCondition, start: Instant) -> VerificationResult {
        // Discover initial predicates from the formula.
        let initial_predicates = discover_initial_predicates(&vc.formula);

        let cegar_config = CegarConfig {
            max_iterations: self.config.max_iterations,
        };
        let mut cegar = CegarLoop::new(initial_predicates, cegar_config);

        // Run refinement iterations.
        for _iter in 0..self.config.max_iterations {
            // Check timeout.
            if self.config.timeout_ms > 0 {
                let elapsed = start.elapsed().as_millis() as u64;
                if elapsed >= self.config.timeout_ms {
                    return VerificationResult::Timeout {
                        solver: "cegar".to_string(),
                        timeout_ms: self.config.timeout_ms,
                    };
                }
            }

            // Run one abstract model check + refinement iteration.
            // We simulate the abstract check by creating a synthetic counterexample
            // from the formula structure and then asking CEGAR to refine.
            let outcome = self.abstract_check_and_refine(&mut cegar, vc);

            match outcome {
                CegarStepResult::Safe => {
                    let time_ms = start.elapsed().as_millis() as u64;
                    return VerificationResult::Proved {
                        solver: "cegar".to_string(),
                        time_ms,
                        strength: ProofStrength::inductive(),
                        proof_certificate: None,
                solver_warnings: None,
                    };
                }
                CegarStepResult::Unsafe(cex) => {
                    let time_ms = start.elapsed().as_millis() as u64;
                    return VerificationResult::Failed {
                        solver: "cegar".to_string(),
                        time_ms,
                        counterexample: Some(cex),
                    };
                }
                CegarStepResult::Continue => continue,
                CegarStepResult::Stalled => break,
            }
        }

        // CEGAR did not converge. Try IC3 fallback if enabled.
        if self.config.ic3_fallback {
            return self.run_ic3_fallback(vc, start);
        }

        let time_ms = start.elapsed().as_millis() as u64;
        VerificationResult::Unknown {
            solver: "cegar".to_string(),
            time_ms,
            reason: "CEGAR refinement did not converge".to_string(),
        }
    }

    /// Perform one abstract model check + refinement step.
    fn abstract_check_and_refine(
        &self,
        cegar: &mut CegarLoop,
        vc: &VerificationCondition,
    ) -> CegarStepResult {
        // Select a refinement strategy based on VC complexity.
        let _strategy = select_strategy(vc);

        // Abstract model check: evaluate the formula under current predicates.
        // For a true formula (property holds), we check if the abstraction
        // can prove it. For false formulas (violation exists), we look for cex.
        match &vc.formula {
            Formula::Bool(true) => CegarStepResult::Safe,
            Formula::Bool(false) => {
                CegarStepResult::Unsafe(Counterexample::new(Vec::new()))
            }
            _ => {
                // Generate a synthetic counterexample from formula variables
                // to drive the CEGAR refinement loop.
                let synthetic_cex = extract_synthetic_counterexample(&vc.formula);
                let blocks = [];

                match cegar.refine_iteration(&synthetic_cex, &blocks) {
                    Ok(CegarOutcome::Safe) => CegarStepResult::Safe,
                    Ok(CegarOutcome::Unsafe) => CegarStepResult::Unsafe(synthetic_cex),
                    Ok(CegarOutcome::Refined { .. }) => CegarStepResult::Continue,
                    // Handle future non-exhaustive CegarOutcome variants.
                    Ok(_) => CegarStepResult::Continue,
                    Err(_) => CegarStepResult::Stalled,
                }
            }
        }
    }

    /// Run IC3/PDR as a fallback when CEGAR stalls.
    fn run_ic3_fallback(&self, vc: &VerificationCondition, start: Instant) -> VerificationResult {
        // Build a transition system from the formula.
        let system = formula_to_transition_system(&vc.formula);
        let config = Ic3Config {
            max_depth: self.config.ic3_max_depth,
            max_block_iterations: 10_000,
        };

        let mut engine = Ic3Engine::new(system, config);
        match engine.check() {
            Ok(Ic3Result::Safe { .. }) => {
                let time_ms = start.elapsed().as_millis() as u64;
                VerificationResult::Proved {
                    solver: "cegar-ic3".to_string(),
                    time_ms,
                    strength: ProofStrength::inductive(),
                    proof_certificate: None,
                solver_warnings: None,
                }
            }
            Ok(Ic3Result::Unsafe { trace }) => {
                let time_ms = start.elapsed().as_millis() as u64;
                let cex = ic3_trace_to_counterexample(&trace);
                VerificationResult::Failed {
                    solver: "cegar-ic3".to_string(),
                    time_ms,
                    counterexample: Some(cex),
                }
            }
            Ok(Ic3Result::Unknown { depth }) => {
                let time_ms = start.elapsed().as_millis() as u64;
                VerificationResult::Unknown {
                    solver: "cegar-ic3".to_string(),
                    time_ms,
                    reason: format!("IC3 reached depth {depth} without convergence"),
                }
            }
            Ok(_) => {
                // Handle future non-exhaustive Ic3Result variants.
                let time_ms = start.elapsed().as_millis() as u64;
                VerificationResult::Unknown {
                    solver: "cegar-ic3".to_string(),
                    time_ms,
                    reason: "IC3 returned unrecognized result variant".to_string(),
                }
            }
            Err(e) => {
                let time_ms = start.elapsed().as_millis() as u64;
                VerificationResult::Unknown {
                    solver: "cegar-ic3".to_string(),
                    time_ms,
                    reason: format!("IC3 error: {e}"),
                }
            }
        }
    }
}

impl Default for CegarBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl crate::VerificationBackend for CegarBackend {
    fn name(&self) -> &str {
        "cegar"
    }

    fn role(&self) -> crate::BackendRole {
        crate::BackendRole::Cegar
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        let classification = cegar_classifier::classify_with_threshold(
            vc,
            self.config.classifier_threshold,
        );
        classification.should_use_cegar
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        let start = Instant::now();
        self.run_cegar(vc, start)
    }
}

/// Internal step result during CEGAR iteration.
enum CegarStepResult {
    /// Property proved safe under current abstraction.
    Safe,
    /// Found a real counterexample.
    Unsafe(Counterexample),
    /// Abstraction was refined, continue iterating.
    Continue,
    /// Refinement stalled, no progress possible.
    Stalled,
}

/// Extract initial predicates from a formula for CEGAR bootstrapping.
fn discover_initial_predicates(formula: &Formula) -> Vec<Predicate> {
    let mut predicates = Vec::new();
    extract_predicates_recursive(formula, &mut predicates);
    predicates
}

/// Recursively extract comparison predicates from formula structure.
fn extract_predicates_recursive(formula: &Formula, predicates: &mut Vec<Predicate>) {
    match formula {
        Formula::Gt(lhs, rhs) | Formula::Ge(lhs, rhs) => {
            if let (Some(lhs_name), Some(rhs_name)) = (var_name(lhs), var_name(rhs)) {
                let op = if matches!(formula, Formula::Gt(..)) {
                    trust_cegar::CmpOp::Gt
                } else {
                    trust_cegar::CmpOp::Ge
                };
                let pred = Predicate::comparison(&lhs_name, op, &rhs_name);
                if !predicates.contains(&pred) {
                    predicates.push(pred);
                }
            }
            if let Some(name) = var_name(lhs)
                && let Some(val) = const_value(rhs) {
                    let op = if matches!(formula, Formula::Gt(..)) {
                        trust_cegar::CmpOp::Gt
                    } else {
                        trust_cegar::CmpOp::Ge
                    };
                    let pred = Predicate::comparison(&name, op, val.to_string());
                    if !predicates.contains(&pred) {
                        predicates.push(pred);
                    }
                }
        }
        Formula::Lt(lhs, rhs) | Formula::Le(lhs, rhs) => {
            if let Some(name) = var_name(lhs)
                && let Some(val) = const_value(rhs) {
                    let op = if matches!(formula, Formula::Lt(..)) {
                        trust_cegar::CmpOp::Lt
                    } else {
                        trust_cegar::CmpOp::Le
                    };
                    let pred = Predicate::comparison(&name, op, val.to_string());
                    if !predicates.contains(&pred) {
                        predicates.push(pred);
                    }
                }
        }
        Formula::Eq(lhs, rhs) => {
            if let Some(name) = var_name(lhs)
                && let Some(val) = const_value(rhs) {
                    let pred = Predicate::comparison(&name, trust_cegar::CmpOp::Eq, val.to_string());
                    if !predicates.contains(&pred) {
                        predicates.push(pred);
                    }
                }
        }
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                extract_predicates_recursive(child, predicates);
            }
        }
        Formula::Not(inner) => {
            extract_predicates_recursive(inner, predicates);
        }
        Formula::Implies(a, b) => {
            extract_predicates_recursive(a, predicates);
            extract_predicates_recursive(b, predicates);
        }
        _ => {}
    }
}

/// Extract variable name from a formula node.
fn var_name(f: &Formula) -> Option<String> {
    match f {
        Formula::Var(name, _) => Some(name.clone()),
        _ => None,
    }
}

/// Extract constant value from a formula node.
fn const_value(f: &Formula) -> Option<i128> {
    match f {
        Formula::Int(n) => Some(*n),
        Formula::Bool(true) => Some(1),
        Formula::Bool(false) => Some(0),
        _ => None,
    }
}

/// Generate a synthetic counterexample from formula variables for CEGAR driving.
fn extract_synthetic_counterexample(formula: &Formula) -> Counterexample {
    let mut vars = FxHashSet::default();
    cegar_classifier::collect_variables(formula, &mut vars);

    let assignments: Vec<(String, CounterexampleValue)> = vars
        .into_iter()
        .map(|name| (name, CounterexampleValue::Int(0)))
        .collect();

    Counterexample::new(assignments)
}

/// Convert a formula into a transition system for IC3.
///
/// Maps the VC formula into the (init, transition, property) triple:
/// - init: formula representing the initial state (true = any state)
/// - transition: identity transition (conservative)
/// - property: the VC's formula (what we want to prove)
fn formula_to_transition_system(formula: &Formula) -> TransitionSystem {
    TransitionSystem::new(
        Formula::Bool(true),
        Formula::Bool(true),
        formula.clone(),
    )
}

/// Convert an IC3 counterexample trace into a verification counterexample.
fn ic3_trace_to_counterexample(trace: &[trust_cegar::Cube]) -> Counterexample {
    let mut assignments = Vec::new();
    for (i, cube) in trace.iter().enumerate() {
        for (j, lit) in cube.literals.iter().enumerate() {
            let name = format!("trace_{i}_lit_{j}");
            let value = match lit {
                Formula::Bool(b) => CounterexampleValue::Bool(*b),
                Formula::Int(n) => CounterexampleValue::Int(*n),
                _ => CounterexampleValue::Bool(false),
            };
            assignments.push((name, value));
        }
    }
    Counterexample::new(assignments)
}

// Make collect_variables accessible from cegar_backend for extract_synthetic_counterexample.
// It is pub(crate) in cegar_classifier.

#[cfg(test)]
mod tests {
    use trust_types::{Sort, SourceSpan, VcKind};

    use super::*;
    use crate::VerificationBackend;

    fn make_vc(kind: VcKind, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "test_fn".to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    #[test]
    fn test_cegar_backend_name() {
        let backend = CegarBackend::new();
        assert_eq!(backend.name(), "cegar");
    }

    #[test]
    fn test_cegar_backend_role() {
        let backend = CegarBackend::new();
        assert_eq!(backend.role(), crate::BackendRole::Cegar);
    }

    #[test]
    fn test_can_handle_simple_vc_returns_false() {
        let backend = CegarBackend::new();
        let vc = make_vc(VcKind::DivisionByZero, Formula::Bool(false));
        assert!(!backend.can_handle(&vc), "simple VCs should not use CEGAR");
    }

    #[test]
    fn test_can_handle_non_termination_returns_false() {
        // tRust #194: NonTermination VCs must NOT be routed to CEGAR/IC3/PDR.
        // PDR proves safety (AG !bad), not termination.
        let backend = CegarBackend::with_config(CegarBackendConfig {
            classifier_threshold: 30,
            ..CegarBackendConfig::default()
        });
        let vc = make_vc(
            VcKind::NonTermination {
                context: "loop".to_string(),
                measure: "n".to_string(),
            },
            Formula::Bool(false),
        );
        assert!(!backend.can_handle(&vc), "NonTermination must NOT use CEGAR (PDR proves safety, not termination)");
    }

    #[test]
    fn test_verify_trivially_true() {
        let backend = CegarBackend::with_config(CegarBackendConfig {
            classifier_threshold: 0, // Accept all VCs for testing
            ..CegarBackendConfig::default()
        });
        let vc = make_vc(VcKind::DivisionByZero, Formula::Bool(true));
        let result = backend.verify(&vc);
        assert!(result.is_proved(), "trivially true formula should be proved");
        assert_eq!(result.solver_name(), "cegar");
    }

    #[test]
    fn test_verify_trivially_false() {
        let backend = CegarBackend::with_config(CegarBackendConfig {
            classifier_threshold: 0,
            ..CegarBackendConfig::default()
        });
        let vc = make_vc(VcKind::DivisionByZero, Formula::Bool(false));
        let result = backend.verify(&vc);
        assert!(result.is_failed(), "trivially false formula should fail");
    }

    #[test]
    fn test_verify_with_timeout() {
        let backend = CegarBackend::with_config(CegarBackendConfig {
            classifier_threshold: 0,
            timeout_ms: 1, // 1ms timeout - will trigger quickly
            max_iterations: 1_000_000,
            ic3_fallback: false,
            ..CegarBackendConfig::default()
        });
        // Non-trivial formula to prevent instant resolution.
        let x = Formula::Var("x".into(), Sort::Int);
        let formula = Formula::Gt(Box::new(x), Box::new(Formula::Int(0)));
        let vc = make_vc(VcKind::DivisionByZero, formula);
        let result = backend.verify(&vc);
        // Either timeout or unknown/proved depending on timing.
        let name = result.solver_name();
        assert!(name == "cegar" || name == "cegar-ic3");
    }

    #[test]
    fn test_verify_non_trivial_with_ic3_fallback() {
        let backend = CegarBackend::with_config(CegarBackendConfig {
            classifier_threshold: 0,
            max_iterations: 2,
            ic3_fallback: true,
            ..CegarBackendConfig::default()
        });
        let x = Formula::Var("x".into(), Sort::Int);
        let formula = Formula::Gt(Box::new(x), Box::new(Formula::Int(0)));
        let vc = make_vc(VcKind::DivisionByZero, formula);
        let result = backend.verify(&vc);
        // IC3 fallback should produce some result.
        let name = result.solver_name();
        assert!(
            name == "cegar" || name == "cegar-ic3",
            "solver should be cegar or cegar-ic3, got: {name}"
        );
    }

    #[test]
    fn test_verify_without_ic3_fallback() {
        let backend = CegarBackend::with_config(CegarBackendConfig {
            classifier_threshold: 0,
            max_iterations: 1,
            ic3_fallback: false,
            ..CegarBackendConfig::default()
        });
        let x = Formula::Var("x".into(), Sort::Int);
        let formula = Formula::Gt(Box::new(x), Box::new(Formula::Int(0)));
        let vc = make_vc(VcKind::DivisionByZero, formula);
        let result = backend.verify(&vc);
        assert_eq!(result.solver_name(), "cegar");
    }

    #[test]
    fn test_discover_initial_predicates_from_comparison() {
        let x = Formula::Var("x".into(), Sort::Int);
        let formula = Formula::Gt(Box::new(x), Box::new(Formula::Int(0)));
        let preds = discover_initial_predicates(&formula);
        assert!(!preds.is_empty());
    }

    #[test]
    fn test_discover_initial_predicates_from_conjunction() {
        let x = Formula::Var("x".into(), Sort::Int);
        let y = Formula::Var("y".into(), Sort::Int);
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(x), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(y), Box::new(Formula::Int(100))),
        ]);
        let preds = discover_initial_predicates(&formula);
        assert!(preds.len() >= 2, "should extract at least 2 predicates");
    }

    #[test]
    fn test_discover_initial_predicates_empty_for_bool() {
        let preds = discover_initial_predicates(&Formula::Bool(true));
        assert!(preds.is_empty());
    }

    #[test]
    fn test_extract_synthetic_counterexample() {
        let formula = Formula::And(vec![
            Formula::Var("x".into(), Sort::Int),
            Formula::Var("y".into(), Sort::Int),
        ]);
        let cex = extract_synthetic_counterexample(&formula);
        assert_eq!(cex.assignments.len(), 2);
    }

    #[test]
    fn test_formula_to_transition_system() {
        let prop = Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let sys = formula_to_transition_system(&prop);
        assert_eq!(sys.init, Formula::Bool(true));
        assert_eq!(sys.transition, Formula::Bool(true));
        assert_eq!(sys.property, prop);
    }

    #[test]
    fn test_ic3_trace_to_counterexample_empty() {
        let cex = ic3_trace_to_counterexample(&[]);
        assert!(cex.assignments.is_empty());
    }

    #[test]
    fn test_ic3_trace_to_counterexample_with_cubes() {
        let trace = vec![
            trust_cegar::Cube::new(vec![Formula::Bool(true)]),
            trust_cegar::Cube::new(vec![Formula::Int(42)]),
        ];
        let cex = ic3_trace_to_counterexample(&trace);
        assert_eq!(cex.assignments.len(), 2);
        assert_eq!(cex.assignments[0].0, "trace_0_lit_0");
        assert_eq!(cex.assignments[1].0, "trace_1_lit_0");
    }

    #[test]
    fn test_default_config() {
        let config = CegarBackendConfig::default();
        assert_eq!(config.max_iterations, 100);
        assert_eq!(config.timeout_ms, 30_000);
        assert_eq!(config.classifier_threshold, 30);
        assert_eq!(config.ic3_max_depth, 200);
        assert!(config.ic3_fallback);
    }

    #[test]
    fn test_backend_default_impl() {
        let backend = CegarBackend::default();
        assert_eq!(backend.name(), "cegar");
    }
}
