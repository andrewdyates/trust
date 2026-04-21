// trust-router/mock_backend.rs: Mock backend for testing
//
// Evaluates simple formula patterns without a real SMT solver.
// Used for testing the pipeline structure before z4 is wired up.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::{BackendRole, VerificationBackend};

/// Mock backend that evaluates trivial formulas.
pub struct MockBackend;

impl VerificationBackend for MockBackend {
    fn name(&self) -> &str {
        "mock"
    }

    fn role(&self) -> BackendRole {
        BackendRole::General
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        let start = std::time::Instant::now();
        let result = eval_formula(&vc.formula);
        let elapsed = start.elapsed().as_millis() as u64;

        match result {
            FormulaResult::False => VerificationResult::Proved {
                solver: "mock".to_string(),
                time_ms: elapsed,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            },
            FormulaResult::True => VerificationResult::Failed {
                solver: "mock".to_string(),
                time_ms: elapsed,
                counterexample: None,
            },
            FormulaResult::Unknown => VerificationResult::Unknown {
                solver: "mock".to_string(),
                time_ms: elapsed,
                reason: "mock backend cannot evaluate complex formulas".to_string(),
            },
        }
    }
}

enum FormulaResult {
    True,
    False,
    Unknown,
}

/// Trivial formula evaluator for constants and simple patterns.
fn eval_formula(formula: &Formula) -> FormulaResult {
    match formula {
        Formula::Bool(true) => FormulaResult::True,
        Formula::Bool(false) => FormulaResult::False,
        Formula::Not(inner) => match eval_formula(inner) {
            FormulaResult::True => FormulaResult::False,
            FormulaResult::False => FormulaResult::True,
            FormulaResult::Unknown => FormulaResult::Unknown,
        },
        // For the midpoint case: the formula has variables, so unknown
        Formula::And(terms) => {
            let mut any_unknown = false;
            for term in terms {
                match eval_formula(term) {
                    FormulaResult::False => return FormulaResult::False,
                    FormulaResult::Unknown => any_unknown = true,
                    FormulaResult::True => {}
                }
            }
            if any_unknown { FormulaResult::Unknown } else { FormulaResult::True }
        }
        Formula::Or(terms) => {
            let mut any_unknown = false;
            for term in terms {
                match eval_formula(term) {
                    FormulaResult::True => return FormulaResult::True,
                    FormulaResult::Unknown => any_unknown = true,
                    FormulaResult::False => {}
                }
            }
            if any_unknown { FormulaResult::Unknown } else { FormulaResult::False }
        }
        // Equality of constants
        Formula::Eq(a, b) => match (a.as_ref(), b.as_ref()) {
            (Formula::Int(x), Formula::Int(y)) => {
                if x == y {
                    FormulaResult::True
                } else {
                    FormulaResult::False
                }
            }
            _ => FormulaResult::Unknown,
        },
        // Anything with variables → Unknown
        _ => FormulaResult::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mock_proves_trivially_false() {
        let backend = MockBackend;
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        let result = backend.verify(&vc);
        assert!(result.is_proved());
    }

    #[test]
    fn test_mock_fails_trivially_true() {
        let backend = MockBackend;
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let result = backend.verify(&vc);
        assert!(result.is_failed());
    }

    #[test]
    fn test_mock_unknown_for_variables() {
        let backend = MockBackend;
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Var("x".into(), Sort::Int),
            contract_metadata: None,
        };
        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }
}
