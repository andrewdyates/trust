// trust-router diagnostic enrichment for counterexamples
//
// Adds contextual information to counterexamples: closest valid state,
// minimal modification to make the property pass, and classification
// of the violation type.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_symex::adapter::{AdapterResult, ValueSnapshot};
use trust_types::{Counterexample, CounterexampleValue, VcKind, VerificationCondition};

/// Enriched diagnostic information for a counterexample.
#[derive(Debug, Clone)]
pub struct EnrichedDiagnostic {
    /// The original counterexample.
    pub counterexample: Counterexample,
    /// Human-readable description of the violation.
    pub violation_description: String,
    /// Classification of the violation type.
    pub violation_kind: ViolationKind,
    /// Suggested minimal modifications to make the property pass.
    pub suggested_fixes: Vec<SuggestedFix>,
    /// Variables that were involved in the violation (subset of counterexample).
    pub relevant_variables: Vec<(String, String)>,
    /// The closest valid state (if computable): variable assignments that
    /// would satisfy the property.
    pub closest_valid_state: Option<FxHashMap<String, String>>,
}

/// Classification of counterexample violations.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ViolationKind {
    /// Division by zero: a denominator is zero.
    DivisionByZero,
    /// Arithmetic overflow: an operation exceeds type bounds.
    ArithmeticOverflow,
    /// Index out of bounds: array/slice access beyond length.
    IndexOutOfBounds,
    /// Precondition violation: caller violated function contract.
    PreconditionViolation,
    /// Postcondition violation: function didn't satisfy its contract.
    PostconditionViolation,
    /// Invariant violation: loop or type invariant broken.
    InvariantViolation,
    /// Memory safety issue (null deref, use-after-free, etc.).
    MemorySafety,
    /// Other/unclassified violation.
    Other(String),
}

/// A suggested minimal fix for a counterexample violation.
#[derive(Debug, Clone)]
pub struct SuggestedFix {
    /// Variable to modify.
    pub variable: String,
    /// Current value in the counterexample.
    pub current_value: String,
    /// Suggested new value that would avoid the violation.
    pub suggested_value: String,
    /// Human-readable explanation.
    pub explanation: String,
}

/// Enrich a counterexample with diagnostic information.
///
/// Analyzes the VC kind, the counterexample values, and the adapter result
/// to produce human-readable diagnostics including violation classification,
/// relevant variables, and suggested fixes.
#[must_use]
pub fn enrich_counterexample(
    vc: &VerificationCondition,
    counterexample: &Counterexample,
    adapter_result: &AdapterResult,
) -> EnrichedDiagnostic {
    let violation_kind = classify_violation(&vc.kind);
    let violation_description = describe_violation(&vc.kind, counterexample);
    let relevant_variables = find_relevant_variables(&violation_kind, counterexample, adapter_result);
    let suggested_fixes = suggest_fixes(&violation_kind, counterexample, adapter_result);
    let closest_valid_state = compute_closest_valid_state(&violation_kind, counterexample);

    EnrichedDiagnostic {
        counterexample: counterexample.clone(),
        violation_description,
        violation_kind,
        suggested_fixes,
        relevant_variables,
        closest_valid_state,
    }
}

/// Classify the violation from the VC kind.
fn classify_violation(kind: &VcKind) -> ViolationKind {
    match kind {
        VcKind::DivisionByZero | VcKind::RemainderByZero => ViolationKind::DivisionByZero,
        VcKind::ArithmeticOverflow { .. }
        | VcKind::ShiftOverflow { .. }
        | VcKind::NegationOverflow { .. }
        | VcKind::CastOverflow { .. } => ViolationKind::ArithmeticOverflow,
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => ViolationKind::IndexOutOfBounds,
        VcKind::Precondition { .. } => ViolationKind::PreconditionViolation,
        VcKind::Postcondition => ViolationKind::PostconditionViolation,
        VcKind::Assertion { .. } => ViolationKind::InvariantViolation,
        _ => ViolationKind::Other(format!("{kind:?}")),
    }
}

/// Generate a human-readable description of the violation.
fn describe_violation(kind: &VcKind, cex: &Counterexample) -> String {
    let var_summary = format_cex_summary(cex);

    match kind {
        VcKind::DivisionByZero => {
            format!("Division by zero detected. When {var_summary}, a division operation has a zero denominator.")
        }
        VcKind::ArithmeticOverflow { op, operand_tys } => {
            format!(
                "Arithmetic overflow in {op:?} operation on ({:?}, {:?}). When {var_summary}, \
                 the result exceeds the representable range.",
                operand_tys.0, operand_tys.1
            )
        }
        VcKind::IndexOutOfBounds => {
            format!(
                "Index out of bounds. When {var_summary}, \
                 an array/slice index exceeds the valid range."
            )
        }
        VcKind::Precondition { callee } => {
            format!(
                "Precondition of `{callee}` violated. When {var_summary}, \
                 the function's input requirements are not met."
            )
        }
        VcKind::Postcondition => {
            format!(
                "Postcondition violated. When {var_summary}, \
                 the function's output guarantee does not hold."
            )
        }
        _ => {
            format!(
                "Verification condition violated ({kind:?}). When {var_summary}."
            )
        }
    }
}

/// Format counterexample assignments into a readable summary.
fn format_cex_summary(cex: &Counterexample) -> String {
    if cex.assignments.is_empty() {
        return "no specific input values".into();
    }

    let parts: Vec<String> = cex
        .assignments
        .iter()
        .take(5) // Limit to first 5 for readability.
        .map(|(name, val)| format!("{name} = {val}"))
        .collect();

    let suffix = if cex.assignments.len() > 5 {
        format!(" (and {} more)", cex.assignments.len() - 5)
    } else {
        String::new()
    };

    format!("{}{suffix}", parts.join(", "))
}

/// Identify variables relevant to the violation.
fn find_relevant_variables(
    violation_kind: &ViolationKind,
    cex: &Counterexample,
    adapter_result: &AdapterResult,
) -> Vec<(String, String)> {
    let mut relevant = Vec::new();

    // All counterexample variables are potentially relevant.
    for (name, val) in &cex.assignments {
        relevant.push((name.clone(), format!("{val}")));
    }

    // Add modified variables from the trace that might indicate the problem.
    for (name, snap) in &adapter_result.modified_vars {
        if !relevant.iter().any(|(n, _)| n == name) {
            relevant.push((name.clone(), format_snapshot_value(snap)));
        }
    }

    // For specific violation types, prioritize certain variables.
    match violation_kind {
        ViolationKind::DivisionByZero => {
            // Prioritize variables with value 0.
            relevant.sort_by(|a, b| {
                let a_zero = a.1 == "0";
                let b_zero = b.1 == "0";
                b_zero.cmp(&a_zero)
            });
        }
        ViolationKind::IndexOutOfBounds => {
            // Prioritize variables that look like indices or lengths.
            relevant.sort_by(|a, b| {
                let a_idx = a.0.contains("idx") || a.0.contains("index") || a.0.contains("len");
                let b_idx = b.0.contains("idx") || b.0.contains("index") || b.0.contains("len");
                b_idx.cmp(&a_idx)
            });
        }
        _ => {}
    }

    relevant
}

/// Format a ValueSnapshot as a string.
fn format_snapshot_value(snap: &ValueSnapshot) -> String {
    match snap.concrete {
        Some(val) => format!("{val}"),
        None => format!("<symbolic: {}>", snap.symbolic),
    }
}

/// Suggest minimal fixes to avoid the violation.
fn suggest_fixes(
    violation_kind: &ViolationKind,
    cex: &Counterexample,
    _adapter_result: &AdapterResult,
) -> Vec<SuggestedFix> {
    let mut fixes = Vec::new();

    match violation_kind {
        ViolationKind::DivisionByZero => {
            // Find variables with value 0 that are likely denominators.
            for (name, val) in &cex.assignments {
                if is_zero(val) {
                    fixes.push(SuggestedFix {
                        variable: name.clone(),
                        current_value: format!("{val}"),
                        suggested_value: "1".into(),
                        explanation: format!(
                            "Change {name} from 0 to a non-zero value to avoid division by zero."
                        ),
                    });
                }
            }
            if fixes.is_empty() {
                fixes.push(SuggestedFix {
                    variable: "<denominator>".into(),
                    current_value: "0".into(),
                    suggested_value: "!= 0".into(),
                    explanation: "Add a guard: ensure the denominator is non-zero before dividing.".into(),
                });
            }
        }
        ViolationKind::ArithmeticOverflow => {
            // Suggest reducing operand magnitudes.
            for (name, val) in &cex.assignments {
                if is_large_value(val) {
                    fixes.push(SuggestedFix {
                        variable: name.clone(),
                        current_value: format!("{val}"),
                        suggested_value: "smaller value".into(),
                        explanation: format!(
                            "Reduce {name} magnitude or use checked/saturating arithmetic."
                        ),
                    });
                }
            }
            if fixes.is_empty() {
                fixes.push(SuggestedFix {
                    variable: "<operands>".into(),
                    current_value: "current".into(),
                    suggested_value: "bounded".into(),
                    explanation: "Use checked_add/checked_mul or saturating arithmetic.".into(),
                });
            }
        }
        ViolationKind::IndexOutOfBounds => {
            for (name, val) in &cex.assignments {
                if name.contains("idx") || name.contains("index") {
                    fixes.push(SuggestedFix {
                        variable: name.clone(),
                        current_value: format!("{val}"),
                        suggested_value: "< len".into(),
                        explanation: format!(
                            "Ensure {name} is within bounds: add a bounds check before indexing."
                        ),
                    });
                }
            }
            if fixes.is_empty() {
                fixes.push(SuggestedFix {
                    variable: "<index>".into(),
                    current_value: "out of range".into(),
                    suggested_value: "< len".into(),
                    explanation: "Add a bounds check before array/slice access.".into(),
                });
            }
        }
        ViolationKind::PreconditionViolation => {
            fixes.push(SuggestedFix {
                variable: "<inputs>".into(),
                current_value: "violating".into(),
                suggested_value: "satisfying precondition".into(),
                explanation: "Ensure caller satisfies the function's #[requires] contract.".into(),
            });
        }
        ViolationKind::PostconditionViolation => {
            fixes.push(SuggestedFix {
                variable: "<return value>".into(),
                current_value: "violating".into(),
                suggested_value: "satisfying postcondition".into(),
                explanation: "Fix the function body to satisfy its #[ensures] contract.".into(),
            });
        }
        _ => {}
    }

    fixes
}

/// Check if a counterexample value is zero.
fn is_zero(val: &CounterexampleValue) -> bool {
    match val {
        CounterexampleValue::Int(n) => *n == 0,
        CounterexampleValue::Uint(n) => *n == 0,
        CounterexampleValue::Float(f) => *f == 0.0,
        CounterexampleValue::Bool(b) => !b,
        // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
        _ => false,
    }
}

/// Check if a counterexample value is large (potential overflow source).
fn is_large_value(val: &CounterexampleValue) -> bool {
    match val {
        CounterexampleValue::Int(n) => n.unsigned_abs() > (i64::MAX as u128),
        CounterexampleValue::Uint(n) => *n > (u64::MAX as u128),
        _ => false,
    }
}

/// Compute the closest valid state: variable assignments that would
/// satisfy the property with minimal changes.
///
/// This is a heuristic approximation: for simple violations (div-by-zero,
/// bounds checks), we can suggest specific value changes. For complex
/// properties, returns None.
fn compute_closest_valid_state(
    violation_kind: &ViolationKind,
    cex: &Counterexample,
) -> Option<FxHashMap<String, String>> {
    let mut valid_state = FxHashMap::default();

    match violation_kind {
        ViolationKind::DivisionByZero => {
            // Change zero-valued variables to 1.
            for (name, val) in &cex.assignments {
                if is_zero(val) {
                    valid_state.insert(name.clone(), "1".into());
                } else {
                    valid_state.insert(name.clone(), format!("{val}"));
                }
            }
            Some(valid_state)
        }
        ViolationKind::ArithmeticOverflow => {
            // Halve large values.
            for (name, val) in &cex.assignments {
                if is_large_value(val) {
                    let halved = match val {
                        CounterexampleValue::Int(n) => format!("{}", n / 2),
                        CounterexampleValue::Uint(n) => format!("{}", n / 2),
                        _ => format!("{val}"),
                    };
                    valid_state.insert(name.clone(), halved);
                } else {
                    valid_state.insert(name.clone(), format!("{val}"));
                }
            }
            Some(valid_state)
        }
        _ => None, // Complex violations need solver-based analysis.
    }
}

#[cfg(test)]
mod tests {
    use trust_types::fx::FxHashMap;

    use trust_symex::adapter::AdapterResult;
    use trust_symex::state::SymbolicState;
    use trust_types::*;

    use super::*;

    fn make_adapter_result() -> AdapterResult {
        AdapterResult {
            trace: vec![],
            final_state: SymbolicState::new(),
            block_trace: vec![0],
            terminated_normally: true,
            modified_vars: FxHashMap::default(),
        }
    }

    #[test]
    fn test_enrich_division_by_zero() {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "div_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };

        let cex = Counterexample::new(vec![
            ("x".into(), CounterexampleValue::Int(42)),
            ("y".into(), CounterexampleValue::Int(0)),
        ]);

        let enriched = enrich_counterexample(&vc, &cex, &make_adapter_result());

        assert_eq!(enriched.violation_kind, ViolationKind::DivisionByZero);
        assert!(enriched.violation_description.contains("Division by zero"));
        // Should suggest changing y from 0 to non-zero.
        assert!(!enriched.suggested_fixes.is_empty());
        let fix = &enriched.suggested_fixes[0];
        assert_eq!(fix.variable, "y");
        assert_eq!(fix.suggested_value, "1");

        // Closest valid state should change y to 1.
        let valid = enriched.closest_valid_state.expect("should have valid state");
        assert_eq!(valid.get("y").unwrap(), "1");
        assert_eq!(valid.get("x").unwrap(), "42");
    }

    #[test]
    fn test_enrich_overflow() {
        let vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::i32(), Ty::i32()),
            },
            function: "add_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };

        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Int(i128::from(i64::MAX) + 1)),
        ]);

        let enriched = enrich_counterexample(&vc, &cex, &make_adapter_result());
        assert_eq!(enriched.violation_kind, ViolationKind::ArithmeticOverflow);
        assert!(!enriched.suggested_fixes.is_empty());
    }

    #[test]
    fn test_enrich_precondition() {
        let vc = VerificationCondition {
            kind: VcKind::Precondition { callee: "foo".into() },
            function: "caller".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };

        let cex = Counterexample::new(vec![
            ("x".into(), CounterexampleValue::Int(-1)),
        ]);

        let enriched = enrich_counterexample(&vc, &cex, &make_adapter_result());
        assert_eq!(enriched.violation_kind, ViolationKind::PreconditionViolation);
        assert!(enriched.violation_description.contains("foo"));
    }

    #[test]
    fn test_enrich_postcondition() {
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "compute".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };

        let cex = Counterexample::new(vec![]);
        let enriched = enrich_counterexample(&vc, &cex, &make_adapter_result());
        assert_eq!(enriched.violation_kind, ViolationKind::PostconditionViolation);
    }

    #[test]
    fn test_enrich_relevant_variables_sorted() {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "div_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };

        let cex = Counterexample::new(vec![
            ("numerator".into(), CounterexampleValue::Int(42)),
            ("denominator".into(), CounterexampleValue::Int(0)),
        ]);

        let enriched = enrich_counterexample(&vc, &cex, &make_adapter_result());
        // For DivisionByZero, zero-valued variables should be first.
        assert_eq!(enriched.relevant_variables[0].0, "denominator");
    }

    #[test]
    fn test_classify_violation_kinds() {
        assert_eq!(classify_violation(&VcKind::DivisionByZero), ViolationKind::DivisionByZero);
        assert_eq!(
            classify_violation(&VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::i32(), Ty::i32()),
            }),
            ViolationKind::ArithmeticOverflow
        );
        assert_eq!(classify_violation(&VcKind::IndexOutOfBounds), ViolationKind::IndexOutOfBounds);
        assert_eq!(classify_violation(&VcKind::Postcondition), ViolationKind::PostconditionViolation);
    }

    #[test]
    fn test_is_zero_values() {
        assert!(is_zero(&CounterexampleValue::Int(0)));
        assert!(is_zero(&CounterexampleValue::Uint(0)));
        assert!(!is_zero(&CounterexampleValue::Int(1)));
        assert!(!is_zero(&CounterexampleValue::Uint(1)));
    }
}
