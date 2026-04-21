// trust-debug/minimization.rs: Counterexample and failure minimization
//
// Implements delta debugging and related minimization algorithms to reduce
// counterexamples, execution traces, and formulas to their essential core.
// A smaller counterexample is easier to understand and debug.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Counterexample, CounterexampleValue, Formula};

/// Result of a minimization operation.
#[derive(Debug, Clone)]
pub(crate) struct MinimizationResult<T: std::fmt::Debug + Clone> {
    /// The minimized artifact.
    pub minimized: T,
    /// Size of the original artifact.
    pub original_size: usize,
    /// Size of the minimized artifact.
    pub minimized_size: usize,
    /// Reduction ratio (0.0 = no reduction, 1.0 = eliminated entirely).
    pub reduction_ratio: f64,
    /// Number of test iterations performed during minimization.
    pub iterations: usize,
}

impl<T: std::fmt::Debug + Clone> MinimizationResult<T> {
    fn new(minimized: T, original_size: usize, minimized_size: usize, iterations: usize) -> Self {
        let reduction_ratio = if original_size == 0 {
            0.0
        } else {
            1.0 - (minimized_size as f64 / original_size as f64)
        };
        Self {
            minimized,
            original_size,
            minimized_size,
            reduction_ratio,
            iterations,
        }
    }
}

/// Outcome of testing a candidate during minimization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TestOutcome {
    /// The candidate still triggers the failure (keep minimizing).
    Fail,
    /// The candidate no longer triggers the failure (reject this reduction).
    Pass,
}

/// Delta debugging algorithm for minimizing failing inputs.
///
/// Given an input that triggers a failure, delta debugging systematically
/// removes parts of the input to find the minimal subset that still fails.
/// Based on Zeller & Hildebrandt, "Simplifying and Isolating Failure-Inducing Input" (2002).
pub(crate) struct DeltaDebugger {
    /// Maximum number of iterations before giving up.
    max_iterations: usize,
}

impl Default for DeltaDebugger {
    fn default() -> Self {
        Self {
            max_iterations: 1000,
        }
    }
}

impl DeltaDebugger {
    /// Create a delta debugger with custom iteration limit.
    #[must_use]
    pub(crate) fn with_max_iterations(max_iterations: usize) -> Self {
        Self { max_iterations }
    }

    /// Minimize a vector of elements using delta debugging.
    ///
    /// The `test_fn` should return `TestOutcome::Fail` if the subset still
    /// triggers the failure, and `TestOutcome::Pass` if the failure disappears.
    ///
    /// Returns the minimal subset that still fails.
    pub(crate) fn minimize_input<T: Clone + std::fmt::Debug>(
        &self,
        input: &[T],
        test_fn: &dyn Fn(&[T]) -> TestOutcome,
    ) -> MinimizationResult<Vec<T>> {
        if input.is_empty() || test_fn(input) == TestOutcome::Pass {
            return MinimizationResult::new(input.to_vec(), input.len(), input.len(), 0);
        }

        let original_size = input.len();
        let mut current = input.to_vec();
        let mut granularity = 2_usize;
        let mut iterations = 0;

        while current.len() >= 2 && iterations < self.max_iterations {
            let chunk_size = current.len().div_ceil(granularity);
            let mut some_complement_failed = false;

            // Try removing each chunk
            let num_chunks = current.len().div_ceil(chunk_size);
            let mut i = 0;
            while i < num_chunks && iterations < self.max_iterations {
                iterations += 1;

                let start = i * chunk_size;
                let end = (start + chunk_size).min(current.len());

                // Build complement (everything except this chunk)
                let complement: Vec<T> = current[..start]
                    .iter()
                    .chain(current[end..].iter())
                    .cloned()
                    .collect();

                if !complement.is_empty() && test_fn(&complement) == TestOutcome::Fail {
                    // Complement still fails => remove the chunk
                    current = complement;
                    // Reset granularity for the smaller input
                    granularity = 2.max(granularity - 1);
                    some_complement_failed = true;
                    break;
                }

                i += 1;
            }

            if !some_complement_failed {
                if granularity >= current.len() {
                    // Cannot reduce further
                    break;
                }
                granularity = (granularity * 2).min(current.len());
            }
        }

        let minimized_size = current.len();
        MinimizationResult::new(current, original_size, minimized_size, iterations)
    }
}

/// A step in an execution trace.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct TraceStep {
    /// Function name.
    pub function: String,
    /// Step index within the trace.
    pub index: usize,
    /// Description of what happens at this step.
    pub description: String,
}

/// Minimize a counterexample by removing variables that are not essential.
///
/// An assignment is essential if removing it causes the property to no longer
/// be violated. The `property_test` function should return `TestOutcome::Fail`
/// when the counterexample still violates the property.
pub(crate) fn minimize_counterexample(
    cex: &Counterexample,
    property_test: &dyn Fn(&Counterexample) -> TestOutcome,
) -> MinimizationResult<Counterexample> {
    let original_size = cex.assignments.len();
    let debugger = DeltaDebugger::default();

    let result = debugger.minimize_input(&cex.assignments, &|subset| {
        let test_cex = Counterexample::new(subset.to_vec());
        property_test(&test_cex)
    });

    MinimizationResult::new(
        Counterexample::new(result.minimized),
        original_size,
        result.minimized_size,
        result.iterations,
    )
}

/// Minimize an execution trace to the shortest subsequence that still
/// demonstrates the property violation.
///
/// The `property_test` function should return `TestOutcome::Fail` when the
/// trace subsequence still demonstrates the violation.
pub(crate) fn minimize_trace(
    trace: &[TraceStep],
    property_test: &dyn Fn(&[TraceStep]) -> TestOutcome,
) -> MinimizationResult<Vec<TraceStep>> {
    let debugger = DeltaDebugger::default();
    debugger.minimize_input(trace, property_test)
}

/// Identify variables in a counterexample that are essential for the violation.
///
/// A variable is essential if removing it from the counterexample causes the
/// property to no longer be violated. Returns the names of essential variables.
#[must_use]
pub(crate) fn essential_variables(
    cex: &Counterexample,
    property_test: &dyn Fn(&Counterexample) -> TestOutcome,
) -> Vec<String> {
    let mut essential = Vec::new();

    for (i, (name, _)) in cex.assignments.iter().enumerate() {
        // Build counterexample without this variable
        let without: Vec<(String, CounterexampleValue)> = cex
            .assignments
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != i)
            .map(|(_, a)| a.clone())
            .collect();

        let reduced = Counterexample::new(without);

        // If removing this variable causes the property to pass,
        // then the variable is essential
        if property_test(&reduced) == TestOutcome::Pass {
            essential.push(name.clone());
        }
    }

    essential
}

/// Simplify a formula by applying algebraic identities.
///
/// Applies standard simplifications:
/// - `And([])` => `Bool(true)`
/// - `Or([])` => `Bool(false)`
/// - `And([x])` => `x`
/// - `Or([x])` => `x`
/// - `Not(Bool(b))` => `Bool(!b)`
/// - `Not(Not(x))` => `x`
/// - `And` with `Bool(false)` => `Bool(false)`
/// - `Or` with `Bool(true)` => `Bool(true)`
/// - `And` removes `Bool(true)` elements
/// - `Or` removes `Bool(false)` elements
#[must_use]
pub(crate) fn simplify_formula(formula: &Formula) -> Formula {
    match formula {
        Formula::Not(inner) => match inner.as_ref() {
            Formula::Bool(b) => Formula::Bool(!b),
            Formula::Not(double_inner) => simplify_formula(double_inner),
            other => {
                let simplified = simplify_formula(other);
                if let Formula::Bool(b) = simplified {
                    Formula::Bool(!b)
                } else {
                    Formula::Not(Box::new(simplified))
                }
            }
        },
        Formula::And(conjuncts) => {
            let simplified: Vec<Formula> = conjuncts
                .iter()
                .map(simplify_formula)
                .collect();

            // Short-circuit: any false makes the whole thing false
            if simplified.iter().any(|f| matches!(f, Formula::Bool(false))) {
                return Formula::Bool(false);
            }

            // Remove true elements
            let filtered: Vec<Formula> = simplified
                .into_iter()
                .filter(|f| !matches!(f, Formula::Bool(true)))
                .collect();

            match filtered.len() {
                0 => Formula::Bool(true),
                1 => filtered.into_iter().next().expect("checked len == 1"),
                _ => Formula::And(filtered),
            }
        }
        Formula::Or(disjuncts) => {
            let simplified: Vec<Formula> = disjuncts
                .iter()
                .map(simplify_formula)
                .collect();

            // Short-circuit: any true makes the whole thing true
            if simplified.iter().any(|f| matches!(f, Formula::Bool(true))) {
                return Formula::Bool(true);
            }

            // Remove false elements
            let filtered: Vec<Formula> = simplified
                .into_iter()
                .filter(|f| !matches!(f, Formula::Bool(false)))
                .collect();

            match filtered.len() {
                0 => Formula::Bool(false),
                1 => filtered.into_iter().next().expect("checked len == 1"),
                _ => Formula::Or(filtered),
            }
        }
        Formula::Implies(lhs, rhs) => {
            let l = simplify_formula(lhs);
            let r = simplify_formula(rhs);
            match (&l, &r) {
                (Formula::Bool(false), _) => Formula::Bool(true),  // false => anything
                (_, Formula::Bool(true)) => Formula::Bool(true),   // anything => true
                (Formula::Bool(true), _) => r,                     // true => P  ===  P
                _ => Formula::Implies(Box::new(l), Box::new(r)),
            }
        }
        // Atoms and other formulas pass through unchanged
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{CounterexampleValue, Formula, Sort};

    // --- DeltaDebugger tests ---

    #[test]
    fn test_delta_debug_empty_input() {
        let debugger = DeltaDebugger::default();
        let input: Vec<i32> = vec![];
        let result = debugger.minimize_input(&input, &|_| TestOutcome::Fail);
        assert!(result.minimized.is_empty());
        assert_eq!(result.original_size, 0);
        assert_eq!(result.iterations, 0);
    }

    #[test]
    fn test_delta_debug_single_element() {
        let debugger = DeltaDebugger::default();
        let input = vec![42];
        let result = debugger.minimize_input(&input, &|subset| {
            if subset.contains(&42) {
                TestOutcome::Fail
            } else {
                TestOutcome::Pass
            }
        });
        assert_eq!(result.minimized, vec![42]);
        assert_eq!(result.minimized_size, 1);
    }

    #[test]
    fn test_delta_debug_finds_minimal_subset() {
        let debugger = DeltaDebugger::default();
        // Input: [1, 2, 3, 4, 5, 6, 7, 8]
        // Failure requires element 5 to be present
        let input: Vec<i32> = (1..=8).collect();
        let result = debugger.minimize_input(&input, &|subset| {
            if subset.contains(&5) {
                TestOutcome::Fail
            } else {
                TestOutcome::Pass
            }
        });
        assert!(
            result.minimized.contains(&5),
            "minimized should contain the essential element 5"
        );
        assert!(
            result.minimized_size <= input.len(),
            "minimized should not be larger than original"
        );
        assert!(result.reduction_ratio >= 0.0);
    }

    #[test]
    fn test_delta_debug_two_required_elements() {
        let debugger = DeltaDebugger::default();
        // Failure requires both 3 and 7
        let input: Vec<i32> = (1..=10).collect();
        let result = debugger.minimize_input(&input, &|subset| {
            if subset.contains(&3) && subset.contains(&7) {
                TestOutcome::Fail
            } else {
                TestOutcome::Pass
            }
        });
        assert!(result.minimized.contains(&3));
        assert!(result.minimized.contains(&7));
        assert!(result.minimized_size <= input.len());
    }

    #[test]
    fn test_delta_debug_all_pass_no_reduction() {
        let debugger = DeltaDebugger::default();
        let input = vec![1, 2, 3];
        let result = debugger.minimize_input(&input, &|_| TestOutcome::Pass);
        assert_eq!(result.minimized, vec![1, 2, 3]);
        assert_eq!(result.iterations, 0);
    }

    #[test]
    fn test_delta_debug_max_iterations() {
        let debugger = DeltaDebugger::with_max_iterations(5);
        let input: Vec<i32> = (1..=100).collect();
        let result = debugger.minimize_input(&input, &|_subset| TestOutcome::Fail);
        assert!(result.iterations <= 5);
    }

    // --- Counterexample minimization tests ---

    #[test]
    fn test_minimize_counterexample_removes_irrelevant() {
        let cex = Counterexample::new(vec![
            ("a".to_string(), CounterexampleValue::Uint(10)),
            ("b".to_string(), CounterexampleValue::Uint(20)),
            ("c".to_string(), CounterexampleValue::Uint(30)),
            ("essential".to_string(), CounterexampleValue::Uint(999)),
        ]);

        let result = minimize_counterexample(&cex, &|test_cex| {
            // Only "essential" variable matters
            if test_cex
                .assignments
                .iter()
                .any(|(name, _)| name == "essential")
            {
                TestOutcome::Fail
            } else {
                TestOutcome::Pass
            }
        });

        assert!(result
            .minimized
            .assignments
            .iter()
            .any(|(name, _)| name == "essential"));
        assert!(
            result.minimized_size <= result.original_size,
            "should reduce counterexample size"
        );
    }

    #[test]
    fn test_minimize_counterexample_empty() {
        let cex = Counterexample::new(vec![]);
        let result = minimize_counterexample(&cex, &|_| TestOutcome::Fail);
        assert_eq!(result.minimized.assignments.len(), 0);
    }

    // --- Trace minimization tests ---

    #[test]
    fn test_minimize_trace_finds_essential_steps() {
        let trace = vec![
            TraceStep {
                function: "init".to_string(),
                index: 0,
                description: "initialize".to_string(),
            },
            TraceStep {
                function: "setup".to_string(),
                index: 1,
                description: "setup state".to_string(),
            },
            TraceStep {
                function: "bug".to_string(),
                index: 2,
                description: "trigger bug".to_string(),
            },
            TraceStep {
                function: "cleanup".to_string(),
                index: 3,
                description: "cleanup".to_string(),
            },
        ];

        let result = minimize_trace(&trace, &|subset| {
            // Bug step is essential
            if subset.iter().any(|s| s.function == "bug") {
                TestOutcome::Fail
            } else {
                TestOutcome::Pass
            }
        });

        assert!(result
            .minimized
            .iter()
            .any(|s| s.function == "bug"));
        assert!(result.minimized_size <= result.original_size);
    }

    #[test]
    fn test_minimize_trace_empty() {
        let trace: Vec<TraceStep> = vec![];
        let result = minimize_trace(&trace, &|_| TestOutcome::Fail);
        assert!(result.minimized.is_empty());
    }

    // --- Essential variables tests ---

    #[test]
    fn test_essential_variables_identifies_critical_ones() {
        let cex = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Uint(5)),
            ("y".to_string(), CounterexampleValue::Uint(10)),
            ("noise".to_string(), CounterexampleValue::Uint(42)),
        ]);

        let essential = essential_variables(&cex, &|test_cex| {
            // Both x and y are needed for the violation
            let has_x = test_cex.assignments.iter().any(|(n, _)| n == "x");
            let has_y = test_cex.assignments.iter().any(|(n, _)| n == "y");
            if has_x && has_y {
                TestOutcome::Fail
            } else {
                TestOutcome::Pass
            }
        });

        assert!(essential.contains(&"x".to_string()));
        assert!(essential.contains(&"y".to_string()));
        assert!(
            !essential.contains(&"noise".to_string()),
            "noise is not essential"
        );
    }

    #[test]
    fn test_essential_variables_all_essential() {
        let cex = Counterexample::new(vec![
            ("a".to_string(), CounterexampleValue::Bool(true)),
            ("b".to_string(), CounterexampleValue::Bool(false)),
        ]);

        let essential = essential_variables(&cex, &|test_cex| {
            // Need both a and b
            if test_cex.assignments.len() >= 2 {
                TestOutcome::Fail
            } else {
                TestOutcome::Pass
            }
        });

        assert_eq!(essential.len(), 2);
    }

    #[test]
    fn test_essential_variables_none_essential() {
        let cex = Counterexample::new(vec![
            ("a".to_string(), CounterexampleValue::Uint(1)),
            ("b".to_string(), CounterexampleValue::Uint(2)),
        ]);

        // Property always fails regardless of variables
        let essential = essential_variables(&cex, &|_| TestOutcome::Fail);
        assert!(
            essential.is_empty(),
            "no variable is essential if removing any still fails"
        );
    }

    #[test]
    fn test_essential_variables_empty_counterexample() {
        let cex = Counterexample::new(vec![]);
        let essential = essential_variables(&cex, &|_| TestOutcome::Fail);
        assert!(essential.is_empty());
    }

    // --- Formula simplification tests ---

    #[test]
    fn test_simplify_not_true() {
        let f = Formula::Not(Box::new(Formula::Bool(true)));
        assert_eq!(simplify_formula(&f), Formula::Bool(false));
    }

    #[test]
    fn test_simplify_not_false() {
        let f = Formula::Not(Box::new(Formula::Bool(false)));
        assert_eq!(simplify_formula(&f), Formula::Bool(true));
    }

    #[test]
    fn test_simplify_double_negation() {
        let inner = Formula::Var("x".to_string(), Sort::Bool);
        let f = Formula::Not(Box::new(Formula::Not(Box::new(inner.clone()))));
        assert_eq!(simplify_formula(&f), inner);
    }

    #[test]
    fn test_simplify_and_empty() {
        let f = Formula::And(vec![]);
        assert_eq!(simplify_formula(&f), Formula::Bool(true));
    }

    #[test]
    fn test_simplify_or_empty() {
        let f = Formula::Or(vec![]);
        assert_eq!(simplify_formula(&f), Formula::Bool(false));
    }

    #[test]
    fn test_simplify_and_singleton() {
        let x = Formula::Var("x".to_string(), Sort::Bool);
        let f = Formula::And(vec![x.clone()]);
        assert_eq!(simplify_formula(&f), x);
    }

    #[test]
    fn test_simplify_or_singleton() {
        let x = Formula::Var("x".to_string(), Sort::Bool);
        let f = Formula::Or(vec![x.clone()]);
        assert_eq!(simplify_formula(&f), x);
    }

    #[test]
    fn test_simplify_and_with_false() {
        let x = Formula::Var("x".to_string(), Sort::Bool);
        let f = Formula::And(vec![x, Formula::Bool(false)]);
        assert_eq!(simplify_formula(&f), Formula::Bool(false));
    }

    #[test]
    fn test_simplify_or_with_true() {
        let x = Formula::Var("x".to_string(), Sort::Bool);
        let f = Formula::Or(vec![x, Formula::Bool(true)]);
        assert_eq!(simplify_formula(&f), Formula::Bool(true));
    }

    #[test]
    fn test_simplify_and_removes_true() {
        let x = Formula::Var("x".to_string(), Sort::Bool);
        let y = Formula::Var("y".to_string(), Sort::Bool);
        let f = Formula::And(vec![Formula::Bool(true), x.clone(), Formula::Bool(true), y.clone()]);
        let result = simplify_formula(&f);
        assert_eq!(result, Formula::And(vec![x, y]));
    }

    #[test]
    fn test_simplify_or_removes_false() {
        let x = Formula::Var("x".to_string(), Sort::Bool);
        let y = Formula::Var("y".to_string(), Sort::Bool);
        let f = Formula::Or(vec![Formula::Bool(false), x.clone(), Formula::Bool(false), y.clone()]);
        let result = simplify_formula(&f);
        assert_eq!(result, Formula::Or(vec![x, y]));
    }

    #[test]
    fn test_simplify_implies_false_antecedent() {
        let x = Formula::Var("x".to_string(), Sort::Bool);
        let f = Formula::Implies(Box::new(Formula::Bool(false)), Box::new(x));
        assert_eq!(simplify_formula(&f), Formula::Bool(true));
    }

    #[test]
    fn test_simplify_implies_true_consequent() {
        let x = Formula::Var("x".to_string(), Sort::Bool);
        let f = Formula::Implies(Box::new(x), Box::new(Formula::Bool(true)));
        assert_eq!(simplify_formula(&f), Formula::Bool(true));
    }

    #[test]
    fn test_simplify_implies_true_antecedent() {
        let x = Formula::Var("x".to_string(), Sort::Bool);
        let f = Formula::Implies(Box::new(Formula::Bool(true)), Box::new(x.clone()));
        assert_eq!(simplify_formula(&f), x);
    }

    #[test]
    fn test_simplify_atom_unchanged() {
        let f = Formula::Var("x".to_string(), Sort::Bool);
        assert_eq!(simplify_formula(&f), f);
    }

    #[test]
    fn test_simplify_nested() {
        // And(true, Not(false), Or(false, x)) => And(true, true, x) => x
        let x = Formula::Var("x".to_string(), Sort::Bool);
        let f = Formula::And(vec![
            Formula::Bool(true),
            Formula::Not(Box::new(Formula::Bool(false))),
            Formula::Or(vec![Formula::Bool(false), x.clone()]),
        ]);
        let result = simplify_formula(&f);
        assert_eq!(result, x);
    }

    // --- MinimizationResult tests ---

    #[test]
    fn test_minimization_result_reduction_ratio() {
        let result = MinimizationResult::new(vec![1, 2], 10, 2, 5);
        assert!((result.reduction_ratio - 0.8).abs() < f64::EPSILON);
    }

    #[test]
    fn test_minimization_result_no_reduction() {
        let result = MinimizationResult::new(vec![1, 2, 3], 3, 3, 0);
        assert!((result.reduction_ratio - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_minimization_result_zero_original() {
        let result: MinimizationResult<Vec<i32>> = MinimizationResult::new(vec![], 0, 0, 0);
        assert!((result.reduction_ratio - 0.0).abs() < f64::EPSILON);
    }
}
