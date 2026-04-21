// trust-testgen/mutation/input_mutation.rs: Input-level mutation for test generation
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use thiserror::Error;
use trust_types::{ConstValue, Ty};

// ---------------------------------------------------------------------------
// Input-level mutation: mutate concrete test inputs to generate new test cases
// ---------------------------------------------------------------------------

/// Error type for mutation operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum MutationError {
    /// The operator cannot be applied to the given value type.
    #[error("operator {operator:?} not applicable to value type")]
    IncompatibleOperator {
        operator: MutationOperator,
    },
    /// No mutations could be generated from the given inputs.
    #[error("no mutations generated: {reason}")]
    NoMutations {
        reason: String,
    },
}

/// Operators that transform concrete test input values into mutated variants.
///
/// These operators are applied to `ConstValue` inputs to create new test cases
/// that exercise boundary conditions and edge cases.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum MutationOperator {
    /// Negate the value (arithmetic negation for numbers, logical negation for bools).
    Negate,
    /// Shift toward the nearest type boundary (MIN, MAX, 0).
    BoundaryShift,
    /// Coerce to a different numeric width (e.g., i32 -> i8 truncation test).
    TypeCoerce,
    /// Replace with zero (or false for bools).
    ZeroSubst,
    /// Replace with the maximum value for the type.
    MaxSubst,
    /// Increment by one (wrapping).
    Increment,
    /// Decrement by one (wrapping).
    Decrement,
}

impl MutationOperator {
    /// All built-in operators.
    pub const ALL: &'static [MutationOperator] = &[
        MutationOperator::Negate,
        MutationOperator::BoundaryShift,
        MutationOperator::TypeCoerce,
        MutationOperator::ZeroSubst,
        MutationOperator::MaxSubst,
        MutationOperator::Increment,
        MutationOperator::Decrement,
    ];

    /// Human-readable name.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            MutationOperator::Negate => "negate",
            MutationOperator::BoundaryShift => "boundary_shift",
            MutationOperator::TypeCoerce => "type_coerce",
            MutationOperator::ZeroSubst => "zero_subst",
            MutationOperator::MaxSubst => "max_subst",
            MutationOperator::Increment => "increment",
            MutationOperator::Decrement => "decrement",
        }
    }
}

/// Configuration for input-level mutation test generation.
#[derive(Debug, Clone)]
pub struct MutationStrategy {
    /// Which operators to apply.
    pub(crate) operators: Vec<MutationOperator>,
    /// Maximum number of mutations to apply per original input value.
    pub(crate) max_mutations_per_input: usize,
    /// Deterministic seed for reproducibility.
    pub(crate) seed: u64,
}

impl Default for MutationStrategy {
    fn default() -> Self {
        Self {
            operators: MutationOperator::ALL.to_vec(),
            max_mutations_per_input: 4,
            seed: 0,
        }
    }
}

impl MutationStrategy {
    /// Create a strategy using only the specified operators.
    #[must_use]
    pub fn with_operators(operators: &[MutationOperator]) -> Self {
        Self {
            operators: operators.to_vec(),
            ..Default::default()
        }
    }
}

/// Expected behavior of a mutated test.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExpectedBehavior {
    /// The test should pass (the mutation preserves correctness).
    Pass,
    /// The test should fail or detect a difference.
    Fail,
    /// Unknown -- requires execution to determine.
    Unknown,
}

/// A single mutation applied to a test input.
#[derive(Debug, Clone)]
pub struct AppliedMutation {
    /// Which operator was used.
    pub(crate) operator: MutationOperator,
    /// The original value before mutation.
    pub(crate) original_value: ConstValue,
    /// The mutated value.
    pub(crate) mutated_value: ConstValue,
}

/// A test variant produced by mutating an existing test's inputs.
#[derive(Debug, Clone)]
pub struct TestMutant {
    /// Name of the original test this was derived from.
    pub(crate) original_test: String,
    /// The mutations applied to produce this variant.
    pub(crate) mutations_applied: Vec<AppliedMutation>,
    /// Expected behavior of this mutated test.
    pub(crate) expected_behavior: ExpectedBehavior,
    /// The mutated input values.
    pub(crate) mutated_inputs: Vec<ConstValue>,
}

impl TestMutant {
    /// Format as a human-readable description.
    #[must_use]
    pub fn describe(&self) -> String {
        let ops: Vec<&str> = self.mutations_applied.iter().map(|m| m.operator.name()).collect();
        format!(
            "mutant of `{}`: {} mutation(s) [{}], expected {:?}",
            self.original_test,
            self.mutations_applied.len(),
            ops.join(", "),
            self.expected_behavior,
        )
    }
}

/// Apply a single `MutationOperator` to a `ConstValue`, producing the mutated value.
///
/// Returns `Ok(mutated_value)` or `Err` if the operator is not applicable.
pub fn apply_operator(
    operator: MutationOperator,
    value: &ConstValue,
    ty: &Ty,
) -> Result<ConstValue, MutationError> {
    match (operator, value) {
        // --- Negate ---
        (MutationOperator::Negate, ConstValue::Int(n)) => Ok(ConstValue::Int(n.wrapping_neg())),
        (MutationOperator::Negate, ConstValue::Uint(n, w)) => {
            // For unsigned: negate via two's complement wrapping
            Ok(ConstValue::Uint(n.wrapping_neg(), *w))
        }
        (MutationOperator::Negate, ConstValue::Bool(b)) => Ok(ConstValue::Bool(!b)),
        (MutationOperator::Negate, ConstValue::Float(f)) => Ok(ConstValue::Float(-f)),

        // --- BoundaryShift ---
        (MutationOperator::BoundaryShift, ConstValue::Int(n)) => {
            // Shift toward nearest boundary: if positive -> MAX, if negative -> MIN, if 0 -> 1
            let width = ty.int_width().unwrap_or(32);
            let max_val = max_signed(width);
            let min_val = min_signed(width);
            let shifted = if *n > 0 {
                max_val
            } else if *n < 0 {
                min_val
            } else {
                1
            };
            Ok(ConstValue::Int(shifted))
        }
        (MutationOperator::BoundaryShift, ConstValue::Uint(n, w)) => {
            let width = ty.int_width().unwrap_or(32);
            let max_val = max_unsigned(width);
            let shifted = if *n == 0 { 1 } else { max_val };
            Ok(ConstValue::Uint(shifted, *w))
        }
        (MutationOperator::BoundaryShift, ConstValue::Bool(b)) => Ok(ConstValue::Bool(!b)),

        // --- TypeCoerce (truncation test) ---
        (MutationOperator::TypeCoerce, ConstValue::Int(n)) => {
            // Truncate to 8 bits to simulate narrow cast
            Ok(ConstValue::Int((*n as i8) as i128))
        }
        (MutationOperator::TypeCoerce, ConstValue::Uint(n, w)) => {
            Ok(ConstValue::Uint((*n as u8) as u128, *w))
        }

        // --- ZeroSubst ---
        (MutationOperator::ZeroSubst, ConstValue::Int(_)) => Ok(ConstValue::Int(0)),
        (MutationOperator::ZeroSubst, ConstValue::Uint(_, w)) => Ok(ConstValue::Uint(0, *w)),
        (MutationOperator::ZeroSubst, ConstValue::Bool(_)) => Ok(ConstValue::Bool(false)),
        (MutationOperator::ZeroSubst, ConstValue::Float(_)) => Ok(ConstValue::Float(0.0)),

        // --- MaxSubst ---
        (MutationOperator::MaxSubst, ConstValue::Int(_)) => {
            let width = ty.int_width().unwrap_or(32);
            Ok(ConstValue::Int(max_signed(width)))
        }
        (MutationOperator::MaxSubst, ConstValue::Uint(_, w)) => {
            let width = ty.int_width().unwrap_or(32);
            Ok(ConstValue::Uint(max_unsigned(width), *w))
        }
        (MutationOperator::MaxSubst, ConstValue::Bool(_)) => Ok(ConstValue::Bool(true)),

        // --- Increment ---
        (MutationOperator::Increment, ConstValue::Int(n)) => {
            Ok(ConstValue::Int(n.wrapping_add(1)))
        }
        (MutationOperator::Increment, ConstValue::Uint(n, w)) => {
            Ok(ConstValue::Uint(n.wrapping_add(1), *w))
        }

        // --- Decrement ---
        (MutationOperator::Decrement, ConstValue::Int(n)) => {
            Ok(ConstValue::Int(n.wrapping_sub(1)))
        }
        (MutationOperator::Decrement, ConstValue::Uint(n, w)) => {
            Ok(ConstValue::Uint(n.wrapping_sub(1), *w))
        }

        _ => Err(MutationError::IncompatibleOperator { operator }),
    }
}

/// Mutate a sequence of test inputs according to a strategy.
///
/// For each input value, applies each applicable operator (up to
/// `strategy.max_mutations_per_input`) and returns all `TestMutant` variants.
#[must_use]
pub fn mutate_test_input(
    test_name: &str,
    inputs: &[(ConstValue, Ty)],
    strategy: &MutationStrategy,
) -> Vec<TestMutant> {
    let mut mutants = Vec::new();

    for (idx, (value, ty)) in inputs.iter().enumerate() {
        let mut count = 0;

        for &operator in &strategy.operators {
            if count >= strategy.max_mutations_per_input {
                break;
            }

            if let Ok(mutated_value) = apply_operator(operator, value, ty) {
                // Skip no-op mutations (where the value doesn't change)
                if const_value_eq(&mutated_value, value) {
                    continue;
                }

                let mut mutated_inputs: Vec<ConstValue> =
                    inputs.iter().map(|(v, _)| v.clone()).collect();
                mutated_inputs[idx] = mutated_value.clone();

                mutants.push(TestMutant {
                    original_test: test_name.to_string(),
                    mutations_applied: vec![AppliedMutation {
                        operator,
                        original_value: value.clone(),
                        mutated_value,
                    }],
                    expected_behavior: ExpectedBehavior::Unknown,
                    mutated_inputs,
                });
                count += 1;
            }
        }
    }

    mutants
}

/// Generate boundary-condition test variants from a set of typed inputs.
///
/// For each input, produces edge-case variants: zero, max, min, +/-1 from current.
#[must_use]
pub fn generate_boundary_tests(
    test_name: &str,
    inputs: &[(ConstValue, Ty)],
) -> Vec<TestMutant> {
    let boundary_ops = [
        MutationOperator::ZeroSubst,
        MutationOperator::MaxSubst,
        MutationOperator::Increment,
        MutationOperator::Decrement,
        MutationOperator::BoundaryShift,
    ];
    let strategy = MutationStrategy {
        operators: boundary_ops.to_vec(),
        max_mutations_per_input: boundary_ops.len(),
        seed: 0,
    };
    mutate_test_input(test_name, inputs, &strategy)
}

/// Calculate the mutation score for input-level test mutants.
///
/// Score = (killed or fail-expected) / total.
/// Mutants with `ExpectedBehavior::Fail` count as killed.
/// Mutants with `ExpectedBehavior::Pass` count as survived.
/// Mutants with `ExpectedBehavior::Unknown` count as survived (conservative).
///
/// Returns a value in `[0.0, 1.0]`. Empty input returns `1.0`.
#[must_use]
pub fn input_mutation_score(mutants: &[TestMutant]) -> f64 {
    if mutants.is_empty() {
        return 1.0;
    }
    let killed = mutants
        .iter()
        .filter(|m| m.expected_behavior == ExpectedBehavior::Fail)
        .count();
    killed as f64 / mutants.len() as f64
}

// --- Helpers ---

/// Structural equality for `ConstValue` (which does not derive `PartialEq`
/// because it contains `f64`).
pub(super) fn const_value_eq(a: &ConstValue, b: &ConstValue) -> bool {
    match (a, b) {
        (ConstValue::Bool(x), ConstValue::Bool(y)) => x == y,
        (ConstValue::Int(x), ConstValue::Int(y)) => x == y,
        (ConstValue::Uint(x, _), ConstValue::Uint(y, _)) => x == y,
        (ConstValue::Float(x), ConstValue::Float(y)) => x.to_bits() == y.to_bits(),
        (ConstValue::Unit, ConstValue::Unit) => true,
        _ => false,
    }
}

fn max_signed(width: u32) -> i128 {
    match width {
        8 => i8::MAX as i128,
        16 => i16::MAX as i128,
        32 => i32::MAX as i128,
        64 => i64::MAX as i128,
        128 => i128::MAX,
        _ => i32::MAX as i128,
    }
}

fn min_signed(width: u32) -> i128 {
    match width {
        8 => i8::MIN as i128,
        16 => i16::MIN as i128,
        32 => i32::MIN as i128,
        64 => i64::MIN as i128,
        128 => i128::MIN,
        _ => i32::MIN as i128,
    }
}

pub(super) fn max_unsigned(width: u32) -> u128 {
    match width {
        8 => u8::MAX as u128,
        16 => u16::MAX as u128,
        32 => u32::MAX as u128,
        64 => u64::MAX as u128,
        128 => u128::MAX,
        _ => u32::MAX as u128,
    }
}
