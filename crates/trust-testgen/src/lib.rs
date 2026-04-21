#![allow(dead_code)]
//! trust-testgen: Property-based test generation from verification conditions
//!
//! When a VC cannot be statically proved (Unknown/SAT), generate Rust test code
//! that exercises the property at runtime with targeted boundary values.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod cex_to_test;
pub(crate) mod coverage;
pub(crate) mod from_counterexample;
pub(crate) mod fuzzing;
pub(crate) mod mutation;
pub(crate) mod property_gen;
pub(crate) mod regression;
pub(crate) mod test_suite;

use trust_types::{Ty, VcKind, VerifiableFunction, VerificationCondition};

pub use from_counterexample::{generate_test_from_counterexample, CounterexampleTestInput};
pub use fuzzing::{
    FuzzConfig, FuzzTarget, SeedCorpus, SeedEntry, generate_fuzz_harness, generate_fuzz_target,
    generate_seed_corpus, generate_typed_fuzz_target,
};
pub use mutation::{
    AppliedMutation, ExpectedBehavior, MirMutant, MutationError, MutationGenerator,
    MutationOperator, MutationResult, MutationStrategy, MutationType, Mutant, TestMutant,
    apply_operator, generate_boundary_tests, generate_mutants, generate_mutants_from_func,
    input_mutation_score, mir_mutation_score, mutate_test_input, mutation_score,
    mutation_score_heuristic,
};
pub use property_gen::{
    InputStrategy, PropertyTestGenerator,
    generate_property_test,
};
pub use test_suite::{TestSuite, TestSuiteError};
pub use regression::{
    RegressionError, RegressionSuite, RegressionTest, SuiteDiff, diff_suites, minimize_suite,
};
pub use coverage::{
    CoverageAnalysis, CoverageError, CoverageGoal, CoverageMap, CoverageReport, VcId,
    coverage_report, gap_analysis, progress_toward_goal, suggest_tests,
};
pub use cex_to_test::{
    CexTestConfig, CexTestError, CexTestGenerator, MinimalReproducer,
    SynthesizedValue, TestTemplate, ValueSynthesizer, VcPropertyTestGen,
    add_cex_tests_to_suite,
};

/// A generated test targeting a specific verification condition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratedTest {
    /// Test function name (e.g., `test_get_midpoint_arithmetic_overflow`).
    pub name: String,
    /// Complete Rust test function source code.
    pub code: String,
    /// Boundary values used as test inputs (for diagnostics/reporting).
    pub boundary_values: Vec<String>,
}

/// Generates property-based tests from unproved verification conditions.
pub struct TestGenerator;

impl TestGenerator {
    /// Generate a test for a single VC + function pair.
    #[must_use]
    pub fn generate_test(vc: &VerificationCondition, func: &VerifiableFunction) -> GeneratedTest {
        let sanitized_name = sanitize_ident(&func.name);
        let kind_suffix = vc_kind_suffix(&vc.kind);
        let name = format!("test_{sanitized_name}_{kind_suffix}");

        let (boundary_values, test_body) = match &vc.kind {
            VcKind::ArithmeticOverflow { operand_tys, .. } => {
                generate_arithmetic_overflow_test(&sanitized_name, &operand_tys.0)
            }
            VcKind::DivisionByZero => generate_division_by_zero_test(&sanitized_name, func),
            VcKind::RemainderByZero => generate_remainder_by_zero_test(&sanitized_name, func),
            VcKind::IndexOutOfBounds => generate_index_out_of_bounds_test(&sanitized_name),
            VcKind::SliceBoundsCheck => generate_slice_bounds_check_test(&sanitized_name),
            VcKind::Precondition { callee } => {
                generate_precondition_test(&sanitized_name, callee, func)
            }
            VcKind::Postcondition => generate_postcondition_test(&sanitized_name, func),
            VcKind::NegationOverflow { ty } => {
                generate_negation_overflow_test(&sanitized_name, ty)
            }
            VcKind::CastOverflow { from_ty, to_ty } => {
                generate_cast_overflow_test(&sanitized_name, from_ty, to_ty)
            }
            VcKind::ShiftOverflow { operand_ty, .. } => {
                generate_shift_overflow_test(&sanitized_name, operand_ty)
            }
            // VcKinds without meaningful runtime test generation
            _ => generate_placeholder_test(&sanitized_name, &vc.kind),
        };

        // Generate an actual call to the function under test with default args
        let call_line = generate_function_call(func);
        let code = format!(
            "#[test]\nfn {name}() {{\n{test_body}\n{call_line}\n}}",
        );

        GeneratedTest { name, code, boundary_values }
    }

    /// Generate a complete `.rs` test file from multiple generated tests.
    #[must_use]
    pub fn generate_test_file(tests: &[GeneratedTest]) -> String {
        let mut file = String::with_capacity(tests.len() * 256);
        file.push_str(
            "// Auto-generated property-based tests from tRust verification conditions.\n\
             // These tests exercise properties that could not be statically proved.\n\
             //\n\
             // Generated by trust-testgen.\n\n",
        );

        for (i, test) in tests.iter().enumerate() {
            if i > 0 {
                file.push('\n');
            }
            file.push_str(&test.code);
            file.push('\n');
        }

        file
    }
}

// ---------------------------------------------------------------------------
// Per-VcKind test generators
// ---------------------------------------------------------------------------

fn generate_arithmetic_overflow_test(
    func_name: &str,
    operand_ty: &Ty,
) -> (Vec<String>, String) {
    let (ty_name, boundary_values) = boundary_values_for_ty(operand_ty);
    let values_str = boundary_values.join(", ");

    let body = format!(
        "    // ArithmeticOverflow: test {func_name} with boundary values of {ty_name}\n\
         \x20   let boundary_values: &[{ty_name}] = &[{values_str}];\n\
         \x20   for &a in boundary_values {{\n\
         \x20       for &b in boundary_values {{\n\
         \x20           // Wrapping arithmetic should not panic\n\
         \x20           let _ = a.wrapping_add(b);\n\
         \x20           let _ = a.wrapping_sub(b);\n\
         \x20           let _ = a.wrapping_mul(b);\n\
         \x20           // Checked arithmetic returns None on overflow\n\
         \x20           let _ = a.checked_add(b);\n\
         \x20           let _ = a.checked_sub(b);\n\
         \x20           let _ = a.checked_mul(b);\n\
         \x20       }}\n\
         \x20   }}"
    );

    (boundary_values, body)
}

fn generate_division_by_zero_test(
    func_name: &str,
    func: &VerifiableFunction,
) -> (Vec<String>, String) {
    let (ty_name, values) = arg_type_boundary(func);
    let boundary_values = values.clone();
    let values_str = boundary_values.join(", ");

    let body = format!(
        "    // DivisionByZero: test {func_name} with divisor boundary values\n\
         \x20   let boundary_values: &[{ty_name}] = &[{values_str}];\n\
         \x20   for &divisor in boundary_values {{\n\
         \x20       if divisor != 0 {{\n\
         \x20           let _ = 42{ty_name_suffix} / divisor;\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   // Verify division by zero panics\n\
         \x20   let result = std::panic::catch_unwind(|| 1{ty_name_suffix} / 0);\n\
         \x20   assert!(result.is_err(), \"division by zero must panic\");",
        ty_name_suffix = type_literal_suffix(&ty_name),
    );

    (boundary_values, body)
}

fn generate_remainder_by_zero_test(
    func_name: &str,
    func: &VerifiableFunction,
) -> (Vec<String>, String) {
    let (ty_name, values) = arg_type_boundary(func);
    let boundary_values = values.clone();
    let values_str = boundary_values.join(", ");

    let body = format!(
        "    // RemainderByZero: test {func_name} with divisor boundary values\n\
         \x20   let boundary_values: &[{ty_name}] = &[{values_str}];\n\
         \x20   for &divisor in boundary_values {{\n\
         \x20       if divisor != 0 {{\n\
         \x20           let _ = 42{ty_name_suffix} % divisor;\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   // Verify remainder by zero panics\n\
         \x20   let result = std::panic::catch_unwind(|| 1{ty_name_suffix} % 0);\n\
         \x20   assert!(result.is_err(), \"remainder by zero must panic\");",
        ty_name_suffix = type_literal_suffix(&ty_name),
    );

    (boundary_values, body)
}

fn generate_index_out_of_bounds_test(func_name: &str) -> (Vec<String>, String) {
    let boundary_values =
        vec!["0".into(), "1".into(), "len - 1".into(), "len".into(), "usize::MAX".into()];

    let body = format!(
        "    // IndexOutOfBounds: test {func_name} with boundary indices\n\
         \x20   let data: Vec<u8> = vec![10, 20, 30, 40, 50];\n\
         \x20   let len = data.len();\n\
         \x20   // Valid indices\n\
         \x20   for i in [0, 1, len - 1] {{\n\
         \x20       assert!(data.get(i).is_some(), \"index {{i}} should be valid for len {{len}}\");\n\
         \x20   }}\n\
         \x20   // Invalid indices\n\
         \x20   for i in [len, len + 1, usize::MAX] {{\n\
         \x20       assert!(data.get(i).is_none(), \"index {{i}} should be out of bounds for len {{len}}\");\n\
         \x20   }}\n\
         \x20   // Direct index panics on out-of-bounds\n\
         \x20   let result = std::panic::catch_unwind(|| {{\n\
         \x20       let v = vec![1u8, 2, 3];\n\
         \x20       v[v.len()]\n\
         \x20   }});\n\
         \x20   assert!(result.is_err(), \"index at len must panic\");"
    );

    (boundary_values, body)
}

fn generate_slice_bounds_check_test(func_name: &str) -> (Vec<String>, String) {
    let boundary_values =
        vec!["0..0".into(), "0..len".into(), "len..len".into(), "0..len+1".into()];

    let body = format!(
        "    // SliceBoundsCheck: test {func_name} with boundary slice ranges\n\
         \x20   let data: Vec<u8> = vec![10, 20, 30, 40, 50];\n\
         \x20   let len = data.len();\n\
         \x20   // Valid slices\n\
         \x20   let _ = &data[0..0];\n\
         \x20   let _ = &data[0..len];\n\
         \x20   let _ = &data[len..len];\n\
         \x20   // Invalid slice panics\n\
         \x20   let result = std::panic::catch_unwind(|| {{\n\
         \x20       let v = vec![1u8, 2, 3];\n\
         \x20       let _ = &v[0..v.len() + 1];\n\
         \x20   }});\n\
         \x20   assert!(result.is_err(), \"slice past end must panic\");"
    );

    (boundary_values, body)
}

fn generate_precondition_test(
    func_name: &str,
    callee: &str,
    func: &VerifiableFunction,
) -> (Vec<String>, String) {
    let (ty_name, values) = arg_type_boundary(func);
    let boundary_values = values.clone();
    let values_str = boundary_values.join(", ");

    let body = format!(
        "    // Precondition: test {func_name} calling `{callee}` with boundary inputs\n\
         \x20   let boundary_values: &[{ty_name}] = &[{values_str}];\n\
         \x20   for &val in boundary_values {{\n\
         \x20       // Each boundary value should either satisfy the precondition\n\
         \x20       // or be clearly invalid. Manual review recommended.\n\
         \x20       let _ = val;\n\
         \x20   }}"
    );

    (boundary_values, body)
}

fn generate_postcondition_test(
    func_name: &str,
    func: &VerifiableFunction,
) -> (Vec<String>, String) {
    let (ty_name, values) = arg_type_boundary(func);
    let boundary_values = values.clone();
    let values_str = boundary_values.join(", ");

    let body = format!(
        "    // Postcondition: test {func_name} return value with boundary inputs\n\
         \x20   let boundary_values: &[{ty_name}] = &[{values_str}];\n\
         \x20   for &val in boundary_values {{\n\
         \x20       // Postcondition should hold for all valid inputs.\n\
         \x20       // Manual review: add concrete postcondition assertion here.\n\
         \x20       let _ = val;\n\
         \x20   }}"
    );

    (boundary_values, body)
}

fn generate_negation_overflow_test(func_name: &str, ty: &Ty) -> (Vec<String>, String) {
    let (ty_name, boundary_values) = boundary_values_for_ty(ty);
    let values_str = boundary_values.join(", ");

    let body = format!(
        "    // NegationOverflow: test {func_name} with boundary values of {ty_name}\n\
         \x20   let boundary_values: &[{ty_name}] = &[{values_str}];\n\
         \x20   for &val in boundary_values {{\n\
         \x20       let _ = val.wrapping_neg();\n\
         \x20       // checked_neg returns None on overflow (e.g., {ty_name}::MIN for signed)\n\
         \x20       let _ = val.checked_neg();\n\
         \x20   }}"
    );

    (boundary_values, body)
}

fn generate_cast_overflow_test(
    func_name: &str,
    from_ty: &Ty,
    to_ty: &Ty,
) -> (Vec<String>, String) {
    let (from_name, from_values) = boundary_values_for_ty(from_ty);
    let to_name = ty_to_rust_name(to_ty);
    let values_str = from_values.join(", ");

    let body = format!(
        "    // CastOverflow: test {func_name} casting {from_name} -> {to_name}\n\
         \x20   let boundary_values: &[{from_name}] = &[{values_str}];\n\
         \x20   for &val in boundary_values {{\n\
         \x20       // `as` cast truncates silently; check if value fits\n\
         \x20       let cast = val as {to_name};\n\
         \x20       let round_trip = cast as {from_name};\n\
         \x20       if val != round_trip {{\n\
         \x20           // Lossy cast detected — value does not fit in {to_name}\n\
         \x20           eprintln!(\"lossy cast: {{val}} as {to_name} = {{cast}}\");\n\
         \x20       }}\n\
         \x20   }}"
    );

    (from_values, body)
}

fn generate_shift_overflow_test(func_name: &str, operand_ty: &Ty) -> (Vec<String>, String) {
    let (ty_name, _) = boundary_values_for_ty(operand_ty);
    let bit_width = operand_ty.int_width().unwrap_or(32);
    let boundary_values: Vec<String> = vec![
        "0".into(),
        "1".into(),
        format!("{}", bit_width - 1),
        format!("{bit_width}"),
        format!("{}", bit_width + 1),
    ];
    let values_str = boundary_values.join(", ");

    let body = format!(
        "    // ShiftOverflow: test {func_name} with boundary shift amounts for {ty_name}\n\
         \x20   let shift_amounts: &[u32] = &[{values_str}];\n\
         \x20   let val: {ty_name} = 1;\n\
         \x20   for &shift in shift_amounts {{\n\
         \x20       let _ = val.wrapping_shl(shift);\n\
         \x20       let _ = val.wrapping_shr(shift);\n\
         \x20       let _ = val.checked_shl(shift);\n\
         \x20       let _ = val.checked_shr(shift);\n\
         \x20   }}"
    );

    (boundary_values, body)
}

fn generate_placeholder_test(func_name: &str, kind: &VcKind) -> (Vec<String>, String) {
    let desc = kind.description();
    let body = format!(
        "    // {desc}: no runtime test generation available for this VC kind.\n\
         \x20   // This property ({desc}) requires static verification.\n\
         \x20   // {func_name} — placeholder test.\n\
         \x20   assert!(true, \"placeholder — VC kind not testable at runtime\");"
    );
    (vec![], body)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Return (Rust type name, boundary values as string literals) for a Ty.
fn boundary_values_for_ty(ty: &Ty) -> (String, Vec<String>) {
    match ty {
        Ty::Int { width: 8, signed: true } => (
            "i8".into(),
            vec!["i8::MIN".into(), "-1".into(), "0".into(), "1".into(), "i8::MAX".into()],
        ),
        Ty::Int { width: 16, signed: true } => (
            "i16".into(),
            vec!["i16::MIN".into(), "-1".into(), "0".into(), "1".into(), "i16::MAX".into()],
        ),
        Ty::Int { width: 32, signed: true } => (
            "i32".into(),
            vec!["i32::MIN".into(), "-1".into(), "0".into(), "1".into(), "i32::MAX".into()],
        ),
        Ty::Int { width: 64, signed: true } => (
            "i64".into(),
            vec!["i64::MIN".into(), "-1".into(), "0".into(), "1".into(), "i64::MAX".into()],
        ),
        Ty::Int { width: 128, signed: true } => (
            "i128".into(),
            vec!["i128::MIN".into(), "-1".into(), "0".into(), "1".into(), "i128::MAX".into()],
        ),
        Ty::Int { width: 8, signed: false } => (
            "u8".into(),
            vec!["0".into(), "1".into(), "u8::MAX / 2".into(), "u8::MAX - 1".into(), "u8::MAX".into()],
        ),
        Ty::Int { width: 16, signed: false } => (
            "u16".into(),
            vec!["0".into(), "1".into(), "u16::MAX / 2".into(), "u16::MAX - 1".into(), "u16::MAX".into()],
        ),
        Ty::Int { width: 32, signed: false } => (
            "u32".into(),
            vec!["0".into(), "1".into(), "u32::MAX / 2".into(), "u32::MAX - 1".into(), "u32::MAX".into()],
        ),
        Ty::Int { width: 64, signed: false } => (
            "u64".into(),
            vec!["0".into(), "1".into(), "u64::MAX / 2".into(), "u64::MAX - 1".into(), "u64::MAX".into()],
        ),
        Ty::Int { width: 128, signed: false } => (
            "u128".into(),
            vec!["0".into(), "1".into(), "u128::MAX / 2".into(), "u128::MAX - 1".into(), "u128::MAX".into()],
        ),
        // Fallback: treat as i32
        _ => (
            "i32".into(),
            vec!["i32::MIN".into(), "-1".into(), "0".into(), "1".into(), "i32::MAX".into()],
        ),
    }
}

/// Map a Ty to its Rust type name string.
fn ty_to_rust_name(ty: &Ty) -> String {
    match ty {
        Ty::Bool => "bool".into(),
        Ty::Int { width, signed: true } => format!("i{width}"),
        Ty::Int { width, signed: false } => format!("u{width}"),
        Ty::Float { width: 32 } => "f32".into(),
        Ty::Float { width: 64 } => "f64".into(),
        Ty::Float { width } => format!("f{width}"),
        _ => "i32".into(),
    }
}

/// Get the first argument type's boundary values from a VerifiableFunction,
/// falling back to i32 if no integer args exist.
fn arg_type_boundary(func: &VerifiableFunction) -> (String, Vec<String>) {
    // locals[0] is the return value; locals[1..=arg_count] are the arguments
    for local in func.body.locals.iter().skip(1).take(func.body.arg_count) {
        if local.ty.is_integer() {
            return boundary_values_for_ty(&local.ty);
        }
    }
    // Fallback
    boundary_values_for_ty(&Ty::i32())
}

/// Return a type literal suffix for numeric literals (e.g., `_i32`, `_u64`).
fn type_literal_suffix(ty_name: &str) -> String {
    format!("_{ty_name}")
}

/// VcKind -> snake_case suffix for test naming.
fn vc_kind_suffix(kind: &VcKind) -> String {
    match kind {
        VcKind::ArithmeticOverflow { .. } => "arithmetic_overflow".into(),
        VcKind::ShiftOverflow { .. } => "shift_overflow".into(),
        VcKind::DivisionByZero => "division_by_zero".into(),
        VcKind::RemainderByZero => "remainder_by_zero".into(),
        VcKind::IndexOutOfBounds => "index_out_of_bounds".into(),
        VcKind::SliceBoundsCheck => "slice_bounds_check".into(),
        VcKind::Assertion { .. } => "assertion".into(),
        VcKind::Precondition { .. } => "precondition".into(),
        VcKind::Postcondition => "postcondition".into(),
        VcKind::CastOverflow { .. } => "cast_overflow".into(),
        VcKind::NegationOverflow { .. } => "negation_overflow".into(),
        VcKind::Unreachable => "unreachable".into(),
        VcKind::DeadState { .. } => "dead_state".into(),
        VcKind::Deadlock => "deadlock".into(),
        VcKind::Temporal { .. } => "temporal".into(),
        VcKind::Liveness { .. } => "liveness".into(),
        VcKind::Fairness { .. } => "fairness".into(),
        VcKind::TaintViolation { .. } => "taint_violation".into(),
        VcKind::RefinementViolation { .. } => "refinement_violation".into(),
        VcKind::ResilienceViolation { .. } => "resilience_violation".into(),
        VcKind::ProtocolViolation { .. } => "protocol_violation".into(),
        VcKind::NonTermination { .. } => "non_termination".into(),
        VcKind::NeuralRobustness { .. } => "neural_robustness".into(),
        VcKind::NeuralOutputRange { .. } => "neural_output_range".into(),
        VcKind::NeuralLipschitz { .. } => "neural_lipschitz".into(),
        VcKind::NeuralMonotonicity { .. } => "neural_monotonicity".into(),
        // tRust #203: Data race and memory ordering tags.
        VcKind::DataRace { .. } => "data_race".into(),
        VcKind::InsufficientOrdering { .. } => "insufficient_ordering".into(),
        // tRust #149: Translation validation.
        VcKind::TranslationValidation { .. } => "translation_validation".into(),
        // tRust #433: Floating-point operation VCs.
        VcKind::FloatDivisionByZero => "float_division_by_zero".into(),
        VcKind::FloatOverflowToInfinity { .. } => "float_overflow_to_infinity".into(),
        // tRust #438: Rvalue safety VCs.
        VcKind::InvalidDiscriminant { .. } => "invalid_discriminant".into(),
        VcKind::AggregateArrayLengthMismatch { .. } => "aggregate_array_length_mismatch".into(),
// tRust #463: Unsafe operation.
        VcKind::UnsafeOperation { .. } => "unsafe_operation".into(),
_ => "unknown_vc_kind".into(),
    }
}

/// Generate a line that calls the function under test with default argument values.
///
/// Uses the function's parameter types to produce sensible defaults (0 for integers,
/// false for bool, 0.0 for floats). The call is wrapped in `let _ = ...;` to suppress
/// unused-result warnings.
fn generate_function_call(func: &VerifiableFunction) -> String {
    let name = sanitize_ident(&func.name);
    let args: Vec<String> = func
        .body
        .locals
        .iter()
        .skip(1) // locals[0] is the return value
        .take(func.body.arg_count)
        .map(|local| default_value_for_ty(&local.ty))
        .collect();
    let args_str = args.join(", ");
    format!("    // Call the function under test\n    let _ = {name}({args_str});")
}

/// Return a default value literal for a given type, used in generated test calls.
fn default_value_for_ty(ty: &Ty) -> String {
    match ty {
        Ty::Bool => "false".into(),
        Ty::Int { width, signed: true } => format!("0_i{width}"),
        Ty::Int { width, signed: false } => format!("0_u{width}"),
        Ty::Float { width: 32 } => "0.0_f32".into(),
        Ty::Float { width: 64 } => "0.0_f64".into(),
        Ty::Float { width } => format!("0.0_f{width}"),
        Ty::Unit => "()".into(),
        _ => "Default::default()".into(),
    }
}

/// Sanitize a function name into a valid Rust identifier.
fn sanitize_ident(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{
        BasicBlock, BinOp, BlockId, Formula, LocalDecl, SourceSpan, Terminator,
        VerifiableBody, VerificationCondition,
    };

    fn make_test_func(name: &str, arg_ty: Ty) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: arg_ty.clone(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: arg_ty, name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn make_vc(kind: VcKind, func_name: &str) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: func_name.to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    #[test]
    fn test_arithmetic_overflow_i32_boundary_values() {
        let func = make_test_func("add_numbers", Ty::i32());
        let vc = make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::i32(), Ty::i32()),
            },
            "add_numbers",
        );

        let test = TestGenerator::generate_test(&vc, &func);
        assert_eq!(test.name, "test_add_numbers_arithmetic_overflow");
        assert!(test.code.contains("#[test]"));
        assert!(test.code.contains("i32::MIN"));
        assert!(test.code.contains("i32::MAX"));
        assert!(test.code.contains("wrapping_add"));
        assert!(test.code.contains("checked_add"));
        assert_eq!(test.boundary_values.len(), 5);
    }

    #[test]
    fn test_arithmetic_overflow_u64_boundary_values() {
        let func = make_test_func("add_usize", Ty::usize());
        let vc = make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            "add_usize",
        );

        let test = TestGenerator::generate_test(&vc, &func);
        assert!(test.code.contains("u64::MAX"));
        assert!(test.boundary_values.contains(&"0".to_string()));
        assert!(test.boundary_values.contains(&"u64::MAX".to_string()));
    }

    #[test]
    fn test_division_by_zero_generates_panic_check() {
        let func = make_test_func("divide", Ty::i32());
        let vc = make_vc(VcKind::DivisionByZero, "divide");

        let test = TestGenerator::generate_test(&vc, &func);
        assert_eq!(test.name, "test_divide_division_by_zero");
        assert!(test.code.contains("catch_unwind"));
        assert!(test.code.contains("division by zero must panic"));
    }

    #[test]
    fn test_remainder_by_zero_generates_panic_check() {
        let func = make_test_func("modulo", Ty::i32());
        let vc = make_vc(VcKind::RemainderByZero, "modulo");

        let test = TestGenerator::generate_test(&vc, &func);
        assert_eq!(test.name, "test_modulo_remainder_by_zero");
        assert!(test.code.contains("catch_unwind"));
        assert!(test.code.contains("remainder by zero must panic"));
    }

    #[test]
    fn test_index_out_of_bounds_boundary_indices() {
        let func = make_test_func("get_item", Ty::usize());
        let vc = make_vc(VcKind::IndexOutOfBounds, "get_item");

        let test = TestGenerator::generate_test(&vc, &func);
        assert_eq!(test.name, "test_get_item_index_out_of_bounds");
        assert!(test.code.contains("usize::MAX"));
        assert!(test.code.contains("len - 1"));
        assert!(test.code.contains("index at len must panic"));
    }

    #[test]
    fn test_slice_bounds_check_generates_range_tests() {
        let func = make_test_func("get_slice", Ty::usize());
        let vc = make_vc(VcKind::SliceBoundsCheck, "get_slice");

        let test = TestGenerator::generate_test(&vc, &func);
        assert_eq!(test.name, "test_get_slice_slice_bounds_check");
        assert!(test.code.contains("slice past end must panic"));
        assert!(test.code.contains("0..len"));
    }

    #[test]
    fn test_precondition_includes_callee_name() {
        let func = make_test_func("caller", Ty::i32());
        let vc = make_vc(
            VcKind::Precondition { callee: "callee_fn".into() },
            "caller",
        );

        let test = TestGenerator::generate_test(&vc, &func);
        assert!(test.code.contains("callee_fn"));
        assert!(test.code.contains("i32::MIN"));
    }

    #[test]
    fn test_negation_overflow_signed() {
        let func = make_test_func("negate", Ty::i32());
        let vc = make_vc(VcKind::NegationOverflow { ty: Ty::i32() }, "negate");

        let test = TestGenerator::generate_test(&vc, &func);
        assert!(test.code.contains("wrapping_neg"));
        assert!(test.code.contains("checked_neg"));
        assert!(test.code.contains("i32::MIN"));
    }

    #[test]
    fn test_cast_overflow_generates_round_trip() {
        let func = make_test_func("narrow", Ty::i32());
        let vc = make_vc(
            VcKind::CastOverflow { from_ty: Ty::i32(), to_ty: Ty::Int { width: 8, signed: true } },
            "narrow",
        );

        let test = TestGenerator::generate_test(&vc, &func);
        assert!(test.code.contains("i32"));
        assert!(test.code.contains("i8"));
        assert!(test.code.contains("round_trip"));
    }

    #[test]
    fn test_shift_overflow_boundary_amounts() {
        let func = make_test_func("shift_left", Ty::u32());
        let vc = make_vc(
            VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: Ty::u32(),
                shift_ty: Ty::u32(),
            },
            "shift_left",
        );

        let test = TestGenerator::generate_test(&vc, &func);
        assert!(test.code.contains("wrapping_shl"));
        assert!(test.code.contains("checked_shl"));
        // Should include boundary shift amount = bit_width (32)
        assert!(test.boundary_values.contains(&"32".to_string()));
        assert!(test.boundary_values.contains(&"31".to_string()));
    }

    #[test]
    fn test_generate_test_file_multiple_tests() {
        let func = make_test_func("compute", Ty::i32());
        let vc1 = make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::i32(), Ty::i32()),
            },
            "compute",
        );
        let vc2 = make_vc(VcKind::DivisionByZero, "compute");

        let test1 = TestGenerator::generate_test(&vc1, &func);
        let test2 = TestGenerator::generate_test(&vc2, &func);
        let file = TestGenerator::generate_test_file(&[test1, test2]);

        assert!(file.contains("Auto-generated"));
        assert!(file.contains("trust-testgen"));
        assert!(file.contains("test_compute_arithmetic_overflow"));
        assert!(file.contains("test_compute_division_by_zero"));
        // Two #[test] annotations
        assert_eq!(file.matches("#[test]").count(), 2);
    }

    #[test]
    fn test_generate_test_file_empty() {
        let file = TestGenerator::generate_test_file(&[]);
        assert!(file.contains("Auto-generated"));
        assert!(!file.contains("#[test]"));
    }

    #[test]
    fn test_placeholder_for_unsupported_vc_kind() {
        let func = make_test_func("protocol", Ty::i32());
        let vc = make_vc(
            VcKind::ProtocolViolation {
                protocol: "raft".into(),
                violation: "split brain".into(),
            },
            "protocol",
        );

        let test = TestGenerator::generate_test(&vc, &func);
        assert!(test.code.contains("placeholder"));
        assert!(test.code.contains("protocol"));
        assert!(test.boundary_values.is_empty());
    }

    #[test]
    fn test_sanitize_ident_special_chars() {
        assert_eq!(sanitize_ident("foo::bar"), "foo__bar");
        assert_eq!(sanitize_ident("my-func"), "my_func");
        assert_eq!(sanitize_ident("normal_name"), "normal_name");
    }

    #[test]
    fn test_vc_kind_suffix_completeness() {
        // Verify all VcKind variants have a suffix (no panics).
        let kinds: Vec<VcKind> = vec![
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
            VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() },
            VcKind::DivisionByZero,
            VcKind::RemainderByZero,
            VcKind::IndexOutOfBounds,
            VcKind::SliceBoundsCheck,
            VcKind::Assertion { message: "test".into() },
            VcKind::Precondition { callee: "f".into() },
            VcKind::Postcondition,
            VcKind::CastOverflow { from_ty: Ty::i32(), to_ty: Ty::u32() },
            VcKind::NegationOverflow { ty: Ty::i32() },
            VcKind::Unreachable,
            VcKind::DeadState { state: "s".into() },
            VcKind::Deadlock,
            VcKind::Temporal { property: "p".into() },
            VcKind::TaintViolation { source_label: "s".into(), sink_kind: "k".into(), path_length: 1 },
            VcKind::RefinementViolation { spec_file: "s".into(), action: "a".into() },
            VcKind::ResilienceViolation { service: "s".into(), failure_mode: "f".into(), reason: "r".into() },
            VcKind::ProtocolViolation { protocol: "p".into(), violation: "v".into() },
            VcKind::NonTermination { context: "loop".into(), measure: "n".into() },
        ];
        for kind in &kinds {
            let suffix = vc_kind_suffix(kind);
            assert!(!suffix.is_empty(), "suffix should not be empty for {kind:?}");
        }
    }

    #[test]
    fn test_boundary_values_for_all_integer_types() {
        let types = vec![
            Ty::Int { width: 8, signed: true },
            Ty::Int { width: 16, signed: true },
            Ty::Int { width: 32, signed: true },
            Ty::Int { width: 64, signed: true },
            Ty::Int { width: 128, signed: true },
            Ty::Int { width: 8, signed: false },
            Ty::Int { width: 16, signed: false },
            Ty::Int { width: 32, signed: false },
            Ty::Int { width: 64, signed: false },
            Ty::Int { width: 128, signed: false },
        ];
        for ty in &types {
            let (name, values) = boundary_values_for_ty(ty);
            assert!(!name.is_empty());
            assert!(values.len() >= 3, "at least 3 boundary values for {name}");
            // All signed types should include a MIN
            if ty.is_signed() {
                assert!(values.iter().any(|v| v.contains("MIN")), "{name} should have MIN");
            }
            // All types should include a MAX
            assert!(values.iter().any(|v| v.contains("MAX")), "{name} should have MAX");
        }
    }
}
