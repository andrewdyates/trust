// trust-testgen: Generate Rust test cases from verification counterexamples
//
// When a solver returns a counterexample (SAT model), we convert the concrete
// variable assignments into a #[test] function that reproduces the violation.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Counterexample, CounterexampleValue, VcKind};
use std::fmt::Write;

use crate::{sanitize_ident, vc_kind_suffix, GeneratedTest};

/// Metadata for generating a test from a counterexample.
pub struct CounterexampleTestInput<'a> {
    /// The counterexample with concrete variable assignments.
    pub counterexample: &'a Counterexample,
    /// The kind of verification condition that was violated.
    pub vc_kind: &'a VcKind,
    /// Fully qualified function name (e.g., `my_crate::math::divide`).
    pub function_path: &'a str,
}

/// Generate a `#[test]` function from a counterexample.
///
/// The generated test instantiates the counterexample's variable assignments
/// and exercises the function under conditions that trigger the violation.
#[must_use]
pub fn generate_test_from_counterexample(input: &CounterexampleTestInput<'_>) -> GeneratedTest {
    let sanitized = sanitize_ident(input.function_path);
    let kind_suffix = vc_kind_suffix(input.vc_kind);
    let name = format!("test_cex_{sanitized}_{kind_suffix}");

    let should_panic = should_generate_panic_test(input.vc_kind);
    let (boundary_values, body) = build_test_body(input);

    let code = if should_panic {
        format!(
            "#[test]\n#[should_panic]\nfn {name}() {{\n{body}\n}}"
        )
    } else {
        format!(
            "#[test]\nfn {name}() {{\n{body}\n}}"
        )
    };

    GeneratedTest { name, code, boundary_values }
}

/// Whether this VcKind violation should produce a `#[should_panic]` test.
fn should_generate_panic_test(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::ArithmeticOverflow { .. }
            | VcKind::DivisionByZero
            | VcKind::RemainderByZero
            | VcKind::IndexOutOfBounds
            | VcKind::SliceBoundsCheck
            | VcKind::NegationOverflow { .. }
            | VcKind::ShiftOverflow { .. }
            | VcKind::Unreachable
    )
}

/// Build the test function body and extract boundary value strings.
fn build_test_body(input: &CounterexampleTestInput<'_>) -> (Vec<String>, String) {
    let assignments = format_assignments(&input.counterexample.assignments);
    let boundary_values: Vec<String> = input
        .counterexample
        .assignments
        .iter()
        .map(|(name, val)| format!("{name} = {val}"))
        .collect();

    let mut body = match input.vc_kind {
        VcKind::ArithmeticOverflow { op, .. } => {
            build_overflow_body(&assignments, op)
        }
        VcKind::DivisionByZero => {
            build_div_zero_body(&assignments)
        }
        VcKind::RemainderByZero => {
            build_rem_zero_body(&assignments)
        }
        VcKind::IndexOutOfBounds => {
            build_index_oob_body(&assignments)
        }
        VcKind::SliceBoundsCheck => {
            build_slice_bounds_body(&assignments)
        }
        VcKind::NegationOverflow { .. } => {
            build_negation_body(&assignments)
        }
        VcKind::ShiftOverflow { op, .. } => {
            build_shift_body(&assignments, op)
        }
        VcKind::Assertion { message } => {
            build_assertion_body(&assignments, message, input.function_path)
        }
        VcKind::Precondition { callee } => {
            build_precondition_body(&assignments, callee, input.function_path)
        }
        VcKind::Postcondition => {
            build_postcondition_body(&assignments, input.function_path)
        }
        _ => build_generic_body(&assignments, input.vc_kind, input.function_path),
    };

    // Append a call to the function under test using counterexample values
    let func_call = build_function_call(input);
    body.push_str(&func_call);

    (boundary_values, body)
}

/// Build a call to the function under test using counterexample variable names.
fn build_function_call(input: &CounterexampleTestInput<'_>) -> String {
    let sanitized_func = sanitize_ident(input.function_path);
    let args: Vec<String> = input
        .counterexample
        .assignments
        .iter()
        .map(|(name, _)| sanitize_ident(name))
        .collect();
    let args_str = args.join(", ");
    format!(
        "\n    // Call the function under test with counterexample values\n\
         \x20   let _ = {sanitized_func}({args_str});"
    )
}

/// Format counterexample assignments as `let` bindings.
fn format_assignments(assignments: &[(String, CounterexampleValue)]) -> String {
    let mut lines = String::new();
    for (name, val) in assignments {
        let sanitized = sanitize_ident(name);
        let (rust_val, ty_suffix) = value_to_rust(val);
        let _ = writeln!(lines, 
            "    let {sanitized}{ty_suffix} = {rust_val};"
        );
    }
    lines
}

/// Convert a `CounterexampleValue` to a Rust literal and optional type suffix.
fn value_to_rust(val: &CounterexampleValue) -> (String, &'static str) {
    match val {
        CounterexampleValue::Bool(b) => (format!("{b}"), ": bool"),
        CounterexampleValue::Int(n) => (format!("{n}"), ": i64"),
        CounterexampleValue::Uint(n) => (format!("{n}"), ": u64"),
        CounterexampleValue::Float(n) => {
            // Ensure the float literal always has a decimal point.
            let s = format!("{n}");
            let s = if s.contains('.') { s } else { format!("{s}.0") };
            (s, ": f64")
        }
        _ => ("unknown".to_string(), "unknown"),
    }
}

// ---------------------------------------------------------------------------
// Per-VcKind body builders
// ---------------------------------------------------------------------------

fn build_overflow_body(assignments: &str, op: &trust_types::BinOp) -> String {
    let op_str = match op {
        trust_types::BinOp::Add => "+",
        trust_types::BinOp::Sub => "-",
        trust_types::BinOp::Mul => "*",
        _ => "/* op */",
    };
    format!(
        "    // Counterexample: arithmetic overflow ({op_str})\n\
         {assignments}\
         \x20   // These values trigger overflow in debug mode:\n\
         \x20   // Uncomment the next line to observe the panic.\n\
         \x20   // let _ = first_operand {op_str} second_operand;\n\
         \x20   panic!(\"counterexample triggers arithmetic overflow\");"
    )
}

fn build_div_zero_body(assignments: &str) -> String {
    format!(
        "    // Counterexample: division by zero\n\
         {assignments}\
         \x20   // The divisor is zero in this counterexample.\n\
         \x20   let _ = 1_i64 / 0_i64;"
    )
}

fn build_rem_zero_body(assignments: &str) -> String {
    format!(
        "    // Counterexample: remainder by zero\n\
         {assignments}\
         \x20   // The divisor is zero in this counterexample.\n\
         \x20   let _ = 1_i64 % 0_i64;"
    )
}

fn build_index_oob_body(assignments: &str) -> String {
    format!(
        "    // Counterexample: index out of bounds\n\
         {assignments}\
         \x20   // The index exceeds array length in this counterexample.\n\
         \x20   let data: Vec<u8> = vec![0];\n\
         \x20   let _ = data[data.len()];"
    )
}

fn build_slice_bounds_body(assignments: &str) -> String {
    format!(
        "    // Counterexample: slice bounds check failed\n\
         {assignments}\
         \x20   // The slice range is invalid in this counterexample.\n\
         \x20   let data: Vec<u8> = vec![0];\n\
         \x20   let _ = &data[0..data.len() + 1];"
    )
}

fn build_negation_body(assignments: &str) -> String {
    format!(
        "    // Counterexample: negation overflow\n\
         {assignments}\
         \x20   // Negating MIN overflows in debug mode.\n\
         \x20   panic!(\"counterexample triggers negation overflow\");"
    )
}

fn build_shift_body(assignments: &str, op: &trust_types::BinOp) -> String {
    let dir = match op {
        trust_types::BinOp::Shl => "left",
        trust_types::BinOp::Shr => "right",
        _ => "unknown",
    };
    format!(
        "    // Counterexample: shift {dir} overflow\n\
         {assignments}\
         \x20   // The shift amount exceeds bit width.\n\
         \x20   panic!(\"counterexample triggers shift overflow\");"
    )
}

fn build_assertion_body(assignments: &str, message: &str, func_path: &str) -> String {
    format!(
        "    // Counterexample: assertion violation in {func_path}\n\
         \x20   // Assertion: {message}\n\
         {assignments}\
         \x20   // These variable assignments violate the assertion.\n\
         \x20   // Call the function with these inputs to reproduce.\n\
         \x20   // PLACEHOLDER: wire up actual function call for {func_path}\n\
         \x20   assert!(false, \"counterexample violates assertion: {message}\");"
    )
}

fn build_precondition_body(
    assignments: &str,
    callee: &str,
    func_path: &str,
) -> String {
    format!(
        "    // Counterexample: precondition violation in {func_path}\n\
         \x20   // Callee: {callee}\n\
         {assignments}\
         \x20   // These inputs violate the precondition of `{callee}`.\n\
         \x20   // PLACEHOLDER: wire up actual call for {func_path} -> {callee}\n\
         \x20   assert!(false, \"counterexample violates precondition of {callee}\");"
    )
}

fn build_postcondition_body(assignments: &str, func_path: &str) -> String {
    format!(
        "    // Counterexample: postcondition violation in {func_path}\n\
         {assignments}\
         \x20   // These inputs produce a return value that violates the postcondition.\n\
         \x20   // PLACEHOLDER: wire up actual function call for {func_path}\n\
         \x20   assert!(false, \"counterexample violates postcondition of {func_path}\");"
    )
}

fn build_generic_body(
    assignments: &str,
    kind: &VcKind,
    func_path: &str,
) -> String {
    let desc = kind.description();
    format!(
        "    // Counterexample: {desc} in {func_path}\n\
         {assignments}\
         \x20   // These variable assignments demonstrate the violation.\n\
         \x20   // Manual review required — this VC kind ({desc}) needs\n\
         \x20   // domain-specific test logic.\n\
         \x20   assert!(false, \"counterexample demonstrates: {desc}\");"
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::BinOp;

    fn make_cex(vars: &[(&str, CounterexampleValue)]) -> Counterexample {
        Counterexample::new(
            vars.iter()
                .map(|(name, val)| (name.to_string(), val.clone()))
                .collect(),
        )
    }

    #[test]
    fn test_overflow_cex_generates_should_panic() {
        let cex = make_cex(&[
            ("a", CounterexampleValue::Int(i128::from(i64::MAX))),
            ("b", CounterexampleValue::Int(1)),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (trust_types::Ty::i32(), trust_types::Ty::i32()),
            },
            function_path: "my_crate::add",
        };

        let test = generate_test_from_counterexample(&input);
        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("test_cex_my_crate__add_arithmetic_overflow"));
        assert!(test.code.contains("arithmetic overflow"));
        assert_eq!(test.boundary_values.len(), 2);
    }

    #[test]
    fn test_division_by_zero_cex() {
        let cex = make_cex(&[
            ("divisor", CounterexampleValue::Int(0)),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::DivisionByZero,
            function_path: "math::divide",
        };

        let test = generate_test_from_counterexample(&input);
        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("division by zero"));
        assert!(test.code.contains("let divisor: i64 = 0;"));
    }

    #[test]
    fn test_remainder_by_zero_cex() {
        let cex = make_cex(&[
            ("divisor", CounterexampleValue::Uint(0)),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::RemainderByZero,
            function_path: "math::modulo",
        };

        let test = generate_test_from_counterexample(&input);
        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("remainder by zero"));
    }

    #[test]
    fn test_index_oob_cex() {
        let cex = make_cex(&[
            ("idx", CounterexampleValue::Uint(10)),
            ("len", CounterexampleValue::Uint(5)),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::IndexOutOfBounds,
            function_path: "buffer::get",
        };

        let test = generate_test_from_counterexample(&input);
        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("index out of bounds"));
    }

    #[test]
    fn test_assertion_cex_no_should_panic() {
        let cex = make_cex(&[
            ("x", CounterexampleValue::Int(-1)),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::Assertion { message: "x >= 0".into() },
            function_path: "lib::validate",
        };

        let test = generate_test_from_counterexample(&input);
        assert!(!test.code.contains("#[should_panic]"));
        assert!(test.code.contains("x >= 0"));
        assert!(test.code.contains("let x: i64 = -1;"));
    }

    #[test]
    fn test_postcondition_cex() {
        let cex = make_cex(&[
            ("input", CounterexampleValue::Uint(0)),
            ("result", CounterexampleValue::Uint(0)),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::Postcondition,
            function_path: "api::process",
        };

        let test = generate_test_from_counterexample(&input);
        assert!(!test.code.contains("#[should_panic]"));
        assert!(test.code.contains("postcondition"));
        assert!(test.code.contains("api::process"));
    }

    #[test]
    fn test_precondition_cex_includes_callee() {
        let cex = make_cex(&[
            ("n", CounterexampleValue::Int(-5)),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::Precondition { callee: "sqrt".into() },
            function_path: "math::compute",
        };

        let test = generate_test_from_counterexample(&input);
        assert!(test.code.contains("sqrt"));
        assert!(test.code.contains("precondition"));
    }

    #[test]
    fn test_float_value_has_decimal() {
        let cex = make_cex(&[
            ("val", CounterexampleValue::Float(42.0)),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::Assertion { message: "val > 0".into() },
            function_path: "f",
        };

        let test = generate_test_from_counterexample(&input);
        // Float literal should have a decimal point
        assert!(test.code.contains("42"));
        assert!(test.code.contains(": f64"));
    }

    #[test]
    fn test_bool_value_rendering() {
        let cex = make_cex(&[
            ("flag", CounterexampleValue::Bool(false)),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::Assertion { message: "flag".into() },
            function_path: "check",
        };

        let test = generate_test_from_counterexample(&input);
        assert!(test.code.contains("let flag: bool = false;"));
    }

    #[test]
    fn test_empty_counterexample() {
        let cex = make_cex(&[]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::Unreachable,
            function_path: "unreachable_fn",
        };

        let test = generate_test_from_counterexample(&input);
        assert!(test.code.contains("#[should_panic]"));
        assert!(test.boundary_values.is_empty());
    }

    #[test]
    fn test_generic_vc_kind_body() {
        let cex = make_cex(&[
            ("state", CounterexampleValue::Int(3)),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::DeadState { state: "S3".into() },
            function_path: "fsm::step",
        };

        let test = generate_test_from_counterexample(&input);
        assert!(test.code.contains("dead state"));
        assert!(test.code.contains("Manual review required"));
    }

    #[test]
    fn test_sanitizes_special_chars_in_var_names() {
        let cex = make_cex(&[
            ("my::var.field", CounterexampleValue::Int(42)),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::DivisionByZero,
            function_path: "f",
        };

        let test = generate_test_from_counterexample(&input);
        // Special chars should be sanitized to underscores
        assert!(test.code.contains("my__var_field"));
    }

    #[test]
    fn test_shift_overflow_cex() {
        let cex = make_cex(&[
            ("val", CounterexampleValue::Uint(1)),
            ("shift", CounterexampleValue::Uint(64)),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: trust_types::Ty::Int { width: 64, signed: false },
                shift_ty: trust_types::Ty::u32(),
            },
            function_path: "bits::shift_left",
        };

        let test = generate_test_from_counterexample(&input);
        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("shift left overflow"));
    }

    #[test]
    fn test_negation_overflow_cex() {
        let cex = make_cex(&[
            ("val", CounterexampleValue::Int(i128::from(i64::MIN))),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::NegationOverflow { ty: trust_types::Ty::i32() },
            function_path: "math::negate",
        };

        let test = generate_test_from_counterexample(&input);
        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("negation overflow"));
    }

    #[test]
    fn test_slice_bounds_cex() {
        let cex = make_cex(&[
            ("start", CounterexampleValue::Uint(3)),
            ("end", CounterexampleValue::Uint(10)),
            ("len", CounterexampleValue::Uint(5)),
        ]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::SliceBoundsCheck,
            function_path: "slice::get_range",
        };

        let test = generate_test_from_counterexample(&input);
        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("slice bounds"));
    }

    #[test]
    fn test_name_format() {
        let cex = make_cex(&[("x", CounterexampleValue::Int(0))]);
        let input = CounterexampleTestInput {
            counterexample: &cex,
            vc_kind: &VcKind::DivisionByZero,
            function_path: "crate::module::func",
        };

        let test = generate_test_from_counterexample(&input);
        assert_eq!(test.name, "test_cex_crate__module__func_division_by_zero");
    }
}
