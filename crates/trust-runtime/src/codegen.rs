// trust-runtime/codegen.rs: Generate Rust code snippets for runtime checks
//
// Produces `#[cfg(trust_runtime)]`-gated code for each check type.
// These snippets are intended to be inserted into generated code or
// used as MIR-level assertion templates.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0


use crate::{CheckStrategy, RuntimeCheck};
use crate::instrumentation::InstrumentationPlan;

/// Generated code snippet for a runtime check.
#[derive(Debug, Clone)]
pub(crate) struct CodeSnippet {
    /// The generated Rust code.
    pub code: String,
    /// Whether this should be `#[cfg(trust_runtime)]`-gated.
    pub cfg_gated: bool,
    /// Description of what this snippet checks.
    pub comment: String,
}

/// Generate a Rust code snippet for a single runtime check.
#[must_use]
pub(crate) fn generate_check_code(check: &RuntimeCheck) -> CodeSnippet {
    let (code, comment) = match &check.strategy {
        CheckStrategy::OverflowCheck { op } => (
            generate_overflow_check(*op),
            "overflow-checked arithmetic (panics in debug, wraps in release)".to_string(),
        ),
        CheckStrategy::BoundsCheck => (
            generate_bounds_check(&check.function, &check.location),
            format!(
                "index bounds check at {}:{}",
                check.location.file, check.location.line_start
            ),
        ),
        CheckStrategy::DivisorNonZero => (
            generate_division_check(&check.function, &check.location),
            format!(
                "division-by-zero check at {}:{}",
                check.location.file, check.location.line_start
            ),
        ),
        CheckStrategy::SliceRangeCheck => (
            generate_slice_check(&check.function, &check.location),
            format!(
                "slice bounds check at {}:{}",
                check.location.file, check.location.line_start
            ),
        ),
        CheckStrategy::PreserveAssertion { message } => (
            generate_preserved_assertion(message),
            format!("preserved assertion: {message}"),
        ),
        CheckStrategy::UnreachablePanic => (
            generate_unreachable_check(&check.function, &check.location),
            "unreachable code guard".to_string(),
        ),
        CheckStrategy::ShiftCheck => (
            generate_shift_check(),
            "shift overflow check".to_string(),
        ),
        CheckStrategy::NegationCheck => (
            generate_negation_check(),
            "negation overflow check".to_string(),
        ),
    };

    CodeSnippet {
        code,
        cfg_gated: true,
        comment,
    }
}

/// Generate all code snippets for an instrumentation plan.
#[must_use]
pub(crate) fn generate_plan_code(plan: &InstrumentationPlan) -> Vec<CodeSnippet> {
    plan.checks.iter().map(|ic| generate_check_code(&ic.check)).collect()
}

/// Wrap a code snippet in `#[cfg(trust_runtime)]` guard.
#[must_use]
pub(crate) fn wrap_cfg_gated(snippet: &CodeSnippet) -> String {
    if snippet.cfg_gated {
        format!(
            "// tRust: {}\n#[cfg(trust_runtime)]\n{{\n    {}\n}}",
            snippet.comment,
            snippet.code.replace('\n', "\n    ")
        )
    } else {
        format!("// tRust: {}\n{}", snippet.comment, snippet.code)
    }
}

// ---------------------------------------------------------------------------
// Code generation for each check type
// ---------------------------------------------------------------------------

fn generate_overflow_check(op: trust_types::BinOp) -> String {
    // tRust #767: Generate the correct checked_* method for each operation.
    let method = match op {
        trust_types::BinOp::Add => "checked_add",
        trust_types::BinOp::Sub => "checked_sub",
        trust_types::BinOp::Mul => "checked_mul",
        trust_types::BinOp::Shl => "checked_shl",
        trust_types::BinOp::Shr => "checked_shr",
        _ => "checked_add",
    };
    format!(
        "// Overflow check: panics in debug, wraps in release\n\
         debug_assert!(\n\
         \x20   lhs.{method}(rhs).is_some(),\n\
         \x20   \"tRust: arithmetic overflow detected in {{}}\",\n\
         \x20   core::any::type_name::<Self>()\n\
         );"
    )
}

fn generate_bounds_check(
    function: &str,
    location: &trust_types::SourceSpan,
) -> String {
    format!(
        concat!(
            "assert!(\n",
            "    index < len,\n",
            "    \"tRust: index out of bounds in `{}` at {}:{}: index {{}} >= len {{}}\",\n",
            "    index, len\n",
            ");"
        ),
        function, location.file, location.line_start
    )
}

fn generate_division_check(
    function: &str,
    location: &trust_types::SourceSpan,
) -> String {
    format!(
        concat!(
            "assert!(\n",
            "    divisor != 0,\n",
            "    \"tRust: division by zero in `{}` at {}:{}\"\n",
            ");"
        ),
        function, location.file, location.line_start
    )
}

fn generate_slice_check(
    function: &str,
    location: &trust_types::SourceSpan,
) -> String {
    format!(
        concat!(
            "assert!(\n",
            "    start <= end && end <= len,\n",
            "    \"tRust: slice bounds violation in `{}` at {}:{}: \
             start={{}}, end={{}}, len={{}}\",\n",
            "    start, end, len\n",
            ");"
        ),
        function, location.file, location.line_start
    )
}

fn generate_preserved_assertion(message: &str) -> String {
    format!(
        "assert!(\n    condition,\n    \"tRust: assertion failed: {}\"\n);",
        message.replace('"', "\\\"")
    )
}

fn generate_unreachable_check(
    function: &str,
    location: &trust_types::SourceSpan,
) -> String {
    format!(
        "unreachable!(\"tRust: unreachable code reached in `{}` at {}:{}\");",
        function, location.file, location.line_start
    )
}

fn generate_shift_check() -> String {
    concat!(
        "// Shift overflow check: shift distance must be < bit width\n",
        "debug_assert!(\n",
        "    shift_amount < bit_width,\n",
        "    \"tRust: shift overflow: shift amount {{}} >= bit width {{}}\",\n",
        "    shift_amount, bit_width\n",
        ");"
    )
    .to_string()
}

fn generate_negation_check() -> String {
    concat!(
        "// Negation overflow check: -MIN overflows for signed types\n",
        "debug_assert!(\n",
        "    value != Self::MIN,\n",
        "    \"tRust: negation overflow: cannot negate minimum value\"\n",
        ");"
    )
    .to_string()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckKind, CheckStrategy, RuntimeCheck};
    use trust_types::SourceSpan;

    fn span() -> SourceSpan {
        SourceSpan {
            file: "src/lib.rs".to_string(),
            line_start: 42,
            col_start: 5,
            line_end: 42,
            col_end: 30,
        }
    }

    fn make_check(kind: CheckKind, strategy: CheckStrategy) -> RuntimeCheck {
        RuntimeCheck {
            kind,
            location: span(),
            description: "test check".to_string(),
            strategy,
            function: "test_fn".to_string(),
        }
    }

    // -----------------------------------------------------------------------
    // Individual check code generation
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_overflow_check() {
        let check = make_check(
            CheckKind::ArithmeticOverflow,
            CheckStrategy::OverflowCheck { op: trust_types::BinOp::Add },
        );
        let snippet = generate_check_code(&check);
        assert!(snippet.code.contains("checked_add"));
        assert!(snippet.code.contains("debug_assert!"));
        assert!(snippet.cfg_gated);
    }

    #[test]
    fn test_generate_overflow_check_sub() {
        let check = make_check(
            CheckKind::ArithmeticOverflow,
            CheckStrategy::OverflowCheck { op: trust_types::BinOp::Sub },
        );
        let snippet = generate_check_code(&check);
        assert!(snippet.code.contains("checked_sub"));
    }

    #[test]
    fn test_generate_overflow_check_mul() {
        let check = make_check(
            CheckKind::ArithmeticOverflow,
            CheckStrategy::OverflowCheck { op: trust_types::BinOp::Mul },
        );
        let snippet = generate_check_code(&check);
        assert!(snippet.code.contains("checked_mul"));
    }

    #[test]
    fn test_generate_bounds_check() {
        let check = make_check(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck);
        let snippet = generate_check_code(&check);
        assert!(snippet.code.contains("index < len"));
        assert!(snippet.code.contains("test_fn"));
        assert!(snippet.code.contains("src/lib.rs:42"));
        assert!(snippet.comment.contains("index bounds check"));
    }

    #[test]
    fn test_generate_division_check() {
        let check = make_check(CheckKind::DivisionByZero, CheckStrategy::DivisorNonZero);
        let snippet = generate_check_code(&check);
        assert!(snippet.code.contains("divisor != 0"));
        assert!(snippet.code.contains("test_fn"));
        assert!(snippet.code.contains("division by zero"));
    }

    #[test]
    fn test_generate_slice_check() {
        let check = make_check(CheckKind::SliceBoundsCheck, CheckStrategy::SliceRangeCheck);
        let snippet = generate_check_code(&check);
        assert!(snippet.code.contains("start <= end"));
        assert!(snippet.code.contains("end <= len"));
        assert!(snippet.code.contains("test_fn"));
    }

    #[test]
    fn test_generate_preserved_assertion() {
        let check = make_check(
            CheckKind::Assertion { message: "x > 0".to_string() },
            CheckStrategy::PreserveAssertion { message: "x > 0".to_string() },
        );
        let snippet = generate_check_code(&check);
        assert!(snippet.code.contains("x > 0"));
        assert!(snippet.code.contains("assertion failed"));
    }

    #[test]
    fn test_generate_unreachable_check() {
        let check = make_check(CheckKind::Unreachable, CheckStrategy::UnreachablePanic);
        let snippet = generate_check_code(&check);
        assert!(snippet.code.contains("unreachable!"));
        assert!(snippet.code.contains("test_fn"));
    }

    #[test]
    fn test_generate_shift_check() {
        let check = make_check(CheckKind::ShiftOverflow, CheckStrategy::ShiftCheck);
        let snippet = generate_check_code(&check);
        assert!(snippet.code.contains("shift_amount < bit_width"));
        assert!(snippet.code.contains("debug_assert!"));
    }

    #[test]
    fn test_generate_negation_check() {
        let check = make_check(CheckKind::NegationOverflow, CheckStrategy::NegationCheck);
        let snippet = generate_check_code(&check);
        assert!(snippet.code.contains("Self::MIN"));
        assert!(snippet.code.contains("negation overflow"));
    }

    // -----------------------------------------------------------------------
    // cfg gating
    // -----------------------------------------------------------------------

    #[test]
    fn test_wrap_cfg_gated() {
        let check = make_check(CheckKind::DivisionByZero, CheckStrategy::DivisorNonZero);
        let snippet = generate_check_code(&check);
        let wrapped = wrap_cfg_gated(&snippet);
        assert!(wrapped.contains("#[cfg(trust_runtime)]"));
        assert!(wrapped.contains("// tRust:"));
    }

    #[test]
    fn test_wrap_not_cfg_gated() {
        let snippet = CodeSnippet {
            code: "let x = 1;".to_string(),
            cfg_gated: false,
            comment: "test".to_string(),
        };
        let wrapped = wrap_cfg_gated(&snippet);
        assert!(!wrapped.contains("#[cfg(trust_runtime)]"));
        assert!(wrapped.contains("let x = 1;"));
    }

    // -----------------------------------------------------------------------
    // Plan-level codegen
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_plan_code() {
        use trust_types::{Formula, VcKind, VerificationCondition, VerificationResult};
        use crate::instrumentation::plan_instrumentation;

        let results = vec![
            (
                VerificationCondition {
                    kind: VcKind::IndexOutOfBounds,
                    function: "lookup".to_string(),
                    location: span(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Unknown {
                    solver: "z4".to_string(),
                    time_ms: 50,
                    reason: "incomplete".to_string(),
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "divide".to_string(),
                    location: span(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Timeout {
                    solver: "z4".to_string(),
                    timeout_ms: 5000,
                },
            ),
        ];

        let plan = plan_instrumentation("test_fn", &results, true);
        let snippets = generate_plan_code(&plan);
        assert_eq!(snippets.len(), 2);
        assert!(snippets[0].code.contains("index < len"));
        assert!(snippets[1].code.contains("divisor != 0"));
    }

    #[test]
    fn test_generate_plan_code_empty() {
        use crate::instrumentation::plan_instrumentation;
        let plan = plan_instrumentation("f", &[], true);
        let snippets = generate_plan_code(&plan);
        assert!(snippets.is_empty());
    }

    // -----------------------------------------------------------------------
    // Edge case: assertion with quotes in message
    // -----------------------------------------------------------------------

    #[test]
    fn test_preserved_assertion_escapes_quotes() {
        let check = make_check(
            CheckKind::Assertion { message: "x > \"limit\"".to_string() },
            CheckStrategy::PreserveAssertion { message: "x > \"limit\"".to_string() },
        );
        let snippet = generate_check_code(&check);
        assert!(snippet.code.contains("\\\"limit\\\""));
    }
}
