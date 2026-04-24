// trust-strengthen/proposer.rs: Spec proposal generation from failure patterns
//
// Takes classified failures from analyzer.rs and generates concrete spec
// proposals (#[requires], #[ensures], safe arithmetic rewrites).
//
// When SourceContext is available, proposals use real variable names from the
// source code instead of generic placeholders.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::BinOp;

use crate::analyzer::{FailureAnalysis, FailurePattern};
use crate::source_reader::{self, SourceContext};

/// A proposed specification or code change.
#[derive(Debug, Clone)]
pub struct Proposal {
    /// Function this proposal targets.
    pub function_path: String,
    /// Human-readable function name.
    pub function_name: String,
    /// What kind of proposal.
    pub kind: ProposalKind,
    /// Confidence in this proposal (0.0-1.0).
    pub confidence: f64,
    /// Human-readable rationale.
    pub rationale: String,
}

/// The kind of spec or code change being proposed.
#[derive(Debug, Clone, PartialEq)]
pub enum ProposalKind {
    /// Add a precondition: `#[requires("expr")]`.
    AddPrecondition { spec_body: String },
    /// Add a postcondition: `#[ensures("expr")]`.
    AddPostcondition { spec_body: String },
    /// Add a loop invariant: `#[invariant("expr")]`.
    AddInvariant { spec_body: String },
    /// Replace an operation with a safe variant.
    SafeArithmetic { original: String, replacement: String },
    /// Add a bounds check before an indexing operation.
    AddBoundsCheck { check_expr: String },
    /// Add a non-zero check before division.
    AddNonZeroCheck { check_expr: String },
}

/// Generate proposals from analyzed failures for a single function.
pub fn strengthen(
    function_path: &str,
    function_name: &str,
    analyses: &[FailureAnalysis],
) -> Vec<Proposal> {
    analyses
        .iter()
        .flat_map(|a| propose_for_failure(function_path, function_name, a, None))
        .collect()
}

/// Generate context-aware proposals using source code analysis.
///
/// When `SourceContext` is available, proposals use real variable names:
/// - Overflow: `requires(a <= usize::MAX - b)` instead of generic "addition does not overflow"
/// - Div-zero: `requires(y != 0)` instead of generic "divisor != 0"
/// - OOB: `requires(i < arr.len())` instead of generic "index < len"
pub fn strengthen_with_context(
    function_path: &str,
    function_name: &str,
    analyses: &[FailureAnalysis],
    source_ctx: &SourceContext,
) -> Vec<Proposal> {
    analyses
        .iter()
        .flat_map(|a| propose_for_failure(function_path, function_name, a, Some(source_ctx)))
        .collect()
}

fn propose_for_failure(
    function_path: &str,
    function_name: &str,
    analysis: &FailureAnalysis,
    source_ctx: Option<&SourceContext>,
) -> Vec<Proposal> {
    match &analysis.pattern {
        FailurePattern::ArithmeticOverflow { op } => {
            propose_overflow_fix(function_path, function_name, op, source_ctx)
        }
        FailurePattern::DivisionByZero => {
            propose_div_zero_fix(function_path, function_name, source_ctx)
        }
        FailurePattern::IndexOutOfBounds => {
            propose_oob_fix(function_path, function_name, source_ctx)
        }
        FailurePattern::CastOverflow => propose_cast_overflow_fix(function_path, function_name),
        FailurePattern::NegationOverflow => {
            propose_negation_overflow_fix(function_path, function_name)
        }
        FailurePattern::ShiftOverflow => propose_shift_overflow_fix(function_path, function_name),
        FailurePattern::AssertionFailure { message } => {
            propose_assertion_fix(function_path, function_name, message)
        }
        FailurePattern::PreconditionViolation { callee } => {
            propose_precondition_fix(function_path, function_name, callee)
        }
        FailurePattern::PostconditionViolation => {
            propose_postcondition_fix(function_path, function_name)
        }
        FailurePattern::UnreachableReached => propose_unreachable_fix(function_path, function_name),
        FailurePattern::Temporal => propose_temporal_fix(function_path, function_name),
        FailurePattern::Unknown => propose_unknown_fix(function_path, function_name),
    }
}

fn propose_overflow_fix(
    function_path: &str,
    function_name: &str,
    op: &BinOp,
    source_ctx: Option<&SourceContext>,
) -> Vec<Proposal> {
    let op_name = match op {
        BinOp::Add => "addition",
        BinOp::Sub => "subtraction",
        BinOp::Mul => "multiplication",
        _ => "operation",
    };
    let checked_method = match op {
        BinOp::Add => "checked_add",
        BinOp::Sub => "checked_sub",
        BinOp::Mul => "checked_mul",
        _ => return vec![],
    };
    let op_char = match op {
        BinOp::Add => '+',
        BinOp::Sub => '-',
        BinOp::Mul => '*',
        _ => '?',
    };

    // Try to find real operand names from source context
    let (left, right, type_suffix) = if let Some(ctx) = source_ctx {
        let operands = source_reader::find_arithmetic_operands(ctx);
        let matching = operands.iter().find(|(_, _, c)| *c == op_char);
        if let Some((l, r, _)) = matching {
            // Determine type suffix from param types
            let suffix = ctx
                .params
                .iter()
                .find(|(name, _)| name == l)
                .map(|(_, ty)| type_max_for(ty))
                .unwrap_or_default();
            (l.clone(), r.clone(), suffix)
        } else {
            ("a".to_string(), "b".to_string(), String::new())
        }
    } else {
        ("a".to_string(), "b".to_string(), String::new())
    };

    // Build context-aware spec body
    let spec_body = if !type_suffix.is_empty() {
        match op {
            BinOp::Add => format!("{left} <= {type_suffix} - {right}"),
            BinOp::Sub => format!("{left} >= {right}"),
            BinOp::Mul => format!("{left} == 0 || {right} <= {type_suffix} / {left}"),
            _ => format!("{left} + {right} >= {left}"),
        }
    } else {
        match op {
            BinOp::Add => format!("{left} + {right} >= {left}"),
            BinOp::Sub => format!("{left} >= {right}"),
            BinOp::Mul => format!("{left} == 0 || {right} == 0"),
            _ => format!("{left} + {right} >= {left}"),
        }
    };

    // Build context-aware checked arithmetic replacement
    let original = format!("{left} {sym} {right}", sym = op_symbol(op));
    let replacement = format!("{left}.{checked_method}({right}).expect(\"{op_name} overflow\")");

    vec![
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition { spec_body },
            confidence: 0.85,
            rationale: format!(
                "Arithmetic {op_name} can overflow -- add precondition bounding operands"
            ),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::SafeArithmetic { original, replacement },
            confidence: 0.75,
            rationale: format!("Replace raw {op_name} with {checked_method}() for safe arithmetic"),
        },
    ]
}

fn propose_div_zero_fix(
    function_path: &str,
    function_name: &str,
    source_ctx: Option<&SourceContext>,
) -> Vec<Proposal> {
    // Try to find the actual divisor variable name
    let divisor_name = if let Some(ctx) = source_ctx {
        let divisors = source_reader::find_divisor_params(ctx);
        divisors.into_iter().next().unwrap_or_else(|| "divisor".to_string())
    } else {
        "divisor".to_string()
    };

    vec![
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition { spec_body: format!("{divisor_name} != 0") },
            confidence: 0.95,
            rationale: format!("Division by zero possible -- require {divisor_name} != 0"),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddNonZeroCheck {
                check_expr: format!("assert!({divisor_name} != 0, \"division by zero\")"),
            },
            confidence: 0.8,
            rationale: "Add runtime non-zero check before division".into(),
        },
    ]
}

fn propose_oob_fix(
    function_path: &str,
    function_name: &str,
    source_ctx: Option<&SourceContext>,
) -> Vec<Proposal> {
    // Try to find the actual index and array variable names
    let (index_name, array_expr) = if let Some(ctx) = source_ctx {
        let indices = source_reader::find_index_params(ctx);
        if let Some((idx, arr_opt)) = indices.into_iter().next() {
            let arr = arr_opt.unwrap_or_else(|| "slice".to_string());
            (idx, arr)
        } else {
            ("index".to_string(), "slice".to_string())
        }
    } else {
        ("index".to_string(), "slice".to_string())
    };

    vec![
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition {
                spec_body: format!("{index_name} < {array_expr}.len()"),
            },
            confidence: 0.9,
            rationale: format!(
                "Index out of bounds possible -- require {index_name} < {array_expr}.len()"
            ),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddBoundsCheck {
                check_expr: format!(
                    "assert!({index_name} < {array_expr}.len(), \"index out of bounds\")"
                ),
            },
            confidence: 0.8,
            rationale: "Add explicit bounds check before indexing".into(),
        },
    ]
}

fn propose_cast_overflow_fix(function_path: &str, function_name: &str) -> Vec<Proposal> {
    vec![
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition { spec_body: "value >= 0 && value <= MAX".into() },
            confidence: 0.7,
            rationale: "Cast may overflow -- add TryFrom-based range check".into(),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::SafeArithmetic {
                original: "value as TargetType".into(),
                replacement: "TargetType::try_from(value).expect(\"cast overflow\")".into(),
            },
            confidence: 0.65,
            rationale: "Replace `as` cast with TryFrom for safe conversion".into(),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddBoundsCheck {
                check_expr: "assert!(value <= TargetType::MAX as SourceType, \"cast overflow\")"
                    .into(),
            },
            confidence: 0.6,
            rationale: "Add explicit range check before cast".into(),
        },
    ]
}

fn propose_negation_overflow_fix(function_path: &str, function_name: &str) -> Vec<Proposal> {
    vec![
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition { spec_body: "x != MIN".into() },
            confidence: 0.9,
            rationale: "Negation of MIN overflows -- require x != MIN".into(),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::SafeArithmetic {
                original: "-x".into(),
                replacement: "x.checked_neg().expect(\"negation overflow\")".into(),
            },
            confidence: 0.8,
            rationale: "Replace unary negation with checked_neg() for safety".into(),
        },
    ]
}

fn propose_shift_overflow_fix(function_path: &str, function_name: &str) -> Vec<Proposal> {
    vec![
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition { spec_body: "shift < bit_width".into() },
            confidence: 0.9,
            rationale: "Shift amount must be less than bit width".into(),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddBoundsCheck {
                check_expr: "assert!(shift < std::mem::size_of::<T>() * 8, \"shift overflow\")"
                    .into(),
            },
            confidence: 0.8,
            rationale: "Add explicit shift amount bounds check".into(),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::SafeArithmetic {
                original: "value << shift".into(),
                replacement: "value.checked_shl(shift as u32).expect(\"shift overflow\")".into(),
            },
            confidence: 0.7,
            rationale: "Replace raw shift with checked_shl() for safe shifting".into(),
        },
    ]
}

fn propose_assertion_fix(function_path: &str, function_name: &str, message: &str) -> Vec<Proposal> {
    vec![
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition { spec_body: message.to_string() },
            confidence: 0.8,
            rationale: format!("Assertion `{message}` can fail -- propagate as precondition"),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPostcondition { spec_body: message.to_string() },
            confidence: 0.5,
            rationale: format!(
                "Assertion `{message}` should hold -- add as postcondition to strengthen spec"
            ),
        },
    ]
}

fn propose_precondition_fix(
    function_path: &str,
    function_name: &str,
    callee: &str,
) -> Vec<Proposal> {
    vec![
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition { spec_body: format!("{callee}_pre != false") },
            confidence: 0.7,
            rationale: format!(
                "Call to {callee} violates its precondition -- propagate requirement to caller"
            ),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddBoundsCheck {
                check_expr: format!(
                    "// Verify {callee} precondition before call\nassert!(/* {callee} precondition */);"
                ),
            },
            confidence: 0.6,
            rationale: format!(
                "Add runtime check to validate {callee}'s precondition before the call"
            ),
        },
    ]
}

fn propose_postcondition_fix(function_path: &str, function_name: &str) -> Vec<Proposal> {
    vec![
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPostcondition {
                spec_body: "result >= 0".into(),
            },
            confidence: 0.5,
            rationale: "Postcondition not established -- needs strengthened implementation or weaker postcondition".into(),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition {
                spec_body: "n >= 0".into(),
            },
            confidence: 0.4,
            rationale: "Postcondition may require stronger input constraints to be provable".into(),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddInvariant {
                spec_body: "i >= 0 && i <= n".into(),
            },
            confidence: 0.35,
            rationale: "Loop or branch may need invariant to establish postcondition".into(),
        },
    ]
}

fn propose_unreachable_fix(function_path: &str, function_name: &str) -> Vec<Proposal> {
    vec![
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition { spec_body: "input >= 0 && input <= MAX".into() },
            confidence: 0.7,
            rationale: "Unreachable code reached -- add precondition for enum exhaustiveness"
                .into(),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddBoundsCheck {
                check_expr: "// Replace unreachable!() with exhaustive match or default branch"
                    .into(),
            },
            confidence: 0.6,
            rationale: "Ensure all enum variants or input classes are handled".into(),
        },
    ]
}

fn propose_temporal_fix(function_path: &str, function_name: &str) -> Vec<Proposal> {
    vec![
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddInvariant {
                spec_body: "counter >= 0 && counter < limit".into(),
            },
            confidence: 0.6,
            rationale: "Temporal property violation -- add loop invariant for progress".into(),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition { spec_body: "state >= 0".into() },
            confidence: 0.5,
            rationale: "Temporal liveness may require initial state precondition".into(),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPostcondition { spec_body: "result >= 0".into() },
            confidence: 0.4,
            rationale: "Add postcondition to encode the expected temporal behavior".into(),
        },
    ]
}

fn propose_unknown_fix(function_path: &str, function_name: &str) -> Vec<Proposal> {
    vec![
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddBoundsCheck {
                check_expr: "// PLACEHOLDER: investigate failure and add appropriate precondition"
                    .into(),
            },
            confidence: 0.2,
            rationale: "Unknown failure pattern -- needs manual investigation or LLM analysis"
                .into(),
        },
        Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddBoundsCheck {
                check_expr: "// PLACEHOLDER: investigate failure and add appropriate postcondition"
                    .into(),
            },
            confidence: 0.15,
            rationale: "Unknown failure -- may need postcondition after investigation".into(),
        },
    ]
}

/// Map a Rust type string to its MAX constant expression.
fn type_max_for(ty: &str) -> String {
    match ty {
        "usize" => "usize::MAX".to_string(),
        "u8" => "u8::MAX".to_string(),
        "u16" => "u16::MAX".to_string(),
        "u32" => "u32::MAX".to_string(),
        "u64" => "u64::MAX".to_string(),
        "u128" => "u128::MAX".to_string(),
        "isize" => "isize::MAX".to_string(),
        "i8" => "i8::MAX".to_string(),
        "i16" => "i16::MAX".to_string(),
        "i32" => "i32::MAX".to_string(),
        "i64" => "i64::MAX".to_string(),
        "i128" => "i128::MAX".to_string(),
        _ => String::new(),
    }
}

fn op_symbol(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        _ => "?",
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{Ty, VcKind};

    use super::*;
    use crate::analyzer::FailureAnalysis;
    use crate::source_reader::extract_function;

    // --- Existing tests (backward compatibility, no source context) ---

    #[test]
    fn test_overflow_proposals() {
        let analysis = FailureAnalysis {
            vc_kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            function: "get_midpoint".into(),
            pattern: FailurePattern::ArithmeticOverflow { op: BinOp::Add },
            solver: Some("z4".into()),
        };

        let proposals = strengthen("test::get_midpoint", "get_midpoint", &[analysis]);
        assert_eq!(proposals.len(), 2);
        assert!(matches!(proposals[0].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(proposals[1].kind, ProposalKind::SafeArithmetic { .. }));
    }

    #[test]
    fn test_div_zero_proposals() {
        let analysis = FailureAnalysis {
            vc_kind: VcKind::DivisionByZero,
            function: "divide".into(),
            pattern: FailurePattern::DivisionByZero,
            solver: None,
        };

        let proposals = strengthen("test::divide", "divide", &[analysis]);
        assert_eq!(proposals.len(), 2);
        assert!(matches!(proposals[0].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(proposals[1].kind, ProposalKind::AddNonZeroCheck { .. }));
    }

    #[test]
    fn test_oob_proposals() {
        let analysis = FailureAnalysis {
            vc_kind: VcKind::IndexOutOfBounds,
            function: "get".into(),
            pattern: FailurePattern::IndexOutOfBounds,
            solver: None,
        };

        let proposals = strengthen("test::get", "get", &[analysis]);
        assert_eq!(proposals.len(), 2);
        assert!(matches!(proposals[0].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(proposals[1].kind, ProposalKind::AddBoundsCheck { .. }));
    }

    #[test]
    fn test_unreachable_produces_proposals() {
        let analysis = FailureAnalysis {
            vc_kind: VcKind::Unreachable,
            function: "f".into(),
            pattern: FailurePattern::UnreachableReached,
            solver: None,
        };

        let proposals = strengthen("test::f", "f", &[analysis]);
        assert_eq!(proposals.len(), 2);
        assert!(matches!(proposals[0].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(proposals[1].kind, ProposalKind::AddBoundsCheck { .. }));
    }

    #[test]
    fn test_multiple_failures() {
        let analyses = vec![
            FailureAnalysis {
                vc_kind: VcKind::DivisionByZero,
                function: "f".into(),
                pattern: FailurePattern::DivisionByZero,
                solver: None,
            },
            FailureAnalysis {
                vc_kind: VcKind::IndexOutOfBounds,
                function: "f".into(),
                pattern: FailurePattern::IndexOutOfBounds,
                solver: None,
            },
        ];

        let proposals = strengthen("test::f", "f", &analyses);
        assert_eq!(proposals.len(), 4); // 2 per failure
    }

    // --- Context-aware proposal tests ---

    #[test]
    fn test_overflow_with_context_midpoint() {
        let source = "fn get_midpoint(a: usize, b: usize) -> usize {\n    (a + b) / 2\n}";
        let ctx = extract_function(source, "get_midpoint").unwrap();

        let analysis = FailureAnalysis {
            vc_kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            function: "get_midpoint".into(),
            pattern: FailurePattern::ArithmeticOverflow { op: BinOp::Add },
            solver: Some("z4".into()),
        };

        let proposals =
            strengthen_with_context("test::get_midpoint", "get_midpoint", &[analysis], &ctx);

        assert_eq!(proposals.len(), 2);

        // Precondition should use real variable names
        if let ProposalKind::AddPrecondition { ref spec_body } = proposals[0].kind {
            assert!(
                spec_body.contains("a") && spec_body.contains("b"),
                "spec should use real param names a, b: got '{spec_body}'"
            );
            assert!(
                spec_body.contains("usize::MAX"),
                "spec should reference usize::MAX: got '{spec_body}'"
            );
        } else {
            panic!("expected AddPrecondition");
        }

        // SafeArithmetic should use real variable names
        if let ProposalKind::SafeArithmetic { ref original, ref replacement } = proposals[1].kind {
            assert!(
                original.contains("a") && original.contains("b"),
                "original should use real names: got '{original}'"
            );
            assert!(
                replacement.contains("a.checked_add(b)"),
                "replacement should use real names: got '{replacement}'"
            );
        } else {
            panic!("expected SafeArithmetic");
        }
    }

    #[test]
    fn test_div_zero_with_context_safe_divide() {
        let source = "fn safe_divide(x: u64, y: u64) -> u64 {\n    x / y\n}";
        let ctx = extract_function(source, "safe_divide").unwrap();

        let analysis = FailureAnalysis {
            vc_kind: VcKind::DivisionByZero,
            function: "safe_divide".into(),
            pattern: FailurePattern::DivisionByZero,
            solver: None,
        };

        let proposals =
            strengthen_with_context("test::safe_divide", "safe_divide", &[analysis], &ctx);

        assert_eq!(proposals.len(), 2);

        // Should use real divisor name "y"
        if let ProposalKind::AddPrecondition { ref spec_body } = proposals[0].kind {
            assert_eq!(spec_body, "y != 0", "should identify y as divisor");
        } else {
            panic!("expected AddPrecondition");
        }

        if let ProposalKind::AddNonZeroCheck { ref check_expr } = proposals[1].kind {
            assert!(
                check_expr.contains("y != 0"),
                "check should use real divisor name: got '{check_expr}'"
            );
        } else {
            panic!("expected AddNonZeroCheck");
        }
    }

    #[test]
    fn test_oob_with_context_get_element() {
        let source = "fn get_element(arr: &[i32], i: usize) -> i32 {\n    arr[i]\n}";
        let ctx = extract_function(source, "get_element").unwrap();

        let analysis = FailureAnalysis {
            vc_kind: VcKind::IndexOutOfBounds,
            function: "get_element".into(),
            pattern: FailurePattern::IndexOutOfBounds,
            solver: None,
        };

        let proposals =
            strengthen_with_context("test::get_element", "get_element", &[analysis], &ctx);

        assert_eq!(proposals.len(), 2);

        // Should use real index name "i" and array name "arr"
        if let ProposalKind::AddPrecondition { ref spec_body } = proposals[0].kind {
            assert_eq!(spec_body, "i < arr.len()", "should identify i as index and arr as array");
        } else {
            panic!("expected AddPrecondition");
        }

        if let ProposalKind::AddBoundsCheck { ref check_expr } = proposals[1].kind {
            assert!(
                check_expr.contains("i < arr.len()"),
                "check should use real names: got '{check_expr}'"
            );
        } else {
            panic!("expected AddBoundsCheck");
        }
    }

    #[test]
    fn test_context_aware_falls_back_without_match() {
        // Source has no arithmetic, so overflow proposal falls back to generic names
        let source = "fn noop(x: i32) -> i32 {\n    x\n}";
        let ctx = extract_function(source, "noop").unwrap();

        let analysis = FailureAnalysis {
            vc_kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            function: "noop".into(),
            pattern: FailurePattern::ArithmeticOverflow { op: BinOp::Add },
            solver: None,
        };

        let proposals = strengthen_with_context("test::noop", "noop", &[analysis], &ctx);

        assert_eq!(proposals.len(), 2);
        // Falls back to generic formula with placeholder var names
        if let ProposalKind::AddPrecondition { ref spec_body } = proposals[0].kind {
            assert_eq!(spec_body, "a + b >= a");
        } else {
            panic!("expected AddPrecondition");
        }
    }

    #[test]
    fn test_div_zero_no_divisor_param_falls_back() {
        // No parameter is used as divisor (divides by literal)
        let source = "fn half(x: u64) -> u64 {\n    x / 2\n}";
        let ctx = extract_function(source, "half").unwrap();

        let analysis = FailureAnalysis {
            vc_kind: VcKind::DivisionByZero,
            function: "half".into(),
            pattern: FailurePattern::DivisionByZero,
            solver: None,
        };

        let proposals = strengthen_with_context("test::half", "half", &[analysis], &ctx);

        // Falls back to generic "divisor"
        if let ProposalKind::AddPrecondition { ref spec_body } = proposals[0].kind {
            assert_eq!(spec_body, "divisor != 0");
        } else {
            panic!("expected AddPrecondition");
        }
    }

    #[test]
    fn test_type_max_for_common_types() {
        assert_eq!(type_max_for("usize"), "usize::MAX");
        assert_eq!(type_max_for("u64"), "u64::MAX");
        assert_eq!(type_max_for("i32"), "i32::MAX");
        assert_eq!(type_max_for("String"), "");
    }

    // --- Enhanced pattern tests: multiple proposals per pattern ---

    #[test]
    fn test_cast_overflow_proposals() {
        let analysis = FailureAnalysis {
            vc_kind: VcKind::CastOverflow {
                from_ty: Ty::Int { width: 64, signed: false },
                to_ty: Ty::Int { width: 32, signed: false },
            },
            function: "narrow".into(),
            pattern: FailurePattern::CastOverflow,
            solver: None,
        };

        let proposals = strengthen("test::narrow", "narrow", &[analysis]);
        assert_eq!(proposals.len(), 3, "CastOverflow should produce 3 proposals");
        assert!(matches!(proposals[0].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(proposals[1].kind, ProposalKind::SafeArithmetic { .. }));
        assert!(matches!(proposals[2].kind, ProposalKind::AddBoundsCheck { .. }));

        // Check SafeArithmetic suggests TryFrom
        if let ProposalKind::SafeArithmetic { ref replacement, .. } = proposals[1].kind {
            assert!(
                replacement.contains("try_from"),
                "should suggest TryFrom: got '{replacement}'"
            );
        }
    }

    #[test]
    fn test_negation_overflow_proposals() {
        let analysis = FailureAnalysis {
            vc_kind: VcKind::NegationOverflow { ty: Ty::Int { width: 64, signed: true } },
            function: "negate".into(),
            pattern: FailurePattern::NegationOverflow,
            solver: None,
        };

        let proposals = strengthen("test::negate", "negate", &[analysis]);
        assert_eq!(proposals.len(), 2, "NegationOverflow should produce 2 proposals");
        assert!(matches!(proposals[0].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(proposals[1].kind, ProposalKind::SafeArithmetic { .. }));

        if let ProposalKind::SafeArithmetic { ref replacement, .. } = proposals[1].kind {
            assert!(
                replacement.contains("checked_neg"),
                "should suggest checked_neg: got '{replacement}'"
            );
        }
    }

    #[test]
    fn test_shift_overflow_proposals() {
        let analysis = FailureAnalysis {
            vc_kind: VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: Ty::Int { width: 64, signed: false },
                shift_ty: Ty::Int { width: 64, signed: false },
            },
            function: "shift_left".into(),
            pattern: FailurePattern::ShiftOverflow,
            solver: None,
        };

        let proposals = strengthen("test::shift_left", "shift_left", &[analysis]);
        assert_eq!(proposals.len(), 3, "ShiftOverflow should produce 3 proposals");
        assert!(matches!(proposals[0].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(proposals[1].kind, ProposalKind::AddBoundsCheck { .. }));
        assert!(matches!(proposals[2].kind, ProposalKind::SafeArithmetic { .. }));

        if let ProposalKind::SafeArithmetic { ref replacement, .. } = proposals[2].kind {
            assert!(
                replacement.contains("checked_shl"),
                "should suggest checked_shl: got '{replacement}'"
            );
        }
    }

    #[test]
    fn test_assertion_failure_proposals() {
        let analysis = FailureAnalysis {
            vc_kind: VcKind::Assertion { message: "x > 0".into() },
            function: "check_positive".into(),
            pattern: FailurePattern::AssertionFailure { message: "x > 0".into() },
            solver: None,
        };

        let proposals = strengthen("test::check_positive", "check_positive", &[analysis]);
        assert_eq!(proposals.len(), 2, "AssertionFailure should produce 2 proposals");
        assert!(matches!(proposals[0].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(proposals[1].kind, ProposalKind::AddPostcondition { .. }));

        // Both should contain the assertion message
        if let ProposalKind::AddPrecondition { ref spec_body } = proposals[0].kind {
            assert_eq!(spec_body, "x > 0");
        }
        if let ProposalKind::AddPostcondition { ref spec_body } = proposals[1].kind {
            assert_eq!(spec_body, "x > 0");
        }
    }

    #[test]
    fn test_precondition_violation_proposals() {
        let analysis = FailureAnalysis {
            vc_kind: VcKind::Precondition { callee: "safe_divide".into() },
            function: "compute".into(),
            pattern: FailurePattern::PreconditionViolation { callee: "safe_divide".into() },
            solver: None,
        };

        let proposals = strengthen("test::compute", "compute", &[analysis]);
        assert_eq!(proposals.len(), 2, "PreconditionViolation should produce 2 proposals");
        assert!(matches!(proposals[0].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(proposals[1].kind, ProposalKind::AddBoundsCheck { .. }));

        if let ProposalKind::AddPrecondition { ref spec_body } = proposals[0].kind {
            assert!(
                spec_body.contains("safe_divide"),
                "should reference callee: got '{spec_body}'"
            );
        }
    }

    #[test]
    fn test_postcondition_violation_proposals() {
        let analysis = FailureAnalysis {
            vc_kind: VcKind::Postcondition,
            function: "build_result".into(),
            pattern: FailurePattern::PostconditionViolation,
            solver: None,
        };

        let proposals = strengthen("test::build_result", "build_result", &[analysis]);
        assert_eq!(proposals.len(), 3, "PostconditionViolation should produce 3 proposals");
        assert!(matches!(proposals[0].kind, ProposalKind::AddPostcondition { .. }));
        assert!(matches!(proposals[1].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(proposals[2].kind, ProposalKind::AddInvariant { .. }));

        // Confidence should decrease: postcondition > precondition > invariant
        assert!(proposals[0].confidence > proposals[1].confidence);
        assert!(proposals[1].confidence > proposals[2].confidence);
    }

    #[test]
    fn test_temporal_proposals() {
        let analysis = FailureAnalysis {
            vc_kind: VcKind::Deadlock,
            function: "event_loop".into(),
            pattern: FailurePattern::Temporal,
            solver: None,
        };

        let proposals = strengthen("test::event_loop", "event_loop", &[analysis]);
        assert_eq!(proposals.len(), 3, "Temporal should produce 3 proposals");
        assert!(matches!(proposals[0].kind, ProposalKind::AddInvariant { .. }));
        assert!(matches!(proposals[1].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(proposals[2].kind, ProposalKind::AddPostcondition { .. }));

        // Invariant has highest confidence for temporal
        assert!(proposals[0].confidence > proposals[1].confidence);
    }

    #[test]
    fn test_unknown_proposals() {
        let analysis = FailureAnalysis {
            vc_kind: VcKind::Unreachable, // re-using, doesn't matter for Unknown
            function: "mystery".into(),
            pattern: FailurePattern::Unknown,
            solver: None,
        };

        let proposals = strengthen("test::mystery", "mystery", &[analysis]);
        assert_eq!(proposals.len(), 2, "Unknown should produce 2 proposals");
        // Unknown now produces AddBoundsCheck (placeholder comments) instead of spec-bearing kinds
        assert!(matches!(proposals[0].kind, ProposalKind::AddBoundsCheck { .. }));
        assert!(matches!(proposals[1].kind, ProposalKind::AddBoundsCheck { .. }));

        // Both should have low confidence
        assert!(proposals[0].confidence <= 0.3, "Unknown proposals should have low confidence");
        assert!(proposals[1].confidence <= 0.3, "Unknown proposals should have low confidence");
    }

    #[test]
    fn test_all_patterns_produce_proposals() {
        // Verify EVERY FailurePattern variant now produces at least 2 proposals
        let patterns: Vec<FailurePattern> = vec![
            FailurePattern::ArithmeticOverflow { op: BinOp::Add },
            FailurePattern::DivisionByZero,
            FailurePattern::IndexOutOfBounds,
            FailurePattern::CastOverflow,
            FailurePattern::NegationOverflow,
            FailurePattern::ShiftOverflow,
            FailurePattern::AssertionFailure { message: "x > 0".into() },
            FailurePattern::PreconditionViolation { callee: "f".into() },
            FailurePattern::PostconditionViolation,
            FailurePattern::UnreachableReached,
            FailurePattern::Temporal,
            FailurePattern::Unknown,
        ];

        for pattern in &patterns {
            let analysis = FailureAnalysis {
                vc_kind: VcKind::Unreachable, // doesn't affect pattern-based proposals
                function: "test_fn".into(),
                pattern: pattern.clone(),
                solver: None,
            };
            let proposals = strengthen("test::test_fn", "test_fn", &[analysis]);
            assert!(
                proposals.len() >= 2,
                "Pattern {pattern:?} should produce at least 2 proposals, got {}",
                proposals.len()
            );
        }
    }

    #[test]
    fn test_all_proposals_have_valid_confidence() {
        let patterns: Vec<FailurePattern> = vec![
            FailurePattern::ArithmeticOverflow { op: BinOp::Mul },
            FailurePattern::DivisionByZero,
            FailurePattern::IndexOutOfBounds,
            FailurePattern::CastOverflow,
            FailurePattern::NegationOverflow,
            FailurePattern::ShiftOverflow,
            FailurePattern::AssertionFailure { message: "cond".into() },
            FailurePattern::PreconditionViolation { callee: "g".into() },
            FailurePattern::PostconditionViolation,
            FailurePattern::UnreachableReached,
            FailurePattern::Temporal,
            FailurePattern::Unknown,
        ];

        for pattern in &patterns {
            let analysis = FailureAnalysis {
                vc_kind: VcKind::Unreachable,
                function: "f".into(),
                pattern: pattern.clone(),
                solver: None,
            };
            let proposals = strengthen("test::f", "f", &[analysis]);
            for p in &proposals {
                assert!(
                    (0.0..=1.0).contains(&p.confidence),
                    "Proposal for {pattern:?} has invalid confidence {}: {:?}",
                    p.confidence,
                    p.kind
                );
            }
        }
    }
}
