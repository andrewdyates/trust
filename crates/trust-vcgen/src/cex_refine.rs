// trust-vcgen/cex_refine.rs: Counterexample-guided spec refinement
//
// Takes a solver counterexample (concrete variable assignments that violate
// a property) and maps it to Rust-level precondition suggestions. This is
// the "strengthen" step for safety properties: when z4 shows x = i32::MAX
// causes overflow, we suggest #[requires(x < i32::MAX)].
//
// Part of #74
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{BinOp, Counterexample, CounterexampleValue, Ty, VcKind};

/// A suggested precondition derived from a counterexample.
///
/// Unlike `SpecSuggestion` (temporal/liveness patterns), this targets safety
/// properties: overflow, division-by-zero, index-out-of-bounds, etc.
#[derive(Debug, Clone, PartialEq)]
pub struct PreconditionSuggestion {
    /// The VC kind that was violated.
    pub vc_kind_tag: String,
    /// Rust-level precondition text, e.g. "x < i32::MAX".
    pub precondition: String,
    /// The attribute form, e.g. "#[requires(x < i32::MAX)]".
    pub attribute: String,
    /// Explanation of why this precondition is needed.
    pub reason: String,
    /// The counterexample variable(s) that triggered the suggestion.
    pub triggering_values: Vec<(String, String)>,
    /// Confidence score in [0.0, 1.0].
    pub confidence: f64,
}

/// Analyzes counterexamples to produce precondition suggestions.
pub struct CounterexampleAnalyzer;

impl CounterexampleAnalyzer {
    /// Analyze a counterexample in the context of a failing VC kind.
    ///
    /// Returns a list of precondition suggestions that would prevent the
    /// counterexample from being reachable.
    #[must_use]
    pub fn analyze(vc_kind: &VcKind, cex: &Counterexample) -> Vec<PreconditionSuggestion> {
        match vc_kind {
            VcKind::ArithmeticOverflow { op, operand_tys } => {
                Self::analyze_overflow(cex, *op, operand_tys)
            }
            VcKind::DivisionByZero | VcKind::RemainderByZero => {
                Self::analyze_division_by_zero(cex, vc_kind)
            }
            VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
                Self::analyze_index_oob(cex, vc_kind)
            }
            VcKind::NegationOverflow { ty } => Self::analyze_negation_overflow(cex, ty),
            VcKind::ShiftOverflow { op, operand_ty, shift_ty } => {
                Self::analyze_shift_overflow(cex, *op, operand_ty, shift_ty)
            }
            VcKind::CastOverflow { from_ty, to_ty } => {
                Self::analyze_cast_overflow(cex, from_ty, to_ty)
            }
            _ => Vec::new(),
        }
    }

    /// Suggest bounds for arithmetic overflow counterexamples.
    fn analyze_overflow(
        cex: &Counterexample,
        op: BinOp,
        operand_tys: &(Ty, Ty),
    ) -> Vec<PreconditionSuggestion> {
        let op_str = match op {
            BinOp::Add => "addition",
            BinOp::Sub => "subtraction",
            BinOp::Mul => "multiplication",
            _ => "arithmetic",
        };

        let mut suggestions = Vec::new();

        for (name, value) in &cex.assignments {
            let (is_boundary, bound_str) = match (value, &operand_tys.0) {
                (CounterexampleValue::Int(v), Ty::Int { width, .. }) => {
                    let (min, max) = signed_bounds(*width);
                    if *v == max {
                        (true, format!("{name} < {}", ty_max_const(&operand_tys.0)))
                    } else if *v == min {
                        (true, format!("{name} > {}", ty_min_const(&operand_tys.0)))
                    } else {
                        (false, String::new())
                    }
                }
                (CounterexampleValue::Uint(v), Ty::Int { width, signed: false }) => {
                    let max = unsigned_max(*width);
                    if *v == max {
                        (true, format!("{name} < {}", ty_max_const(&operand_tys.0)))
                    } else if *v == 0 {
                        (true, format!("{name} > 0"))
                    } else {
                        (false, String::new())
                    }
                }
                _ => (false, String::new()),
            };

            if is_boundary {
                let attr = format!("#[requires({bound_str})]");
                suggestions.push(PreconditionSuggestion {
                    vc_kind_tag: format!("arithmetic_overflow_{op_str}"),
                    precondition: bound_str.clone(),
                    attribute: attr,
                    reason: format!(
                        "{op_str} overflows when {name} = {value}; \
                         bounding {name} prevents this"
                    ),
                    triggering_values: vec![(name.to_string(), value.to_string())],
                    confidence: 0.85,
                });
            }
        }

        // If no boundary values found, suggest generic range constraint
        if suggestions.is_empty() && !cex.assignments.is_empty() {
            let vars: Vec<(String, String)> =
                cex.assignments.iter().map(|(n, v)| (n.clone(), v.to_string())).collect();
            let var_names: Vec<&str> = cex.assignments.iter().map(|(n, _)| n.as_str()).collect();
            let combined = match op {
                BinOp::Add => {
                    let precond = format!(
                        "{} + {} <= {}",
                        var_names.first().unwrap_or(&"a"),
                        var_names.get(1).unwrap_or(&"b"),
                        ty_max_const(&operand_tys.0)
                    );
                    Some(precond)
                }
                BinOp::Sub => {
                    let precond = format!(
                        "{} >= {}",
                        var_names.first().unwrap_or(&"a"),
                        var_names.get(1).unwrap_or(&"b"),
                    );
                    Some(precond)
                }
                BinOp::Mul => {
                    let precond = format!(
                        "{} * {} <= {}",
                        var_names.first().unwrap_or(&"a"),
                        var_names.get(1).unwrap_or(&"b"),
                        ty_max_const(&operand_tys.0)
                    );
                    Some(precond)
                }
                _ => None,
            };
            if let Some(precond) = combined {
                suggestions.push(PreconditionSuggestion {
                    vc_kind_tag: format!("arithmetic_overflow_{op_str}"),
                    precondition: precond.clone(),
                    attribute: format!("#[requires({precond})]"),
                    reason: format!(
                        "{op_str} overflows with the given inputs; \
                         constraining the result range prevents this"
                    ),
                    triggering_values: vars,
                    confidence: 0.7,
                });
            }
        }

        suggestions
    }

    /// Suggest divisor != 0 for division/remainder by zero.
    fn analyze_division_by_zero(
        cex: &Counterexample,
        vc_kind: &VcKind,
    ) -> Vec<PreconditionSuggestion> {
        let kind_str =
            if matches!(vc_kind, VcKind::RemainderByZero) { "remainder" } else { "division" };

        // Find the variable that was zero
        let zero_vars: Vec<String> = cex
            .assignments
            .iter()
            .filter(|(_, v)| is_zero(v))
            .map(|(name, _)| name.clone())
            .collect();

        if zero_vars.is_empty() {
            // No explicit zero binding found; suggest generic guard
            let tvs: Vec<(String, String)> =
                cex.assignments.iter().map(|(n, v)| (n.clone(), v.to_string())).collect();
            return vec![PreconditionSuggestion {
                vc_kind_tag: format!("{kind_str}_by_zero"),
                precondition: "divisor != 0".to_string(),
                attribute: "#[requires(divisor != 0)]".to_string(),
                reason: format!(
                    "{kind_str} by zero detected; \
                     ensure the divisor is non-zero"
                ),
                triggering_values: tvs,
                confidence: 0.9,
            }];
        }

        zero_vars
            .into_iter()
            .map(|var| {
                let precond = format!("{var} != 0");
                PreconditionSuggestion {
                    vc_kind_tag: format!("{kind_str}_by_zero"),
                    precondition: precond.clone(),
                    attribute: format!("#[requires({precond})]"),
                    reason: format!(
                        "{kind_str} by zero when {var} = 0; \
                         requiring {var} != 0 prevents this"
                    ),
                    triggering_values: vec![(var, "0".to_string())],
                    confidence: 0.95,
                }
            })
            .collect()
    }

    /// Suggest index < len for index-out-of-bounds.
    fn analyze_index_oob(
        cex: &Counterexample,
        vc_kind: &VcKind,
    ) -> Vec<PreconditionSuggestion> {
        let kind_str = if matches!(vc_kind, VcKind::SliceBoundsCheck) {
            "slice_bounds"
        } else {
            "index_out_of_bounds"
        };

        // Heuristic: look for a variable named like "index"/"idx"/"i" and one
        // named like "len"/"length"/"size".
        let index_var = cex.assignments.iter().find(|(n, _)| {
            let lower = n.to_lowercase();
            lower.contains("index") || lower.contains("idx") || lower == "i"
        });
        let len_var = cex.assignments.iter().find(|(n, _)| {
            let lower = n.to_lowercase();
            lower.contains("len") || lower.contains("length") || lower.contains("size")
        });

        let all_tvs = || -> Vec<(String, String)> {
            cex.assignments.iter().map(|(n, v)| (n.clone(), v.to_string())).collect()
        };

        match (index_var, len_var) {
            (Some((idx_name, idx_val)), Some((len_name, _))) => {
                let precond = format!("{idx_name} < {len_name}");
                vec![PreconditionSuggestion {
                    vc_kind_tag: kind_str.to_string(),
                    precondition: precond.clone(),
                    attribute: format!("#[requires({precond})]"),
                    reason: format!(
                        "index out of bounds when {idx_name} = {idx_val}; \
                         bounding {idx_name} by {len_name} prevents this"
                    ),
                    triggering_values: all_tvs(),
                    confidence: 0.9,
                }]
            }
            (Some((idx_name, idx_val)), None) => {
                let precond = format!("{idx_name} < len");
                vec![PreconditionSuggestion {
                    vc_kind_tag: kind_str.to_string(),
                    precondition: precond.clone(),
                    attribute: format!("#[requires({precond})]"),
                    reason: format!(
                        "index out of bounds when {idx_name} = {idx_val}; \
                         ensure index is within bounds"
                    ),
                    triggering_values: vec![(idx_name.to_string(), idx_val.to_string())],
                    confidence: 0.75,
                }]
            }
            _ => {
                vec![PreconditionSuggestion {
                    vc_kind_tag: kind_str.to_string(),
                    precondition: "index < len".to_string(),
                    attribute: "#[requires(index < len)]".to_string(),
                    reason: "index out of bounds detected; ensure index is within bounds"
                        .to_string(),
                    triggering_values: all_tvs(),
                    confidence: 0.6,
                }]
            }
        }
    }

    /// Suggest x != MIN for negation overflow.
    fn analyze_negation_overflow(
        cex: &Counterexample,
        ty: &Ty,
    ) -> Vec<PreconditionSuggestion> {
        let min_const = ty_min_const(ty);

        let mut suggestions = Vec::new();
        for (name, v) in &cex.assignments {
            let is_min = if let (CounterexampleValue::Int(n), Ty::Int { width, .. }) = (v, ty) {
                let (min, _) = signed_bounds(*width);
                *n == min
            } else {
                false
            };
            if is_min {
                let precond = format!("{name} != {min_const}");
                suggestions.push(PreconditionSuggestion {
                    vc_kind_tag: "negation_overflow".to_string(),
                    precondition: precond.clone(),
                    attribute: format!("#[requires({precond})]"),
                    reason: format!(
                        "negating {name} overflows when {name} = {min_const}; \
                         excluding the minimum value prevents this"
                    ),
                    triggering_values: vec![(name.to_string(), min_const.clone())],
                    confidence: 0.95,
                });
            }
        }
        suggestions
    }

    /// Suggest shift amount < bit_width for shift overflow.
    fn analyze_shift_overflow(
        cex: &Counterexample,
        _op: BinOp,
        operand_ty: &Ty,
        _shift_ty: &Ty,
    ) -> Vec<PreconditionSuggestion> {
        let bit_width = match operand_ty {
            Ty::Int { width, .. } => *width,
            _ => 32,
        };

        let mut suggestions = Vec::new();
        for (name, value) in &cex.assignments {
            let exceeds = match value {
                CounterexampleValue::Uint(n) => *n >= u128::from(bit_width),
                CounterexampleValue::Int(n) => *n >= i128::from(bit_width) || *n < 0,
                _ => false,
            };
            if exceeds {
                let precond = format!("{name} < {bit_width}");
                suggestions.push(PreconditionSuggestion {
                    vc_kind_tag: "shift_overflow".to_string(),
                    precondition: precond.clone(),
                    attribute: format!("#[requires({precond})]"),
                    reason: format!(
                        "shift amount {name} = {value} exceeds bit width {bit_width}; \
                         bounding the shift amount prevents this"
                    ),
                    triggering_values: vec![(name.to_string(), value.to_string())],
                    confidence: 0.9,
                });
            }
        }
        suggestions
    }

    /// Suggest range constraints for narrowing cast overflow.
    fn analyze_cast_overflow(
        cex: &Counterexample,
        _from_ty: &Ty,
        to_ty: &Ty,
    ) -> Vec<PreconditionSuggestion> {
        let (to_min, to_max) = match to_ty {
            Ty::Int { .. } => (ty_min_const(to_ty), ty_max_const(to_ty)),
            _ => return Vec::new(),
        };

        let to_name = ty_name(to_ty);

        let mut suggestions = Vec::new();
        for (name, value) in &cex.assignments {
            let precond = match to_ty {
                Ty::Int { signed: false, .. } => format!("{name} >= 0 && {name} <= {to_max}"),
                _ => format!("{name} >= {to_min} && {name} <= {to_max}"),
            };
            suggestions.push(PreconditionSuggestion {
                vc_kind_tag: "cast_overflow".to_string(),
                precondition: precond.clone(),
                attribute: format!("#[requires({precond})]"),
                reason: format!(
                    "casting {name} = {value} to {to_name} overflows; \
                     constraining {name} to the target range prevents this"
                ),
                triggering_values: vec![(name.to_string(), value.to_string())],
                confidence: 0.85,
            });
        }
        suggestions
    }
}

/// Check if a counterexample value is zero.
fn is_zero(v: &CounterexampleValue) -> bool {
    match v {
        CounterexampleValue::Int(0) | CounterexampleValue::Uint(0) => true,
        CounterexampleValue::Float(f) => *f == 0.0,
        _ => false,
    }
}

/// Get the signed bounds for a given bit width.
fn signed_bounds(width: u32) -> (i128, i128) {
    if width == 128 {
        (i128::MIN, i128::MAX)
    } else {
        let max = (1i128 << (width - 1)) - 1;
        let min = -(1i128 << (width - 1));
        (min, max)
    }
}

/// Get the unsigned max for a given bit width.
fn unsigned_max(width: u32) -> u128 {
    if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Human-readable Rust constant for the maximum value of a type.
fn ty_max_const(ty: &Ty) -> String {
    match ty {
        Ty::Int { width: 8, signed: false } => "u8::MAX".to_string(),
        Ty::Int { width: 16, signed: false } => "u16::MAX".to_string(),
        Ty::Int { width: 32, signed: false } => "u32::MAX".to_string(),
        Ty::Int { width: 64, signed: false } => "u64::MAX".to_string(),
        Ty::Int { width: 128, signed: false } => "u128::MAX".to_string(),
        Ty::Int { width: 8, signed: true } => "i8::MAX".to_string(),
        Ty::Int { width: 16, signed: true } => "i16::MAX".to_string(),
        Ty::Int { width: 32, signed: true } => "i32::MAX".to_string(),
        Ty::Int { width: 64, signed: true } => "i64::MAX".to_string(),
        Ty::Int { width: 128, signed: true } => "i128::MAX".to_string(),
        _ => "MAX".to_string(),
    }
}

/// Human-readable Rust constant for the minimum value of a type.
fn ty_min_const(ty: &Ty) -> String {
    match ty {
        Ty::Int { signed: false, .. } => "0".to_string(),
        Ty::Int { width: 8, signed: true } => "i8::MIN".to_string(),
        Ty::Int { width: 16, signed: true } => "i16::MIN".to_string(),
        Ty::Int { width: 32, signed: true } => "i32::MIN".to_string(),
        Ty::Int { width: 64, signed: true } => "i64::MIN".to_string(),
        Ty::Int { width: 128, signed: true } => "i128::MIN".to_string(),
        _ => "MIN".to_string(),
    }
}

/// Human-readable type name.
fn ty_name(ty: &Ty) -> String {
    match ty {
        Ty::Int { width, signed: false } => format!("u{width}"),
        Ty::Int { width, signed: true } => format!("i{width}"),
        Ty::Bool => "bool".to_string(),
        _ => "unknown".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn overflow_add_i32() -> VcKind {
        VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::i32(), Ty::i32()),
        }
    }

    fn overflow_mul_u64() -> VcKind {
        VcKind::ArithmeticOverflow {
            op: BinOp::Mul,
            operand_tys: (Ty::Int { width: 64, signed: false }, Ty::Int { width: 64, signed: false }),
        }
    }

    fn cex_with(assignments: Vec<(&str, CounterexampleValue)>) -> Counterexample {
        Counterexample::new(
            assignments.into_iter().map(|(n, v)| (n.to_string(), v)).collect(),
        )
    }

    #[test]
    fn test_overflow_boundary_max_suggests_bound() {
        let cex = cex_with(vec![
            ("x", CounterexampleValue::Int(i32::MAX as i128)),
            ("y", CounterexampleValue::Int(1)),
        ]);
        let suggestions = CounterexampleAnalyzer::analyze(&overflow_add_i32(), &cex);

        assert!(!suggestions.is_empty(), "should produce at least one suggestion");
        let s = &suggestions[0];
        assert_eq!(s.precondition, "x < i32::MAX");
        assert_eq!(s.attribute, "#[requires(x < i32::MAX)]");
        assert!(s.reason.contains("addition"));
        assert!(s.confidence > 0.8);
    }

    #[test]
    fn test_overflow_boundary_min_suggests_bound() {
        let cex = cex_with(vec![
            ("a", CounterexampleValue::Int(i32::MIN as i128)),
            ("b", CounterexampleValue::Int(-1)),
        ]);
        let suggestions = CounterexampleAnalyzer::analyze(&overflow_add_i32(), &cex);

        assert!(!suggestions.is_empty());
        let s = &suggestions[0];
        assert_eq!(s.precondition, "a > i32::MIN");
        assert_eq!(s.attribute, "#[requires(a > i32::MIN)]");
    }

    #[test]
    fn test_overflow_non_boundary_suggests_range() {
        let cex = cex_with(vec![
            ("x", CounterexampleValue::Int(100)),
            ("y", CounterexampleValue::Int(200)),
        ]);
        let suggestions = CounterexampleAnalyzer::analyze(&overflow_add_i32(), &cex);

        assert_eq!(suggestions.len(), 1, "should produce generic range suggestion");
        let s = &suggestions[0];
        assert!(s.precondition.contains('+'));
        assert!(s.precondition.contains("i32::MAX"));
        assert!(s.confidence < 0.8, "generic suggestions should have lower confidence");
    }

    #[test]
    fn test_overflow_unsigned_max_suggests_bound() {
        let cex = cex_with(vec![
            ("n", CounterexampleValue::Uint(u64::MAX as u128)),
            ("m", CounterexampleValue::Uint(1)),
        ]);
        let suggestions = CounterexampleAnalyzer::analyze(&overflow_mul_u64(), &cex);

        assert!(!suggestions.is_empty());
        let s = &suggestions[0];
        assert_eq!(s.precondition, "n < u64::MAX");
    }

    #[test]
    fn test_division_by_zero_identifies_zero_var() {
        let cex = cex_with(vec![
            ("x", CounterexampleValue::Int(42)),
            ("y", CounterexampleValue::Int(0)),
        ]);
        let suggestions = CounterexampleAnalyzer::analyze(&VcKind::DivisionByZero, &cex);

        assert_eq!(suggestions.len(), 1);
        let s = &suggestions[0];
        assert_eq!(s.precondition, "y != 0");
        assert_eq!(s.attribute, "#[requires(y != 0)]");
        assert!(s.confidence >= 0.95);
    }

    #[test]
    fn test_remainder_by_zero() {
        let cex = cex_with(vec![
            ("dividend", CounterexampleValue::Uint(100)),
            ("divisor", CounterexampleValue::Uint(0)),
        ]);
        let suggestions = CounterexampleAnalyzer::analyze(&VcKind::RemainderByZero, &cex);

        assert_eq!(suggestions.len(), 1);
        let s = &suggestions[0];
        assert_eq!(s.precondition, "divisor != 0");
        assert!(s.vc_kind_tag.contains("remainder"));
    }

    #[test]
    fn test_division_by_zero_no_explicit_zero_fallback() {
        let cex = cex_with(vec![("result", CounterexampleValue::Int(42))]);
        let suggestions = CounterexampleAnalyzer::analyze(&VcKind::DivisionByZero, &cex);

        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].precondition, "divisor != 0");
        assert!(suggestions[0].confidence >= 0.9);
    }

    #[test]
    fn test_index_oob_with_named_vars() {
        let cex = cex_with(vec![
            ("index", CounterexampleValue::Uint(10)),
            ("len", CounterexampleValue::Uint(5)),
        ]);
        let suggestions =
            CounterexampleAnalyzer::analyze(&VcKind::IndexOutOfBounds, &cex);

        assert_eq!(suggestions.len(), 1);
        let s = &suggestions[0];
        assert_eq!(s.precondition, "index < len");
        assert_eq!(s.attribute, "#[requires(index < len)]");
        assert!(s.confidence >= 0.9);
    }

    #[test]
    fn test_index_oob_with_idx_shorthand() {
        let cex = cex_with(vec![
            ("idx", CounterexampleValue::Uint(100)),
            ("length", CounterexampleValue::Uint(50)),
        ]);
        let suggestions =
            CounterexampleAnalyzer::analyze(&VcKind::IndexOutOfBounds, &cex);

        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].precondition, "idx < length");
    }

    #[test]
    fn test_index_oob_no_len_var() {
        let cex = cex_with(vec![("i", CounterexampleValue::Uint(99))]);
        let suggestions =
            CounterexampleAnalyzer::analyze(&VcKind::IndexOutOfBounds, &cex);

        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].precondition, "i < len");
        assert!(suggestions[0].confidence < 0.8, "no len var -> lower confidence");
    }

    #[test]
    fn test_index_oob_no_recognizable_vars() {
        let cex = cex_with(vec![("x", CounterexampleValue::Uint(5))]);
        let suggestions =
            CounterexampleAnalyzer::analyze(&VcKind::IndexOutOfBounds, &cex);

        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].precondition, "index < len");
        assert!(suggestions[0].confidence <= 0.6);
    }

    #[test]
    fn test_slice_bounds_check() {
        let cex = cex_with(vec![
            ("index", CounterexampleValue::Uint(10)),
            ("size", CounterexampleValue::Uint(5)),
        ]);
        let suggestions =
            CounterexampleAnalyzer::analyze(&VcKind::SliceBoundsCheck, &cex);

        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].vc_kind_tag, "slice_bounds");
    }

    #[test]
    fn test_negation_overflow_at_min() {
        let ty = Ty::i32();
        let cex = cex_with(vec![("x", CounterexampleValue::Int(i32::MIN as i128))]);
        let suggestions =
            CounterexampleAnalyzer::analyze(&VcKind::NegationOverflow { ty }, &cex);

        assert_eq!(suggestions.len(), 1);
        let s = &suggestions[0];
        assert_eq!(s.precondition, "x != i32::MIN");
        assert!(s.confidence >= 0.95);
    }

    #[test]
    fn test_negation_overflow_not_at_min() {
        let ty = Ty::i32();
        let cex = cex_with(vec![("x", CounterexampleValue::Int(42))]);
        let suggestions =
            CounterexampleAnalyzer::analyze(&VcKind::NegationOverflow { ty }, &cex);

        assert!(suggestions.is_empty(), "non-MIN value should not trigger suggestion");
    }

    #[test]
    fn test_shift_overflow_exceeds_width() {
        let vc_kind = VcKind::ShiftOverflow {
            op: BinOp::Shl,
            operand_ty: Ty::u32(),
            shift_ty: Ty::u32(),
        };
        let cex = cex_with(vec![
            ("value", CounterexampleValue::Uint(1)),
            ("shift", CounterexampleValue::Uint(32)),
        ]);
        let suggestions = CounterexampleAnalyzer::analyze(&vc_kind, &cex);

        assert_eq!(suggestions.len(), 1);
        let s = &suggestions[0];
        assert_eq!(s.precondition, "shift < 32");
        assert!(s.reason.contains("bit width"));
    }

    #[test]
    fn test_shift_overflow_negative_amount() {
        let vc_kind = VcKind::ShiftOverflow {
            op: BinOp::Shr,
            operand_ty: Ty::i32(),
            shift_ty: Ty::i32(),
        };
        let cex = cex_with(vec![
            ("x", CounterexampleValue::Int(5)),
            ("amt", CounterexampleValue::Int(-1)),
        ]);
        let suggestions = CounterexampleAnalyzer::analyze(&vc_kind, &cex);

        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].precondition, "amt < 32");
    }

    #[test]
    fn test_cast_overflow_signed_to_unsigned() {
        let vc_kind = VcKind::CastOverflow {
            from_ty: Ty::i32(),
            to_ty: Ty::Int { width: 16, signed: false },
        };
        let cex = cex_with(vec![("x", CounterexampleValue::Int(-1))]);
        let suggestions = CounterexampleAnalyzer::analyze(&vc_kind, &cex);

        assert_eq!(suggestions.len(), 1);
        let s = &suggestions[0];
        assert!(s.precondition.contains("x >= 0"));
        assert!(s.precondition.contains("u16::MAX"));
    }

    #[test]
    fn test_cast_overflow_narrowing_signed() {
        let vc_kind = VcKind::CastOverflow {
            from_ty: Ty::Int { width: 32, signed: true },
            to_ty: Ty::Int { width: 8, signed: true },
        };
        let cex = cex_with(vec![("val", CounterexampleValue::Int(200))]);
        let suggestions = CounterexampleAnalyzer::analyze(&vc_kind, &cex);

        assert_eq!(suggestions.len(), 1);
        let s = &suggestions[0];
        assert!(s.precondition.contains("i8::MIN"));
        assert!(s.precondition.contains("i8::MAX"));
        assert!(s.reason.contains("i8"));
    }

    #[test]
    fn test_unknown_vc_kind_returns_empty() {
        let cex = cex_with(vec![("x", CounterexampleValue::Int(42))]);
        let suggestions = CounterexampleAnalyzer::analyze(&VcKind::Postcondition, &cex);
        assert!(suggestions.is_empty());
    }

    #[test]
    fn test_empty_counterexample() {
        let cex = Counterexample::new(vec![]);
        let suggestions = CounterexampleAnalyzer::analyze(&VcKind::DivisionByZero, &cex);
        // Should still produce a fallback suggestion
        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].precondition, "divisor != 0");
    }

    #[test]
    fn test_triggering_values_populated() {
        let cex = cex_with(vec![
            ("x", CounterexampleValue::Int(i32::MAX as i128)),
        ]);
        let suggestions = CounterexampleAnalyzer::analyze(&overflow_add_i32(), &cex);

        assert!(!suggestions.is_empty());
        assert!(!suggestions[0].triggering_values.is_empty());
        assert_eq!(suggestions[0].triggering_values[0].0, "x");
    }
}
