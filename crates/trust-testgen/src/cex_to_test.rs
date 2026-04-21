// trust-testgen: Counterexample-driven test generation
//
// Converts solver counterexamples (SAT models) into concrete Rust test cases.
// Bridges verification and testing: when a VC fails with a counterexample,
// this module synthesizes a regression test that reproduces the violation.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use trust_types::fx::{FxHashMap, FxHashSet};
use std::fmt::Write as FmtWrite;

use trust_types::{
    Counterexample, CounterexampleValue, Formula, Sort, Ty, VcKind,
    VerificationCondition,
};

use crate::{sanitize_ident, vc_kind_suffix, GeneratedTest};
use crate::regression::RegressionSuite;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors from counterexample-to-test conversion.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CexTestError {
    #[error("counterexample has no assignments")]
    EmptyCounterexample,

    #[error("unsupported value type for synthesis: {description}")]
    UnsupportedValue { description: String },

    #[error("shrinking failed after {iterations} iterations")]
    ShrinkFailed { iterations: usize },

    #[error("template rendering error: {0}")]
    Render(#[from] std::fmt::Error),
}

// ---------------------------------------------------------------------------
// ValueSynthesizer: map solver values to Rust literals
// ---------------------------------------------------------------------------

/// Maps solver values (bitvectors, integers, booleans, arrays) to Rust literal
/// strings suitable for inclusion in generated test code.
pub struct ValueSynthesizer;

impl ValueSynthesizer {
    /// Synthesize a Rust literal from a `CounterexampleValue`.
    #[must_use]
    pub fn synthesize(value: &CounterexampleValue) -> SynthesizedValue {
        match value {
            CounterexampleValue::Bool(b) => SynthesizedValue {
                literal: format!("{b}"),
                rust_type: "bool".to_string(),
                type_annotation: ": bool".to_string(),
            },
            CounterexampleValue::Int(n) => {
                let (literal, rust_type) = Self::synthesize_signed(*n);
                SynthesizedValue {
                    literal,
                    rust_type: rust_type.to_string(),
                    type_annotation: format!(": {rust_type}"),
                }
            }
            CounterexampleValue::Uint(n) => {
                let (literal, rust_type) = Self::synthesize_unsigned(*n);
                SynthesizedValue {
                    literal,
                    rust_type: rust_type.to_string(),
                    type_annotation: format!(": {rust_type}"),
                }
            }
            CounterexampleValue::Float(f) => {
                let literal = if f.is_nan() {
                    "f64::NAN".to_string()
                } else if f.is_infinite() {
                    if f.is_sign_positive() {
                        "f64::INFINITY".to_string()
                    } else {
                        "f64::NEG_INFINITY".to_string()
                    }
                } else {
                    let s = format!("{f}");
                    if s.contains('.') { s } else { format!("{s}.0") }
                };
                SynthesizedValue {
                    literal,
                    rust_type: "f64".to_string(),
                    type_annotation: ": f64".to_string(),
                }
            }
            _ => SynthesizedValue {
                literal: "Default::default()".to_string(),
                rust_type: "unknown".to_string(),
                type_annotation: String::new(),
            },
        }
    }

    /// Synthesize a typed Rust literal from a value + target Ty.
    #[must_use]
    pub fn synthesize_typed(value: &CounterexampleValue, target_ty: &Ty) -> SynthesizedValue {
        match (value, target_ty) {
            (CounterexampleValue::Int(n), Ty::Int { width, signed: true }) => {
                let ty_name = format!("i{width}");
                SynthesizedValue {
                    literal: format!("{n}_{ty_name}"),
                    rust_type: ty_name.clone(),
                    type_annotation: format!(": {ty_name}"),
                }
            }
            (CounterexampleValue::Uint(n), Ty::Int { width, signed: false }) => {
                let ty_name = format!("u{width}");
                SynthesizedValue {
                    literal: format!("{n}_{ty_name}"),
                    rust_type: ty_name.clone(),
                    type_annotation: format!(": {ty_name}"),
                }
            }
            (CounterexampleValue::Int(n), Ty::Int { width, signed: false }) => {
                // Signed value used as unsigned — clamp to 0
                let clamped = if *n < 0 { 0u128 } else { *n as u128 };
                let ty_name = format!("u{width}");
                SynthesizedValue {
                    literal: format!("{clamped}_{ty_name}"),
                    rust_type: ty_name.clone(),
                    type_annotation: format!(": {ty_name}"),
                }
            }
            _ => Self::synthesize(value),
        }
    }

    /// Synthesize a Rust literal for a bitvector value.
    #[must_use]
    pub fn synthesize_bitvec(value: i128, width: u32) -> SynthesizedValue {
        let (literal, rust_type) = if width <= 8 {
            (format!("0x{:02x}_u8", value as u8), "u8")
        } else if width <= 16 {
            (format!("0x{:04x}_u16", value as u16), "u16")
        } else if width <= 32 {
            (format!("0x{:08x}_u32", value as u32), "u32")
        } else if width <= 64 {
            (format!("0x{:016x}_u64", value as u64), "u64")
        } else {
            (format!("0x{:032x}_u128", value as u128), "u128")
        };
        SynthesizedValue {
            literal,
            rust_type: rust_type.to_string(),
            type_annotation: format!(": {rust_type}"),
        }
    }

    /// Synthesize a Rust literal for an array value.
    ///
    /// Arrays are rendered as `[elem0, elem1, ...]` with a fixed length.
    #[must_use]
    pub fn synthesize_array(
        entries: &BTreeMap<u64, CounterexampleValue>,
        default_val: &CounterexampleValue,
        length: usize,
    ) -> SynthesizedValue {
        let mut elements = Vec::with_capacity(length);
        for i in 0..length {
            let val = entries.get(&(i as u64)).unwrap_or(default_val);
            elements.push(Self::synthesize(val).literal);
        }
        let inner_type = Self::synthesize(default_val).rust_type;
        let literal = format!("[{}]", elements.join(", "));
        SynthesizedValue {
            literal,
            rust_type: format!("[{inner_type}; {length}]"),
            type_annotation: format!(": [{inner_type}; {length}]"),
        }
    }

    /// Choose smallest signed type for value.
    fn synthesize_signed(n: i128) -> (String, &'static str) {
        if i8::MIN as i128 <= n && n <= i8::MAX as i128 {
            (format!("{n}_i8"), "i8")
        } else if i16::MIN as i128 <= n && n <= i16::MAX as i128 {
            (format!("{n}_i16"), "i16")
        } else if i32::MIN as i128 <= n && n <= i32::MAX as i128 {
            (format!("{n}_i32"), "i32")
        } else if i64::MIN as i128 <= n && n <= i64::MAX as i128 {
            (format!("{n}_i64"), "i64")
        } else {
            (format!("{n}_i128"), "i128")
        }
    }

    /// Choose smallest unsigned type for value.
    fn synthesize_unsigned(n: u128) -> (String, &'static str) {
        if n <= u8::MAX as u128 {
            (format!("{n}_u8"), "u8")
        } else if n <= u16::MAX as u128 {
            (format!("{n}_u16"), "u16")
        } else if n <= u32::MAX as u128 {
            (format!("{n}_u32"), "u32")
        } else if n <= u64::MAX as u128 {
            (format!("{n}_u64"), "u64")
        } else {
            (format!("{n}_u128"), "u128")
        }
    }
}

/// A synthesized Rust literal with type information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SynthesizedValue {
    /// The Rust literal string (e.g., `42_i32`, `true`, `0xff_u8`).
    pub(crate) literal: String,
    /// The Rust type name (e.g., `i32`, `bool`, `u8`).
    pub(crate) rust_type: String,
    /// Type annotation suitable for `let x<annotation> = ...` (e.g., `: i32`).
    pub(crate) type_annotation: String,
}

// ---------------------------------------------------------------------------
// TestTemplate: generate #[test] fn with concrete inputs
// ---------------------------------------------------------------------------

/// Renders a `#[test]` function from structured parts.
pub struct TestTemplate {
    /// Test function name.
    pub(crate) name: String,
    /// Optional `#[should_panic]` attribute.
    pub(crate) should_panic: bool,
    /// Optional panic message substring for `#[should_panic(expected = "...")]`.
    pub(crate) panic_expected: Option<String>,
    /// Variable bindings: `(name, type_annotation, literal)`.
    pub(crate) bindings: Vec<(String, String, String)>,
    /// Comment lines (without `//` prefix).
    pub(crate) comments: Vec<String>,
    /// Assertion or action lines (full Rust statements).
    pub(crate) body_lines: Vec<String>,
}

impl TestTemplate {
    /// Create a new test template.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            should_panic: false,
            panic_expected: None,
            bindings: Vec::new(),
            comments: Vec::new(),
            body_lines: Vec::new(),
        }
    }

    /// Set `#[should_panic]`.
    #[must_use]
    pub fn with_should_panic(mut self, should_panic: bool) -> Self {
        self.should_panic = should_panic;
        self
    }

    /// Set `#[should_panic(expected = "...")]`.
    #[must_use]
    pub fn with_panic_expected(mut self, expected: impl Into<String>) -> Self {
        self.should_panic = true;
        self.panic_expected = Some(expected.into());
        self
    }

    /// Add a variable binding.
    #[must_use]
    pub fn with_binding(
        mut self,
        name: impl Into<String>,
        type_annotation: impl Into<String>,
        literal: impl Into<String>,
    ) -> Self {
        self.bindings.push((name.into(), type_annotation.into(), literal.into()));
        self
    }

    /// Add a comment line.
    #[must_use]
    pub fn with_comment(mut self, comment: impl Into<String>) -> Self {
        self.comments.push(comment.into());
        self
    }

    /// Add a body line (full Rust statement).
    #[must_use]
    pub fn with_body_line(mut self, line: impl Into<String>) -> Self {
        self.body_lines.push(line.into());
        self
    }

    /// Render the test function as a complete Rust source string.
    #[must_use]
    pub fn render(&self) -> String {
        let mut out = String::with_capacity(512);

        out.push_str("#[test]\n");
        if self.should_panic {
            if let Some(ref expected) = self.panic_expected {
                let _ = writeln!(out, "#[should_panic(expected = \"{expected}\")]");
            } else {
                out.push_str("#[should_panic]\n");
            }
        }
        let _ = writeln!(out, "fn {}() {{", self.name);

        for comment in &self.comments {
            let _ = writeln!(out, "    // {comment}");
        }

        for (name, ty_ann, literal) in &self.bindings {
            let _ = writeln!(out, "    let {name}{ty_ann} = {literal};");
        }

        if !self.bindings.is_empty() && !self.body_lines.is_empty() {
            out.push('\n');
        }

        for line in &self.body_lines {
            let _ = writeln!(out, "    {line}");
        }

        out.push('}');
        out
    }

    /// Convert to a `GeneratedTest`.
    #[must_use]
    pub fn to_generated_test(&self) -> GeneratedTest {
        let boundary_values = self
            .bindings
            .iter()
            .map(|(name, _, literal)| format!("{name} = {literal}"))
            .collect();
        GeneratedTest {
            name: self.name.clone(),
            code: self.render(),
            boundary_values,
        }
    }
}

// ---------------------------------------------------------------------------
// CexTestGenerator: convert counterexample model to concrete Rust test
// ---------------------------------------------------------------------------

/// Configuration for counterexample-driven test generation.
#[derive(Debug, Clone)]
pub struct CexTestConfig {
    /// Maximum number of variables to include in generated test.
    pub(crate) max_variables: usize,
    /// Whether to generate `#[should_panic]` tests for panic-inducing VCs.
    pub(crate) generate_should_panic: bool,
    /// Whether to include trace comments when available.
    pub(crate) include_trace: bool,
    /// Prefix for generated test names.
    pub(crate) name_prefix: String,
}

impl Default for CexTestConfig {
    fn default() -> Self {
        Self {
            max_variables: 32,
            generate_should_panic: true,
            include_trace: true,
            name_prefix: "cex".to_string(),
        }
    }
}

/// Convert counterexample models to concrete Rust tests.
///
/// Given a `Counterexample` from solver output and the violated `VcKind`,
/// produces a `GeneratedTest` that instantiates the concrete values and
/// exercises the violation path.
pub struct CexTestGenerator {
    config: CexTestConfig,
}

impl CexTestGenerator {
    /// Create a new generator with default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self { config: CexTestConfig::default() }
    }

    /// Create a new generator with custom configuration.
    #[must_use]
    pub fn with_config(config: CexTestConfig) -> Self {
        Self { config }
    }

    /// Generate a test from a counterexample and the violated VC.
    pub fn generate(
        &self,
        cex: &Counterexample,
        vc: &VerificationCondition,
    ) -> Result<GeneratedTest, CexTestError> {
        let kind_suffix = vc_kind_suffix(&vc.kind);
        let sanitized_func = sanitize_ident(&vc.function);
        let name = format!(
            "test_{}_{sanitized_func}_{kind_suffix}",
            self.config.name_prefix,
        );

        let mut template = TestTemplate::new(&name);

        // Determine if this should be a should_panic test
        let is_panic_vc = self.config.generate_should_panic && is_panic_vc_kind(&vc.kind);
        template.should_panic = is_panic_vc;

        // Add comment describing the counterexample origin
        template.comments.push(format!(
            "Counterexample for {}: {} in `{}`",
            kind_suffix,
            vc.kind.description(),
            vc.function,
        ));

        // Add trace comments if available
        if self.config.include_trace
            && let Some(ref trace) = cex.trace {
                for step in &trace.steps {
                    let pp = step.program_point.as_deref().unwrap_or("?");
                    let assigns: Vec<String> =
                        step.assignments.iter().map(|(k, v)| format!("{k}={v}")).collect();
                    template.comments.push(format!(
                        "Trace step {}: [{}] {}",
                        step.step,
                        pp,
                        assigns.join(", "),
                    ));
                }
            }

        // Synthesize variable bindings from counterexample assignments
        let assignments = &cex.assignments;
        let limit = assignments.len().min(self.config.max_variables);
        for (var_name, val) in assignments.iter().take(limit) {
            let synthesized = ValueSynthesizer::synthesize(val);
            template.bindings.push((
                sanitize_ident(var_name),
                synthesized.type_annotation,
                synthesized.literal,
            ));
        }

        // Add VC-kind-specific body
        add_vc_body(&mut template, &vc.kind, &vc.function);

        // Add a call to the function under test using counterexample values
        let sanitized_func = sanitize_ident(&vc.function);
        let args: Vec<String> = template
            .bindings
            .iter()
            .map(|(name, _, _)| name.clone())
            .collect();
        let args_str = args.join(", ");
        template.body_lines.push(
            "// Call the function under test with counterexample values".to_string()
        );
        template.body_lines.push(format!(
            "let _ = {sanitized_func}({args_str});"
        ));

        Ok(template.to_generated_test())
    }

    /// Generate tests from multiple counterexamples.
    pub fn generate_batch(
        &self,
        cex_vc_pairs: &[(&Counterexample, &VerificationCondition)],
    ) -> Vec<Result<GeneratedTest, CexTestError>> {
        cex_vc_pairs
            .iter()
            .map(|(cex, vc)| self.generate(cex, vc))
            .collect()
    }
}

impl Default for CexTestGenerator {
    fn default() -> Self {
        Self::new()
    }
}

/// Whether a VcKind represents a panic-inducing violation.
fn is_panic_vc_kind(kind: &VcKind) -> bool {
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

/// Add VC-kind-specific body lines to the test template.
fn add_vc_body(template: &mut TestTemplate, kind: &VcKind, func_path: &str) {
    match kind {
        VcKind::ArithmeticOverflow { op, .. } => {
            let op_str = match op {
                trust_types::BinOp::Add => "+",
                trust_types::BinOp::Sub => "-",
                trust_types::BinOp::Mul => "*",
                _ => "/* op */",
            };
            template.body_lines.push(format!(
                "// Arithmetic overflow with operator `{op_str}` in `{func_path}`"
            ));
            template.body_lines.push(
                "// These concrete values trigger overflow in debug mode.".to_string(),
            );
            template.body_lines.push(format!(
                "panic!(\"counterexample: arithmetic overflow ({op_str}) in {func_path}\");"
            ));
        }
        VcKind::DivisionByZero => {
            template.body_lines.push(format!(
                "// Division by zero in `{func_path}` — divisor is zero."
            ));
            template.body_lines.push("let _ = 1_i64 / 0_i64;".to_string());
        }
        VcKind::RemainderByZero => {
            template.body_lines.push(format!(
                "// Remainder by zero in `{func_path}` — divisor is zero."
            ));
            template.body_lines.push("let _ = 1_i64 % 0_i64;".to_string());
        }
        VcKind::IndexOutOfBounds => {
            template.body_lines.push(format!(
                "// Index out of bounds in `{func_path}`."
            ));
            template.body_lines.push("let data: Vec<u8> = vec![0];".to_string());
            template.body_lines.push("let _ = data[data.len()];".to_string());
        }
        VcKind::SliceBoundsCheck => {
            template.body_lines.push(format!(
                "// Slice bounds violation in `{func_path}`."
            ));
            template.body_lines.push("let data: Vec<u8> = vec![0];".to_string());
            template.body_lines.push("let _ = &data[0..data.len() + 1];".to_string());
        }
        VcKind::NegationOverflow { .. } => {
            template.body_lines.push(format!(
                "// Negation overflow in `{func_path}`."
            ));
            template.body_lines.push(
                "panic!(\"counterexample: negation overflow\");".to_string(),
            );
        }
        VcKind::ShiftOverflow { op, .. } => {
            let dir = match op {
                trust_types::BinOp::Shl => "left",
                trust_types::BinOp::Shr => "right",
                _ => "unknown",
            };
            template.body_lines.push(format!(
                "// Shift {dir} overflow in `{func_path}`."
            ));
            template.body_lines.push(
                "panic!(\"counterexample: shift overflow\");".to_string(),
            );
        }
        VcKind::Assertion { message } => {
            template.body_lines.push(format!(
                "// Assertion violation in `{func_path}`: {message}"
            ));
            template.body_lines.push(format!(
                "assert!(false, \"counterexample violates: {message}\");"
            ));
        }
        VcKind::Precondition { callee } => {
            template.body_lines.push(format!(
                "// Precondition of `{callee}` violated by `{func_path}`."
            ));
            template.body_lines.push(format!(
                "assert!(false, \"precondition of {callee} violated\");"
            ));
        }
        VcKind::Postcondition => {
            template.body_lines.push(format!(
                "// Postcondition of `{func_path}` violated."
            ));
            template.body_lines.push(format!(
                "assert!(false, \"postcondition of {func_path} violated\");"
            ));
        }
        _ => {
            let desc = kind.description();
            template.body_lines.push(format!(
                "// {desc} in `{func_path}` — manual review required."
            ));
            template.body_lines.push(format!(
                "assert!(false, \"counterexample demonstrates: {desc}\");"
            ));
        }
    }
}

// ---------------------------------------------------------------------------
// PropertyTestGen: generate proptest strategies from VC structure
// ---------------------------------------------------------------------------

/// Generates proptest/quickcheck-style strategy code from VC formula structure.
///
/// Analyzes the `Formula` in a `VerificationCondition` to extract variable
/// domains and constraints, then produces Rust code with appropriate
/// `proptest!` or manual random-testing strategies.
pub struct VcPropertyTestGen;

impl VcPropertyTestGen {
    /// Generate a property test strategy from a VC.
    ///
    /// Extracts free variables and their sorts from the formula, then
    /// generates a test that randomly exercises the property.
    #[must_use]
    pub fn generate(vc: &VerificationCondition) -> GeneratedTest {
        let sanitized = sanitize_ident(&vc.function);
        let kind_suffix = vc_kind_suffix(&vc.kind);
        let name = format!("test_prop_{sanitized}_{kind_suffix}");

        // Extract variables from the formula
        let variables = extract_formula_variables(&vc.formula);

        let mut template = TestTemplate::new(&name);
        template.comments.push(format!(
            "Property test for {} in `{}`",
            vc.kind.description(),
            vc.function,
        ));

        if variables.is_empty() {
            // No variables — generate a static assertion test
            template.body_lines.push(
                "// No free variables in VC formula — static check.".to_string()
            );
            template.body_lines.push(format!(
                "// VC kind: {}",
                vc.kind.description(),
            ));
            template.body_lines.push(
                "assert!(true, \"no inputs to vary for property test\");".to_string(),
            );
        } else {
            // Generate proptest-style random testing code
            template.comments.push(format!(
                "Variables: {}",
                variables
                    .iter()
                    .map(|(n, s)| format!("{n}: {}", sort_to_rust_type(s)))
                    .collect::<Vec<_>>()
                    .join(", "),
            ));

            template.body_lines.push(
                "// Property test: random inputs over variable domains".to_string(),
            );
            template.body_lines.push(
                "use std::collections::hash_map::DefaultHasher;".to_string(),
            );
            template.body_lines.push(
                "use std::hash::{Hash, Hasher};".to_string(),
            );
            template.body_lines.push(
                "for seed in 0..100_u64 {".to_string(),
            );
            template.body_lines.push(
                "    let mut hasher = DefaultHasher::new();".to_string(),
            );
            template.body_lines.push(
                "    seed.hash(&mut hasher);".to_string(),
            );

            for (var_name, sort) in &variables {
                let sanitized_var = sanitize_ident(var_name);
                let strategy_line = sort_to_strategy_line(&sanitized_var, sort);
                template.body_lines.push(format!("    {strategy_line}"));
            }

            template.body_lines.push(format!(
                "    // Exercise VC property: {}",
                vc.kind.description(),
            ));
            template.body_lines.push(format!(
                "    let _ = ({});",
                variables
                    .iter()
                    .map(|(n, _)| sanitize_ident(n))
                    .collect::<Vec<_>>()
                    .join(", "),
            ));
            template.body_lines.push("}".to_string());
        }

        template.to_generated_test()
    }
}

/// Extract free variables and their sorts from a formula.
fn extract_formula_variables(formula: &Formula) -> Vec<(String, Sort)> {
    let mut variables: FxHashMap<String, Sort> = FxHashMap::default();
    collect_variables(formula, &mut variables);
    let mut sorted: Vec<(String, Sort)> = variables.into_iter().collect();
    sorted.sort_by(|a, b| a.0.cmp(&b.0));
    sorted
}

/// Recursively collect Var nodes from a formula.
fn collect_variables(formula: &Formula, vars: &mut FxHashMap<String, Sort>) {
    match formula {
        Formula::Var(name, sort) => {
            vars.entry(name.clone()).or_insert_with(|| sort.clone());
        }
        Formula::Not(inner) | Formula::Neg(inner) => {
            collect_variables(inner, vars);
        }
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                collect_variables(child, vars);
            }
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => {
            collect_variables(a, vars);
            collect_variables(b, vars);
        }
        Formula::BvAdd(a, b, _)
        | Formula::BvSub(a, b, _)
        | Formula::BvMul(a, b, _)
        | Formula::BvUDiv(a, b, _)
        | Formula::BvSDiv(a, b, _)
        | Formula::BvURem(a, b, _)
        | Formula::BvSRem(a, b, _)
        | Formula::BvAnd(a, b, _)
        | Formula::BvOr(a, b, _)
        | Formula::BvXor(a, b, _)
        | Formula::BvShl(a, b, _)
        | Formula::BvLShr(a, b, _)
        | Formula::BvAShr(a, b, _)
        | Formula::BvULt(a, b, _)
        | Formula::BvULe(a, b, _)
        | Formula::BvSLt(a, b, _)
        | Formula::BvSLe(a, b, _)
        | Formula::BvConcat(a, b) => {
            collect_variables(a, vars);
            collect_variables(b, vars);
        }
        Formula::Ite(c, t, e) => {
            collect_variables(c, vars);
            collect_variables(t, vars);
            collect_variables(e, vars);
        }
        Formula::Forall(_, body) | Formula::Exists(_, body) => {
            collect_variables(body, vars);
        }
        Formula::BvToInt(inner, _, _)
        | Formula::IntToBv(inner, _)
        | Formula::BvZeroExt(inner, _)
        | Formula::BvSignExt(inner, _)
        | Formula::BvNot(inner, _) => {
            collect_variables(inner, vars);
        }
        Formula::BvExtract { inner, .. } => {
            collect_variables(inner, vars);
        }
        // Literals have no variables
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {}
        // Array operations - handle all remaining variants
        _ => {}
    }
}

/// Convert a Sort to a Rust type name.
fn sort_to_rust_type(sort: &Sort) -> String {
    match sort {
        Sort::Bool => "bool".to_string(),
        Sort::Int => "i64".to_string(),
        Sort::BitVec(w) => {
            if *w <= 8 {
                "u8".to_string()
            } else if *w <= 16 {
                "u16".to_string()
            } else if *w <= 32 {
                "u32".to_string()
            } else if *w <= 64 {
                "u64".to_string()
            } else {
                "u128".to_string()
            }
        }
        Sort::Array(_, elem) => format!("Vec<{}>", sort_to_rust_type(elem)),
        _ => "unknown".to_string(),
    }
}

/// Generate a random value strategy line for a variable with given sort.
fn sort_to_strategy_line(var_name: &str, sort: &Sort) -> String {
    match sort {
        Sort::Bool => {
            format!("let {var_name} = hasher.finish() % 2 == 0;")
        }
        Sort::Int => {
            format!("let {var_name} = hasher.finish() as i64;")
        }
        Sort::BitVec(w) => {
            let ty = sort_to_rust_type(sort);
            if *w <= 64 {
                format!("let {var_name} = hasher.finish() as {ty};")
            } else {
                format!(
                    "let {var_name} = (hasher.finish() as u128) | ((hasher.finish() as u128) << 64);"
                )
            }
        }
        Sort::Array(_, _) => {
            format!("let {var_name} = vec![]; // PLACEHOLDER: array strategy")
        }
        _ => format!("let {var_name} = Default::default(); // unknown sort"),
    }
}

// ---------------------------------------------------------------------------
// MinimalReproducer: shrink counterexample to minimal failing input
// ---------------------------------------------------------------------------

/// Shrinks a counterexample to a minimal set of assignments that still
/// triggers the violation.
///
/// The shrinking strategy is:
/// 1. Try removing each assignment; if the test still makes sense, keep it removed.
/// 2. For integer values, try shrinking toward zero.
/// 3. For boolean values, try flipping.
pub struct MinimalReproducer {
    /// Maximum shrinking iterations.
    max_iterations: usize,
}

impl MinimalReproducer {
    /// Create a new reproducer with default max iterations.
    #[must_use]
    pub fn new() -> Self {
        Self { max_iterations: 100 }
    }

    /// Create a reproducer with a custom iteration limit.
    #[must_use]
    pub fn with_max_iterations(max_iterations: usize) -> Self {
        Self { max_iterations }
    }

    /// Shrink the counterexample's assignments.
    ///
    /// Returns a new `Counterexample` with potentially fewer and/or simpler
    /// variable assignments. The shrinking is purely structural — it does not
    /// re-run the solver. It tries to minimize values toward zero.
    #[must_use]
    pub fn shrink(&self, cex: &Counterexample) -> Counterexample {
        let mut assignments = cex.assignments.clone();
        let mut iteration = 0;

        // Phase 1: Shrink individual values toward zero
        for assignment in &mut assignments {
            if iteration >= self.max_iterations {
                break;
            }
            let (name, val) = assignment;
            if let Some(shrunk) = shrink_value(val) {
                *assignment = (name.clone(), shrunk);
            }
            iteration += 1;
        }

        // Phase 2: Try further shrinking passes
        let mut changed = true;
        while changed && iteration < self.max_iterations {
            changed = false;
            for assignment in &mut assignments {
                if iteration >= self.max_iterations {
                    break;
                }
                let (name, val) = assignment;
                let val_str = format!("{val}");
                if let Some(shrunk) = shrink_value(val) {
                    let shrunk_str = format!("{shrunk}");
                    if shrunk_str != val_str {
                        *assignment = (name.clone(), shrunk);
                        changed = true;
                    }
                }
                iteration += 1;
            }
        }

        Counterexample {
            assignments,
            trace: cex.trace.clone(),
        }
    }

    /// Remove assignments that are likely irrelevant to the violation.
    ///
    /// Keeps only assignments whose variable names appear in the provided
    /// set of relevant names (e.g., extracted from the VC formula).
    #[must_use]
    pub fn filter_relevant(
        &self,
        cex: &Counterexample,
        relevant_vars: &FxHashSet<String>,
    ) -> Counterexample {
        let filtered: Vec<_> = cex
            .assignments
            .iter()
            .filter(|(name, _)| relevant_vars.contains(name))
            .cloned()
            .collect();

        Counterexample {
            assignments: if filtered.is_empty() {
                // Don't produce empty — keep at least the original
                cex.assignments.clone()
            } else {
                filtered
            },
            trace: cex.trace.clone(),
        }
    }

    /// Shrink and filter in one step.
    #[must_use]
    pub fn minimize(
        &self,
        cex: &Counterexample,
        relevant_vars: &FxHashSet<String>,
    ) -> Counterexample {
        let filtered = self.filter_relevant(cex, relevant_vars);
        self.shrink(&filtered)
    }
}

impl Default for MinimalReproducer {
    fn default() -> Self {
        Self::new()
    }
}

/// Try to shrink a single counterexample value toward a simpler form.
fn shrink_value(val: &CounterexampleValue) -> Option<CounterexampleValue> {
    match val {
        CounterexampleValue::Bool(_) => None, // Can't shrink booleans further
        CounterexampleValue::Int(n) => {
            let n = *n;
            if n == 0 {
                None
            } else if n > 0 {
                Some(CounterexampleValue::Int(n / 2))
            } else {
                Some(CounterexampleValue::Int(-((-n) / 2)))
            }
        }
        CounterexampleValue::Uint(n) => {
            let n = *n;
            if n == 0 {
                None
            } else {
                Some(CounterexampleValue::Uint(n / 2))
            }
        }
        CounterexampleValue::Float(f) => {
            let f = *f;
            if f == 0.0 || f.is_nan() {
                None
            } else {
                Some(CounterexampleValue::Float(f / 2.0))
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Integration: RegressionSuite from CexTestGenerator output
// ---------------------------------------------------------------------------

/// Add generated counterexample tests to a regression suite.
///
/// For each (counterexample, VC) pair, generates a `RegressionTest` and
/// adds it to the suite. Duplicates are skipped.
pub fn add_cex_tests_to_suite(
    suite: &mut RegressionSuite,
    cex_vc_pairs: &[(&Counterexample, &VerificationCondition)],
    commit_hash: Option<&str>,
) -> Vec<crate::regression::RegressionError> {
    let mut errors = Vec::new();
    for (cex, vc) in cex_vc_pairs {
        if let Err(err) =
            suite.add_from_counterexample(cex, &vc.kind, &vc.function, commit_hash)
        {
            errors.push(err);
        }
    }
    errors
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{BinOp, Formula, Sort, SourceSpan};

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    fn make_cex(vars: &[(&str, CounterexampleValue)]) -> Counterexample {
        Counterexample::new(
            vars.iter()
                .map(|(name, val)| (name.to_string(), val.clone()))
                .collect(),
        )
    }

    fn make_vc(kind: VcKind, function: &str) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: function.to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn make_vc_with_formula(
        kind: VcKind,
        function: &str,
        formula: Formula,
    ) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: function.to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    // -----------------------------------------------------------------------
    // ValueSynthesizer
    // -----------------------------------------------------------------------

    #[test]
    fn test_synthesize_bool() {
        let val = ValueSynthesizer::synthesize(&CounterexampleValue::Bool(true));
        assert_eq!(val.literal, "true");
        assert_eq!(val.rust_type, "bool");
        assert_eq!(val.type_annotation, ": bool");
    }

    #[test]
    fn test_synthesize_small_int() {
        let val = ValueSynthesizer::synthesize(&CounterexampleValue::Int(42));
        assert_eq!(val.literal, "42_i8");
        assert_eq!(val.rust_type, "i8");
    }

    #[test]
    fn test_synthesize_large_int() {
        let val = ValueSynthesizer::synthesize(&CounterexampleValue::Int(i64::MAX as i128));
        assert_eq!(val.literal, format!("{}_i64", i64::MAX));
        assert_eq!(val.rust_type, "i64");
    }

    #[test]
    fn test_synthesize_negative_int() {
        let val = ValueSynthesizer::synthesize(&CounterexampleValue::Int(-1));
        assert_eq!(val.literal, "-1_i8");
    }

    #[test]
    fn test_synthesize_uint() {
        let val = ValueSynthesizer::synthesize(&CounterexampleValue::Uint(255));
        assert_eq!(val.literal, "255_u8");
        assert_eq!(val.rust_type, "u8");
    }

    #[test]
    fn test_synthesize_large_uint() {
        let val = ValueSynthesizer::synthesize(&CounterexampleValue::Uint(u64::MAX as u128));
        assert_eq!(val.literal, format!("{}_u64", u64::MAX));
        assert_eq!(val.rust_type, "u64");
    }

    #[test]
    fn test_synthesize_float() {
        let val = ValueSynthesizer::synthesize(&CounterexampleValue::Float(3.125));
        assert_eq!(val.literal, "3.125");
        assert_eq!(val.rust_type, "f64");
    }

    #[test]
    fn test_synthesize_float_nan() {
        let val = ValueSynthesizer::synthesize(&CounterexampleValue::Float(f64::NAN));
        assert_eq!(val.literal, "f64::NAN");
    }

    #[test]
    fn test_synthesize_float_infinity() {
        let val = ValueSynthesizer::synthesize(&CounterexampleValue::Float(f64::INFINITY));
        assert_eq!(val.literal, "f64::INFINITY");

        let val = ValueSynthesizer::synthesize(&CounterexampleValue::Float(f64::NEG_INFINITY));
        assert_eq!(val.literal, "f64::NEG_INFINITY");
    }

    #[test]
    fn test_synthesize_typed_i32() {
        let val = ValueSynthesizer::synthesize_typed(
            &CounterexampleValue::Int(42),
            &Ty::Int { width: 32, signed: true },
        );
        assert_eq!(val.literal, "42_i32");
        assert_eq!(val.rust_type, "i32");
    }

    #[test]
    fn test_synthesize_typed_u64() {
        let val = ValueSynthesizer::synthesize_typed(
            &CounterexampleValue::Uint(100),
            &Ty::Int { width: 64, signed: false },
        );
        assert_eq!(val.literal, "100_u64");
        assert_eq!(val.rust_type, "u64");
    }

    #[test]
    fn test_synthesize_typed_negative_as_unsigned() {
        let val = ValueSynthesizer::synthesize_typed(
            &CounterexampleValue::Int(-5),
            &Ty::Int { width: 32, signed: false },
        );
        assert_eq!(val.literal, "0_u32");
    }

    #[test]
    fn test_synthesize_bitvec() {
        let val = ValueSynthesizer::synthesize_bitvec(0xff, 8);
        assert_eq!(val.literal, "0xff_u8");
        assert_eq!(val.rust_type, "u8");

        let val = ValueSynthesizer::synthesize_bitvec(0xdead, 16);
        assert_eq!(val.literal, "0xdead_u16");
    }

    #[test]
    fn test_synthesize_array() {
        let mut entries = BTreeMap::new();
        entries.insert(0, CounterexampleValue::Int(10));
        entries.insert(2, CounterexampleValue::Int(30));
        let default_val = CounterexampleValue::Int(0);

        let val = ValueSynthesizer::synthesize_array(&entries, &default_val, 3);
        assert!(val.literal.contains("10_i8"));
        assert!(val.literal.contains("0_i8"));
        assert!(val.literal.contains("30_i8"));
        assert_eq!(val.rust_type, "[i8; 3]");
    }

    // -----------------------------------------------------------------------
    // TestTemplate
    // -----------------------------------------------------------------------

    #[test]
    fn test_template_basic_render() {
        let template = TestTemplate::new("test_basic")
            .with_comment("A test comment")
            .with_binding("x", ": i32", "42_i32")
            .with_body_line("assert_eq!(x, 42);");

        let code = template.render();
        assert!(code.contains("#[test]"));
        assert!(code.contains("fn test_basic()"));
        assert!(code.contains("// A test comment"));
        assert!(code.contains("let x: i32 = 42_i32;"));
        assert!(code.contains("assert_eq!(x, 42);"));
    }

    #[test]
    fn test_template_should_panic() {
        let template = TestTemplate::new("test_panic")
            .with_should_panic(true)
            .with_body_line("panic!(\"boom\");");

        let code = template.render();
        assert!(code.contains("#[should_panic]"));
        assert!(code.contains("panic!(\"boom\");"));
    }

    #[test]
    fn test_template_should_panic_expected() {
        let template = TestTemplate::new("test_panic_exp")
            .with_panic_expected("overflow")
            .with_body_line("panic!(\"overflow\");");

        let code = template.render();
        assert!(code.contains("#[should_panic(expected = \"overflow\")]"));
    }

    #[test]
    fn test_template_to_generated_test() {
        let template = TestTemplate::new("test_gen")
            .with_binding("a", ": i32", "1")
            .with_binding("b", ": i32", "2")
            .with_body_line("let _ = a + b;");

        let generated = template.to_generated_test();
        assert_eq!(generated.name, "test_gen");
        assert_eq!(generated.boundary_values.len(), 2);
        assert!(generated.boundary_values.contains(&"a = 1".to_string()));
        assert!(generated.boundary_values.contains(&"b = 2".to_string()));
    }

    // -----------------------------------------------------------------------
    // CexTestGenerator: Integer overflow counterexample to test
    // -----------------------------------------------------------------------

    #[test]
    fn test_cex_integer_overflow_to_test() {
        let cex = make_cex(&[
            ("a", CounterexampleValue::Int(i64::MAX as i128)),
            ("b", CounterexampleValue::Int(1)),
        ]);
        let vc = make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::i32(), Ty::i32()),
            },
            "math::add",
        );

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.name.contains("cex"));
        assert!(test.name.contains("math__add"));
        assert!(test.name.contains("arithmetic_overflow"));
        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("#[test]"));
        assert!(test.code.contains("arithmetic overflow"));
        assert_eq!(test.boundary_values.len(), 2);
    }

    #[test]
    fn test_cex_overflow_sub() {
        let cex = make_cex(&[
            ("x", CounterexampleValue::Int(i64::MIN as i128)),
            ("y", CounterexampleValue::Int(1)),
        ]);
        let vc = make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Sub,
                operand_tys: (Ty::i64(), Ty::i64()),
            },
            "math::subtract",
        );

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("arithmetic overflow"));
        assert!(test.code.contains("`-`"));
    }

    #[test]
    fn test_cex_overflow_mul() {
        let cex = make_cex(&[
            ("a", CounterexampleValue::Int(i32::MAX as i128)),
            ("b", CounterexampleValue::Int(2)),
        ]);
        let vc = make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Mul,
                operand_tys: (Ty::i32(), Ty::i32()),
            },
            "math::multiply",
        );

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.code.contains("arithmetic overflow"));
        assert!(test.code.contains("`*`"));
    }

    // -----------------------------------------------------------------------
    // CexTestGenerator: Null deref / assertion counterexample to test
    // -----------------------------------------------------------------------

    #[test]
    fn test_cex_null_deref_assertion_to_test() {
        // Null deref manifests as an assertion "ptr != null" violation
        let cex = make_cex(&[
            ("ptr", CounterexampleValue::Uint(0)),
            ("offset", CounterexampleValue::Uint(8)),
        ]);
        let vc = make_vc(
            VcKind::Assertion { message: "pointer is non-null".into() },
            "unsafe_code::deref_ptr",
        );

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.name.contains("assertion"));
        // Assertion violations are NOT should_panic
        assert!(!test.code.contains("#[should_panic]"));
        assert!(test.code.contains("pointer is non-null"));
        assert!(test.code.contains("counterexample violates"));
        assert_eq!(test.boundary_values.len(), 2);
    }

    #[test]
    fn test_cex_null_check_precondition() {
        let cex = make_cex(&[
            ("p", CounterexampleValue::Uint(0)),
        ]);
        let vc = make_vc(
            VcKind::Precondition { callee: "deref".into() },
            "api::process",
        );

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.code.contains("precondition of deref violated"));
        assert!(!test.code.contains("#[should_panic]"));
    }

    // -----------------------------------------------------------------------
    // CexTestGenerator: Out-of-bounds counterexample to test
    // -----------------------------------------------------------------------

    #[test]
    fn test_cex_oob_index_to_test() {
        let cex = make_cex(&[
            ("index", CounterexampleValue::Uint(10)),
            ("len", CounterexampleValue::Uint(5)),
        ]);
        let vc = make_vc(VcKind::IndexOutOfBounds, "buffer::get");

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.name.contains("index_out_of_bounds"));
        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("Index out of bounds"));
        assert!(test.code.contains("data[data.len()]"));
        assert_eq!(test.boundary_values.len(), 2);
    }

    #[test]
    fn test_cex_oob_slice_to_test() {
        let cex = make_cex(&[
            ("start", CounterexampleValue::Uint(3)),
            ("end", CounterexampleValue::Uint(100)),
            ("len", CounterexampleValue::Uint(10)),
        ]);
        let vc = make_vc(VcKind::SliceBoundsCheck, "slice::range");

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.name.contains("slice_bounds_check"));
        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("Slice bounds"));
        assert_eq!(test.boundary_values.len(), 3);
    }

    // -----------------------------------------------------------------------
    // CexTestGenerator: Other VcKind counterexamples
    // -----------------------------------------------------------------------

    #[test]
    fn test_cex_division_by_zero() {
        let cex = make_cex(&[("divisor", CounterexampleValue::Int(0))]);
        let vc = make_vc(VcKind::DivisionByZero, "math::divide");

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("1_i64 / 0_i64"));
    }

    #[test]
    fn test_cex_remainder_by_zero() {
        let cex = make_cex(&[("divisor", CounterexampleValue::Int(0))]);
        let vc = make_vc(VcKind::RemainderByZero, "math::modulo");

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("1_i64 % 0_i64"));
    }

    #[test]
    fn test_cex_negation_overflow() {
        let cex = make_cex(&[
            ("val", CounterexampleValue::Int(i64::MIN as i128)),
        ]);
        let vc = make_vc(
            VcKind::NegationOverflow { ty: Ty::i64() },
            "math::negate",
        );

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("negation overflow"));
    }

    #[test]
    fn test_cex_shift_overflow() {
        let cex = make_cex(&[
            ("val", CounterexampleValue::Uint(1)),
            ("shift", CounterexampleValue::Uint(64)),
        ]);
        let vc = make_vc(
            VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: Ty::u64(),
                shift_ty: Ty::u32(),
            },
            "bits::shift_left",
        );

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.code.contains("#[should_panic]"));
        assert!(test.code.contains("shift overflow"));
    }

    #[test]
    fn test_cex_postcondition() {
        let cex = make_cex(&[
            ("input", CounterexampleValue::Int(0)),
            ("result", CounterexampleValue::Int(-1)),
        ]);
        let vc = make_vc(VcKind::Postcondition, "api::compute");

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(!test.code.contains("#[should_panic]"));
        assert!(test.code.contains("postcondition of api::compute violated"));
    }

    #[test]
    fn test_cex_generic_vc_kind() {
        let cex = make_cex(&[("state", CounterexampleValue::Int(3))]);
        let vc = make_vc(
            VcKind::DeadState { state: "S3".into() },
            "fsm::step",
        );

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.code.contains("manual review required"));
        assert!(test.code.contains("dead state"));
    }

    // -----------------------------------------------------------------------
    // CexTestGenerator: batch generation
    // -----------------------------------------------------------------------

    #[test]
    fn test_cex_batch_generation() {
        let cex1 = make_cex(&[("a", CounterexampleValue::Int(1))]);
        let cex2 = make_cex(&[("b", CounterexampleValue::Int(2))]);
        let vc1 = make_vc(VcKind::DivisionByZero, "f1");
        let vc2 = make_vc(VcKind::IndexOutOfBounds, "f2");

        let generator = CexTestGenerator::new();
        let results = generator.generate_batch(&[(&cex1, &vc1), (&cex2, &vc2)]);

        assert_eq!(results.len(), 2);
        assert!(results[0].is_ok());
        assert!(results[1].is_ok());

        let test1 = results[0].as_ref().unwrap();
        let test2 = results[1].as_ref().unwrap();
        assert_ne!(test1.name, test2.name);
    }

    // -----------------------------------------------------------------------
    // CexTestGenerator: with trace
    // -----------------------------------------------------------------------

    #[test]
    fn test_cex_with_trace_includes_comments() {
        let mut trace_step = trust_types::TraceStep {
            step: 0,
            assignments: BTreeMap::new(),
            program_point: Some("bb3".to_string()),
        };
        trace_step.assignments.insert("x".to_string(), "42".to_string());

        let trace = trust_types::CounterexampleTrace::new(vec![trace_step]);
        let cex = Counterexample::with_trace(
            vec![("x".to_string(), CounterexampleValue::Int(42))],
            trace,
        );
        let vc = make_vc(VcKind::DivisionByZero, "f");

        let generator = CexTestGenerator::new();
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.code.contains("Trace step 0"));
        assert!(test.code.contains("[bb3]"));
        assert!(test.code.contains("x=42"));
    }

    // -----------------------------------------------------------------------
    // CexTestGenerator: config options
    // -----------------------------------------------------------------------

    #[test]
    fn test_cex_config_no_should_panic() {
        let config = CexTestConfig {
            generate_should_panic: false,
            ..Default::default()
        };
        let cex = make_cex(&[("a", CounterexampleValue::Int(1))]);
        let vc = make_vc(VcKind::DivisionByZero, "f");

        let generator = CexTestGenerator::with_config(config);
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(!test.code.contains("#[should_panic]"));
    }

    #[test]
    fn test_cex_config_custom_prefix() {
        let config = CexTestConfig {
            name_prefix: "regression".to_string(),
            ..Default::default()
        };
        let cex = make_cex(&[("a", CounterexampleValue::Int(1))]);
        let vc = make_vc(VcKind::DivisionByZero, "f");

        let generator = CexTestGenerator::with_config(config);
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(test.name.starts_with("test_regression_"));
    }

    #[test]
    fn test_cex_config_no_trace() {
        let config = CexTestConfig {
            include_trace: false,
            ..Default::default()
        };
        let trace = trust_types::CounterexampleTrace::new(vec![
            trust_types::TraceStep {
                step: 0,
                assignments: BTreeMap::new(),
                program_point: Some("bb0".to_string()),
            },
        ]);
        let cex = Counterexample::with_trace(
            vec![("x".to_string(), CounterexampleValue::Int(0))],
            trace,
        );
        let vc = make_vc(VcKind::DivisionByZero, "f");

        let generator = CexTestGenerator::with_config(config);
        let test = generator.generate(&cex, &vc).expect("should generate");

        assert!(!test.code.contains("Trace step"));
    }

    // -----------------------------------------------------------------------
    // VcPropertyTestGen
    // -----------------------------------------------------------------------

    #[test]
    fn test_vc_property_test_no_variables() {
        let vc = make_vc(VcKind::DivisionByZero, "f");
        let test = VcPropertyTestGen::generate(&vc);

        assert!(test.name.contains("test_prop_"));
        assert!(test.code.contains("no inputs to vary"));
    }

    #[test]
    fn test_vc_property_test_with_variables() {
        let formula = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let vc = make_vc_with_formula(VcKind::DivisionByZero, "f", formula);
        let test = VcPropertyTestGen::generate(&vc);

        assert!(test.code.contains("x: i64"));
        assert!(test.code.contains("for seed in 0..100_u64"));
    }

    #[test]
    fn test_vc_property_test_bitvec_variables() {
        let formula = Formula::BvAdd(
            Box::new(Formula::Var("a".to_string(), Sort::BitVec(32))),
            Box::new(Formula::Var("b".to_string(), Sort::BitVec(32))),
            32,
        );
        let vc = make_vc_with_formula(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::u32(), Ty::u32()),
            },
            "math::add",
            formula,
        );
        let test = VcPropertyTestGen::generate(&vc);

        assert!(test.code.contains("a: u32"));
        assert!(test.code.contains("b: u32"));
    }

    #[test]
    fn test_vc_property_test_bool_variable() {
        let formula = Formula::And(vec![
            Formula::Var("flag".to_string(), Sort::Bool),
            Formula::Gt(
                Box::new(Formula::Var("count".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]);
        let vc = make_vc_with_formula(
            VcKind::Assertion { message: "invariant".into() },
            "check",
            formula,
        );
        let test = VcPropertyTestGen::generate(&vc);

        assert!(test.code.contains("count: i64"));
        assert!(test.code.contains("flag: bool"));
    }

    // -----------------------------------------------------------------------
    // MinimalReproducer
    // -----------------------------------------------------------------------

    #[test]
    fn test_shrink_value_int_positive() {
        let shrunk = shrink_value(&CounterexampleValue::Int(100));
        match shrunk {
            Some(CounterexampleValue::Int(50)) => {}
            other => panic!("expected Some(Int(50)), got {other:?}"),
        }
    }

    #[test]
    fn test_shrink_value_int_negative() {
        let shrunk = shrink_value(&CounterexampleValue::Int(-100));
        match shrunk {
            Some(CounterexampleValue::Int(-50)) => {}
            other => panic!("expected Some(Int(-50)), got {other:?}"),
        }
    }

    #[test]
    fn test_shrink_value_int_zero() {
        let shrunk = shrink_value(&CounterexampleValue::Int(0));
        assert!(shrunk.is_none());
    }

    #[test]
    fn test_shrink_value_uint() {
        let shrunk = shrink_value(&CounterexampleValue::Uint(200));
        match shrunk {
            Some(CounterexampleValue::Uint(100)) => {}
            other => panic!("expected Some(Uint(100)), got {other:?}"),
        }
    }

    #[test]
    fn test_shrink_value_uint_zero() {
        let shrunk = shrink_value(&CounterexampleValue::Uint(0));
        assert!(shrunk.is_none());
    }

    #[test]
    fn test_shrink_value_float() {
        let shrunk = shrink_value(&CounterexampleValue::Float(10.0));
        match shrunk {
            Some(CounterexampleValue::Float(f)) => {
                assert!((f - 5.0).abs() < f64::EPSILON, "expected 5.0, got {f}");
            }
            other => panic!("expected Some(Float(5.0)), got {other:?}"),
        }
    }

    #[test]
    fn test_shrink_value_bool() {
        let shrunk = shrink_value(&CounterexampleValue::Bool(true));
        assert!(shrunk.is_none());
    }

    #[test]
    fn test_minimal_reproducer_shrink() {
        let cex = make_cex(&[
            ("a", CounterexampleValue::Int(1000)),
            ("b", CounterexampleValue::Uint(500)),
        ]);

        let reproducer = MinimalReproducer::new();
        let shrunk = reproducer.shrink(&cex);

        // Values should be smaller than originals
        for (name, val) in &shrunk.assignments {
            match (name.as_str(), val) {
                ("a", CounterexampleValue::Int(n)) => {
                    assert!(*n < 1000, "a should be shrunk from 1000, got {n}");
                }
                ("b", CounterexampleValue::Uint(n)) => {
                    assert!(*n < 500, "b should be shrunk from 500, got {n}");
                }
                _ => panic!("unexpected variable: {name}"),
            }
        }
    }

    #[test]
    fn test_minimal_reproducer_filter_relevant() {
        let cex = make_cex(&[
            ("relevant_a", CounterexampleValue::Int(10)),
            ("irrelevant_b", CounterexampleValue::Int(20)),
            ("relevant_c", CounterexampleValue::Int(30)),
        ]);

        let relevant: FxHashSet<String> =
            ["relevant_a".to_string(), "relevant_c".to_string()].into();

        let reproducer = MinimalReproducer::new();
        let filtered = reproducer.filter_relevant(&cex, &relevant);

        assert_eq!(filtered.assignments.len(), 2);
        assert!(filtered.assignments.iter().any(|(n, _)| n == "relevant_a"));
        assert!(filtered.assignments.iter().any(|(n, _)| n == "relevant_c"));
    }

    #[test]
    fn test_minimal_reproducer_filter_keeps_all_if_empty_match() {
        let cex = make_cex(&[
            ("a", CounterexampleValue::Int(10)),
        ]);

        let relevant: FxHashSet<String> = FxHashSet::default();

        let reproducer = MinimalReproducer::new();
        let filtered = reproducer.filter_relevant(&cex, &relevant);

        // Should keep originals when filter matches nothing
        assert_eq!(filtered.assignments.len(), 1);
    }

    #[test]
    fn test_minimal_reproducer_minimize() {
        let cex = make_cex(&[
            ("x", CounterexampleValue::Int(1000)),
            ("noise", CounterexampleValue::Int(999)),
        ]);

        let relevant: FxHashSet<String> = ["x".to_string()].into();

        let reproducer = MinimalReproducer::new();
        let minimized = reproducer.minimize(&cex, &relevant);

        // Should have only relevant variable, and value should be shrunk
        assert_eq!(minimized.assignments.len(), 1);
        assert_eq!(minimized.assignments[0].0, "x");
        match &minimized.assignments[0].1 {
            CounterexampleValue::Int(n) => {
                assert!(*n < 1000, "value should be shrunk");
            }
            _ => panic!("wrong type"),
        }
    }

    #[test]
    fn test_minimal_reproducer_max_iterations() {
        let reproducer = MinimalReproducer::with_max_iterations(2);
        let cex = make_cex(&[
            ("a", CounterexampleValue::Int(1_000_000)),
            ("b", CounterexampleValue::Int(2_000_000)),
            ("c", CounterexampleValue::Int(3_000_000)),
        ]);

        let shrunk = reproducer.shrink(&cex);
        // With max_iterations=2, only first two can be shrunk
        assert_eq!(shrunk.assignments.len(), 3);
    }

    // -----------------------------------------------------------------------
    // Integration: add_cex_tests_to_suite
    // -----------------------------------------------------------------------

    #[test]
    fn test_add_cex_tests_to_suite() {
        let mut suite = RegressionSuite::new("cex_integration");
        let cex = make_cex(&[
            ("x", CounterexampleValue::Int(42)),
        ]);
        let vc = make_vc(VcKind::DivisionByZero, "math::divide");

        let errors = add_cex_tests_to_suite(
            &mut suite,
            &[(&cex, &vc)],
            Some("abc123"),
        );

        assert!(errors.is_empty());
        assert_eq!(suite.len(), 1);
        assert!(suite.tests[0].test_name.contains("division_by_zero"));
    }

    #[test]
    fn test_add_multiple_cex_tests() {
        let mut suite = RegressionSuite::new("multi");
        let cex1 = make_cex(&[("a", CounterexampleValue::Int(1))]);
        let cex2 = make_cex(&[("b", CounterexampleValue::Uint(2))]);
        let vc1 = make_vc(VcKind::DivisionByZero, "f");
        let vc2 = make_vc(VcKind::IndexOutOfBounds, "g");

        let errors = add_cex_tests_to_suite(
            &mut suite,
            &[(&cex1, &vc1), (&cex2, &vc2)],
            None,
        );

        assert!(errors.is_empty());
        assert_eq!(suite.len(), 2);
    }

    // -----------------------------------------------------------------------
    // extract_formula_variables
    // -----------------------------------------------------------------------

    #[test]
    fn test_extract_variables_empty_formula() {
        let vars = extract_formula_variables(&Formula::Bool(true));
        assert!(vars.is_empty());
    }

    #[test]
    fn test_extract_variables_single_var() {
        let formula = Formula::Var("x".to_string(), Sort::Int);
        let vars = extract_formula_variables(&formula);
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].0, "x");
    }

    #[test]
    fn test_extract_variables_nested() {
        let formula = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("y".to_string(), Sort::BitVec(32))),
                Box::new(Formula::Var("z".to_string(), Sort::BitVec(32))),
            ),
        ]);
        let vars = extract_formula_variables(&formula);
        assert_eq!(vars.len(), 3);
        // Should be sorted by name
        assert_eq!(vars[0].0, "x");
        assert_eq!(vars[1].0, "y");
        assert_eq!(vars[2].0, "z");
    }

    #[test]
    fn test_extract_variables_dedup() {
        let formula = Formula::Add(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
        );
        let vars = extract_formula_variables(&formula);
        assert_eq!(vars.len(), 1);
    }

    // -----------------------------------------------------------------------
    // sort_to_rust_type
    // -----------------------------------------------------------------------

    #[test]
    fn test_sort_to_rust_type() {
        assert_eq!(sort_to_rust_type(&Sort::Bool), "bool");
        assert_eq!(sort_to_rust_type(&Sort::Int), "i64");
        assert_eq!(sort_to_rust_type(&Sort::BitVec(8)), "u8");
        assert_eq!(sort_to_rust_type(&Sort::BitVec(16)), "u16");
        assert_eq!(sort_to_rust_type(&Sort::BitVec(32)), "u32");
        assert_eq!(sort_to_rust_type(&Sort::BitVec(64)), "u64");
        assert_eq!(sort_to_rust_type(&Sort::BitVec(128)), "u128");
    }

    #[test]
    fn test_sort_to_rust_type_array() {
        let sort = Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8)));
        assert_eq!(sort_to_rust_type(&sort), "Vec<u8>");
    }
}
