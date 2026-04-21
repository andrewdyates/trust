// trust-testgen: Fuzz target generation from verification failures
//
// When verification fails, generate cargo-fuzz compatible fuzz harnesses
// that exercise the failing code path with coverage-guided fuzzing.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;
use std::time::Duration;
use std::fmt::Write;

use trust_types::{Counterexample, CounterexampleValue, Formula, Ty, VerifiableFunction};

use crate::{sanitize_ident, boundary_values_for_ty, ty_to_rust_name, GeneratedTest};

/// Configuration for fuzz target generation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuzzConfig {
    /// Directory for the fuzzing corpus.
    pub(crate) corpus_dir: PathBuf,
    /// Maximum number of fuzzing iterations (0 = unlimited).
    pub(crate) max_iterations: u64,
    /// Timeout per fuzzing run.
    pub(crate) timeout: Duration,
    /// Whether to generate cargo-fuzz compatible targets.
    pub(crate) cargo_fuzz_compatible: bool,
}

impl Default for FuzzConfig {
    fn default() -> Self {
        Self {
            corpus_dir: PathBuf::from("fuzz/corpus"),
            max_iterations: 0,
            timeout: Duration::from_secs(60),
            cargo_fuzz_compatible: true,
        }
    }
}

/// A generated fuzz target for a specific function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuzzTarget {
    /// Name of the fuzz target (used as filename).
    pub(crate) name: String,
    /// Complete Rust source code for the fuzz harness.
    pub(crate) code: String,
    /// Constraints that the fuzzer should try to satisfy.
    pub(crate) constraints: Vec<String>,
    /// Configuration used to generate this target.
    pub(crate) config: FuzzConfig,
}

impl FuzzTarget {
    /// Convert this fuzz target to a `GeneratedTest` for inclusion in test suites.
    #[must_use]
    pub fn to_generated_test(&self) -> GeneratedTest {
        GeneratedTest {
            name: format!("fuzz_{}", self.name),
            code: self.code.clone(),
            boundary_values: self.constraints.clone(),
        }
    }
}

/// A seed corpus entry for a fuzz target.
#[derive(Debug, Clone, PartialEq)]
pub struct SeedEntry {
    /// Human-readable description of the seed's origin.
    pub(crate) origin: String,
    /// Raw bytes for this seed (serialized input values).
    pub(crate) data: Vec<u8>,
    /// Priority score: higher = more interesting to the fuzzer.
    /// Boundary values and counterexamples get higher scores.
    pub(crate) priority: u32,
}

/// A seed corpus collection for initializing a fuzzer.
#[derive(Debug, Clone)]
pub struct SeedCorpus {
    /// Name of the function this corpus is for.
    pub(crate) function_name: String,
    /// Seed entries, ordered by priority (highest first).
    pub(crate) seeds: Vec<SeedEntry>,
}

impl SeedCorpus {
    /// Create an empty seed corpus for the given function.
    #[must_use]
    pub fn new(function_name: &str) -> Self {
        Self {
            function_name: function_name.to_string(),
            seeds: Vec::new(),
        }
    }

    /// Add a seed entry and maintain priority ordering.
    pub fn add(&mut self, entry: SeedEntry) {
        self.seeds.push(entry);
        self.seeds.sort_by(|a, b| b.priority.cmp(&a.priority));
    }

    /// Number of seeds in the corpus.
    #[must_use]
    pub fn len(&self) -> usize {
        self.seeds.len()
    }

    /// Whether the corpus is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.seeds.is_empty()
    }

    /// Get the top-N highest-priority seeds.
    #[must_use]
    pub fn top_seeds(&self, n: usize) -> &[SeedEntry] {
        let end = n.min(self.seeds.len());
        &self.seeds[..end]
    }
}

/// Generate a seed corpus from counterexamples for a function.
///
/// Each counterexample variable assignment is serialized to bytes and added
/// as a high-priority seed. Boundary values for the function's parameter
/// types are added as medium-priority seeds.
#[must_use]
pub fn generate_seed_corpus(
    func: &VerifiableFunction,
    counterexamples: &[Counterexample],
) -> SeedCorpus {
    let mut corpus = SeedCorpus::new(&func.name);

    // Add counterexample seeds (highest priority)
    for (i, cex) in counterexamples.iter().enumerate() {
        let data = serialize_counterexample(cex);
        corpus.add(SeedEntry {
            origin: format!("counterexample[{i}]"),
            data,
            priority: 100,
        });
    }

    // Add boundary value seeds (medium priority)
    let args: Vec<_> = func.body.locals.iter().skip(1).take(func.body.arg_count).collect();
    for local in &args {
        let (_, values) = boundary_values_for_ty(&local.ty);
        for (j, val) in values.iter().enumerate() {
            let data = serialize_boundary_value(val, &local.ty);
            let name = local.name.as_deref().unwrap_or("arg");
            corpus.add(SeedEntry {
                origin: format!("boundary[{name}={val}]"),
                data,
                priority: 50 + (j as u32 % 10),
            });
        }
    }

    // Add zero/unit seeds (lowest priority)
    let zero_data = vec![0u8; 8];
    corpus.add(SeedEntry {
        origin: "zero".into(),
        data: zero_data,
        priority: 10,
    });

    corpus
}

/// Generate a fuzz target from a `VerifiableFunction` with typed parameters.
///
/// Produces a cargo-fuzz compatible harness that reads structured bytes
/// and deserializes them into the function's parameter types.
#[must_use]
pub fn generate_typed_fuzz_target(
    func: &VerifiableFunction,
    constraints: &[Formula],
    config: &FuzzConfig,
) -> FuzzTarget {
    let sanitized = sanitize_ident(&func.name);
    let args: Vec<_> = func.body.locals.iter().skip(1).take(func.body.arg_count).collect();

    let mut code = String::new();
    code.push_str("#![no_main]\nuse libfuzzer_sys::fuzz_target;\n\n");
    let _ = writeln!(code, "// Typed fuzz target for `{}`", func.name);
    let _ = writeln!(code, "// Parameters: {}", args.len());

    // Calculate minimum data size
    let min_bytes: usize = args.iter().map(|a| byte_size_for_ty(&a.ty)).sum();
    let _ = writeln!(code, "// Minimum input bytes: {min_bytes}");

    if !constraints.is_empty() {
        code.push_str(&format_constraint_comments(constraints));
    }

    code.push_str("\nfuzz_target!(|data: &[u8]| {\n");
    let _ = writeln!(code, "    if data.len() < {min_bytes} {{ return; }}");

    // Deserialize typed parameters from byte slices
    let mut offset = 0;
    for local in &args {
        let name = local.name.as_deref().unwrap_or("arg");
        let ty_name = ty_to_rust_name(&local.ty);
        let byte_size = byte_size_for_ty(&local.ty);
        let _ = writeln!(code, 
            "    let {name}: {ty_name} = {};",
            deserialize_expr(&ty_name, offset, byte_size),
        );
        offset += byte_size;
    }

    // Apply constraint guards
    if !constraints.is_empty() {
        code.push('\n');
        code.push_str(&format_constraint_guards(constraints));
    }

    let _ = write!(code, 
        "\n    // PLACEHOLDER: wire up call to `{}`\n",
        func.name,
    );

    // Black-box each parameter to prevent optimization
    for local in &args {
        let name = local.name.as_deref().unwrap_or("arg");
        let _ = writeln!(code, "    let _ = std::hint::black_box({name});");
    }

    code.push_str("});\n");

    let constraint_strs: Vec<String> = constraints.iter().map(|c| format!("{c:?}")).collect();

    FuzzTarget {
        name: sanitized,
        code,
        constraints: constraint_strs,
        config: config.clone(),
    }
}

/// Byte size for deserializing a Ty from fuzz input.
fn byte_size_for_ty(ty: &Ty) -> usize {
    match ty {
        Ty::Bool => 1,
        Ty::Int { width, .. } => (*width as usize) / 8,
        Ty::Float { width: 32 } => 4,
        Ty::Float { width: 64 } => 8,
        Ty::Unit => 0,
        _ => 8, // default fallback
    }
}

/// Generate a deserialization expression for a type from byte slice.
fn deserialize_expr(ty_name: &str, offset: usize, byte_size: usize) -> String {
    if byte_size == 0 {
        return "()".into();
    }
    match ty_name {
        "bool" => format!("data[{offset}] != 0"),
        "f32" => format!(
            "f32::from_le_bytes(data[{offset}..{}].try_into().unwrap())",
            offset + byte_size,
        ),
        "f64" => format!(
            "f64::from_le_bytes(data[{offset}..{}].try_into().unwrap())",
            offset + byte_size,
        ),
        _ => format!(
            "{ty_name}::from_le_bytes(data[{offset}..{}].try_into().unwrap())",
            offset + byte_size,
        ),
    }
}

/// Serialize a counterexample's assignments to bytes.
fn serialize_counterexample(cex: &Counterexample) -> Vec<u8> {
    let mut data = Vec::new();
    for (_, val) in &cex.assignments {
        match val {
            CounterexampleValue::Bool(b) => data.push(u8::from(*b)),
            CounterexampleValue::Int(n) => data.extend_from_slice(&(*n as i64).to_le_bytes()),
            CounterexampleValue::Uint(n) => data.extend_from_slice(&(*n as u64).to_le_bytes()),
            CounterexampleValue::Float(f) => data.extend_from_slice(&f.to_le_bytes()),
            _ => {},
        }
    }
    data
}

/// Serialize a boundary value string to bytes for a given type.
fn serialize_boundary_value(val_str: &str, ty: &Ty) -> Vec<u8> {
    // For complex expressions like "i32::MAX", use a sentinel value
    match ty {
        Ty::Bool => {
            if val_str.contains("true") {
                vec![1]
            } else {
                vec![0]
            }
        }
        Ty::Int { width: 32, signed: true } => {
            let n: i32 = match val_str {
                "i32::MIN" => i32::MIN,
                "i32::MAX" => i32::MAX,
                _ => val_str.parse().unwrap_or(0),
            };
            n.to_le_bytes().to_vec()
        }
        Ty::Int { width: 64, signed: true } => {
            let n: i64 = match val_str {
                "i64::MIN" => i64::MIN,
                "i64::MAX" => i64::MAX,
                _ => val_str.parse().unwrap_or(0),
            };
            n.to_le_bytes().to_vec()
        }
        _ => {
            // Default: try to parse as i64 and serialize
            let n: i64 = val_str.parse().unwrap_or(0);
            n.to_le_bytes().to_vec()
        }
    }
}

// ---------------------------------------------------------------------------
// Original API (Formula-based)
// ---------------------------------------------------------------------------

/// Generate a cargo-fuzz compatible fuzz harness from a function and its constraints.
///
/// The generated harness reads arbitrary bytes from the fuzzer, converts them to
/// typed inputs, and exercises the target function under the given constraints.
#[must_use]
pub fn generate_fuzz_harness(func: &str, constraints: &[Formula]) -> String {
    let sanitized = sanitize_ident(func);
    let constraint_comments = format_constraint_comments(constraints);

    if constraints.is_empty() {
        return format!(
            "#![no_main]\n\
             use libfuzzer_sys::fuzz_target;\n\
             \n\
             // Fuzz target for `{func}`\n\
             // No specific constraints — exercising general input space.\n\
             \n\
             fuzz_target!(|data: &[u8]| {{\n\
             \x20   if data.len() < 8 {{ return; }}\n\
             \x20   let val = i64::from_le_bytes(data[..8].try_into().unwrap());\n\
             \x20   // PLACEHOLDER: wire up call to `{func}(val)`\n\
             \x20   let _ = std::hint::black_box(val);\n\
             }});\n"
        );
    }

    format!(
        "#![no_main]\n\
         use libfuzzer_sys::fuzz_target;\n\
         \n\
         // Fuzz target for `{func}`\n\
         {constraint_comments}\
         \n\
         fuzz_target!(|data: &[u8]| {{\n\
         \x20   if data.len() < 8 {{ return; }}\n\
         \x20   let val = i64::from_le_bytes(data[..8].try_into().unwrap());\n\
         \n\
         \x20   // Filter inputs to satisfy constraints\n\
         \x20   // (coverage-guided fuzzer will learn to produce valid inputs)\n\
         {guard_code}\
         \n\
         \x20   // PLACEHOLDER: wire up call to `{sanitized}(val)`\n\
         \x20   let _ = std::hint::black_box(val);\n\
         }});\n",
        guard_code = format_constraint_guards(constraints),
    )
}

/// Generate a fuzz target with full configuration.
#[must_use]
pub fn generate_fuzz_target(
    func: &str,
    constraints: &[Formula],
    config: &FuzzConfig,
) -> FuzzTarget {
    let sanitized = sanitize_ident(func);
    let code = generate_fuzz_harness(func, constraints);
    let constraint_strs: Vec<String> = constraints.iter().map(|c| format!("{c:?}")).collect();

    FuzzTarget {
        name: sanitized,
        code,
        constraints: constraint_strs,
        config: config.clone(),
    }
}

// ---------------------------------------------------------------------------
// Formula -> Rust helpers (pub(crate) for use by property_gen)
// ---------------------------------------------------------------------------

/// Format constraints as Rust comments for the harness header.
fn format_constraint_comments(constraints: &[Formula]) -> String {
    let mut out = String::new();
    out.push_str("// Constraints from verification failure:\n");
    for (i, c) in constraints.iter().enumerate() {
        let _ = writeln!(out, "//   [{i}]: {c:?}");
    }
    out
}

/// Format constraint formulas as Rust guard conditions.
fn format_constraint_guards(constraints: &[Formula]) -> String {
    let mut out = String::new();
    for (i, c) in constraints.iter().enumerate() {
        let guard = formula_to_rust_guard(c);
        let _ = write!(out, 
            "    // Constraint [{i}]: {c:?}\n\
             \x20   if !({guard}) {{ return; }}\n"
        );
    }
    out
}

/// Convert a `Formula` to a Rust boolean expression for use as a guard.
///
/// Handles simple formulas; complex ones get a `true` placeholder.
pub fn formula_to_rust_guard(formula: &Formula) -> String {
    match formula {
        Formula::Bool(b) => format!("{b}"),
        Formula::Gt(lhs, rhs) => {
            format!("{} > {}", formula_to_rust_expr(lhs), formula_to_rust_expr(rhs))
        }
        Formula::Ge(lhs, rhs) => {
            format!("{} >= {}", formula_to_rust_expr(lhs), formula_to_rust_expr(rhs))
        }
        Formula::Lt(lhs, rhs) => {
            format!("{} < {}", formula_to_rust_expr(lhs), formula_to_rust_expr(rhs))
        }
        Formula::Le(lhs, rhs) => {
            format!("{} <= {}", formula_to_rust_expr(lhs), formula_to_rust_expr(rhs))
        }
        Formula::Eq(lhs, rhs) => {
            format!("{} == {}", formula_to_rust_expr(lhs), formula_to_rust_expr(rhs))
        }
        Formula::Not(inner) => {
            format!("!({})", formula_to_rust_guard(inner))
        }
        Formula::And(conjuncts) => {
            let parts: Vec<_> = conjuncts.iter().map(formula_to_rust_guard).collect();
            if parts.is_empty() {
                "true".to_string()
            } else {
                parts.join(" && ")
            }
        }
        Formula::Or(disjuncts) => {
            let parts: Vec<_> = disjuncts.iter().map(formula_to_rust_guard).collect();
            if parts.is_empty() {
                "false".to_string()
            } else {
                format!("({})", parts.join(" || "))
            }
        }
        _ => format!("true /* complex: {formula:?} */"),
    }
}

/// Convert a `Formula` to a Rust value expression.
fn formula_to_rust_expr(formula: &Formula) -> String {
    match formula {
        Formula::Bool(b) => format!("{b}"),
        Formula::Int(n) => format!("{n}_i64"),
        Formula::Var(name, _) => name.clone(),
        Formula::Add(lhs, rhs) => {
            format!("({} + {})", formula_to_rust_expr(lhs), formula_to_rust_expr(rhs))
        }
        Formula::Sub(lhs, rhs) => {
            format!("({} - {})", formula_to_rust_expr(lhs), formula_to_rust_expr(rhs))
        }
        Formula::Mul(lhs, rhs) => {
            format!("({} * {})", formula_to_rust_expr(lhs), formula_to_rust_expr(rhs))
        }
        _ => format!("0 /* complex: {formula:?} */"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{BasicBlock, BlockId, LocalDecl, Sort, SourceSpan, Terminator, VerifiableBody};

    fn make_func(name: &str, args: &[(Ty, &str)]) -> VerifiableFunction {
        let mut locals = vec![LocalDecl {
            index: 0,
            ty: Ty::Unit,
            name: None,
        }];
        for (i, (ty, pname)) in args.iter().enumerate() {
            locals.push(LocalDecl {
                index: i + 1,
                ty: ty.clone(),
                name: Some(pname.to_string()),
            });
        }
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals,
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: args.len(),
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // --- Original API tests ---

    #[test]
    fn test_generate_fuzz_harness_no_constraints() {
        let harness = generate_fuzz_harness("my_crate::compute", &[]);
        assert!(harness.contains("#![no_main]"));
        assert!(harness.contains("fuzz_target!"));
        assert!(harness.contains("my_crate::compute"));
        assert!(harness.contains("black_box"));
    }

    #[test]
    fn test_generate_fuzz_harness_with_constraints() {
        let constraints = vec![Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )];
        let harness = generate_fuzz_harness("math::divide", &constraints);
        assert!(harness.contains("fuzz_target!"));
        assert!(harness.contains("Constraint [0]"));
        assert!(harness.contains("x > 0_i64"));
    }

    #[test]
    fn test_generate_fuzz_target_structure() {
        let config = FuzzConfig::default();
        let target = generate_fuzz_target("process", &[], &config);
        assert_eq!(target.name, "process");
        assert!(target.code.contains("fuzz_target!"));
        assert!(target.constraints.is_empty());
        assert_eq!(target.config, config);
    }

    #[test]
    fn test_fuzz_target_to_generated_test() {
        let config = FuzzConfig::default();
        let target = generate_fuzz_target("f", &[], &config);
        let test = target.to_generated_test();
        assert_eq!(test.name, "fuzz_f");
    }

    #[test]
    fn test_fuzz_config_default() {
        let config = FuzzConfig::default();
        assert_eq!(config.corpus_dir, PathBuf::from("fuzz/corpus"));
        assert_eq!(config.max_iterations, 0);
        assert_eq!(config.timeout, Duration::from_secs(60));
        assert!(config.cargo_fuzz_compatible);
    }

    #[test]
    fn test_formula_to_rust_guard_bool() {
        assert_eq!(formula_to_rust_guard(&Formula::Bool(true)), "true");
        assert_eq!(formula_to_rust_guard(&Formula::Bool(false)), "false");
    }

    #[test]
    fn test_formula_to_rust_guard_comparison() {
        let gt = Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(formula_to_rust_guard(&gt), "x > 0_i64");

        let ge = Formula::Ge(
            Box::new(Formula::Var("y".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        );
        assert_eq!(formula_to_rust_guard(&ge), "y >= 10_i64");
    }

    #[test]
    fn test_formula_to_rust_guard_not() {
        let not = Formula::Not(Box::new(Formula::Bool(false)));
        assert_eq!(formula_to_rust_guard(&not), "!(false)");
    }

    #[test]
    fn test_formula_to_rust_guard_and() {
        let and = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(100)),
            ),
        ]);
        assert_eq!(formula_to_rust_guard(&and), "x > 0_i64 && x < 100_i64");
    }

    #[test]
    fn test_formula_to_rust_guard_or() {
        let or = Formula::Or(vec![
            Formula::Bool(true),
            Formula::Bool(false),
        ]);
        assert_eq!(formula_to_rust_guard(&or), "(true || false)");
    }

    #[test]
    fn test_formula_to_rust_guard_empty_and() {
        assert_eq!(formula_to_rust_guard(&Formula::And(vec![])), "true");
    }

    #[test]
    fn test_formula_to_rust_guard_empty_or() {
        assert_eq!(formula_to_rust_guard(&Formula::Or(vec![])), "false");
    }

    #[test]
    fn test_formula_to_rust_guard_eq() {
        let eq = Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(42)),
        );
        assert_eq!(formula_to_rust_guard(&eq), "x == 42_i64");
    }

    #[test]
    fn test_formula_to_rust_expr_arithmetic() {
        let add = Formula::Add(
            Box::new(Formula::Var("a".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        );
        assert_eq!(formula_to_rust_expr(&add), "(a + 1_i64)");

        let sub = Formula::Sub(
            Box::new(Formula::Var("a".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        );
        assert_eq!(formula_to_rust_expr(&sub), "(a - 1_i64)");

        let mul = Formula::Mul(
            Box::new(Formula::Int(2)),
            Box::new(Formula::Var("n".into(), Sort::Int)),
        );
        assert_eq!(formula_to_rust_expr(&mul), "(2_i64 * n)");
    }

    #[test]
    fn test_formula_to_rust_guard_complex_fallback() {
        let complex = Formula::BitVec { value: 42, width: 32 };
        let guard = formula_to_rust_guard(&complex);
        assert!(guard.starts_with("true"));
        assert!(guard.contains("complex"));
    }

    #[test]
    fn test_generate_fuzz_harness_multiple_constraints() {
        let constraints = vec![
            Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(100)),
            ),
        ];
        let harness = generate_fuzz_harness("bounded_fn", &constraints);
        assert!(harness.contains("Constraint [0]"));
        assert!(harness.contains("Constraint [1]"));
        assert!(harness.contains("x > 0_i64"));
        assert!(harness.contains("x < 100_i64"));
    }

    // --- Seed corpus tests ---

    #[test]
    fn test_seed_corpus_new_empty() {
        let corpus = SeedCorpus::new("test_fn");
        assert_eq!(corpus.function_name, "test_fn");
        assert!(corpus.is_empty());
        assert_eq!(corpus.len(), 0);
    }

    #[test]
    fn test_seed_corpus_add_maintains_priority_order() {
        let mut corpus = SeedCorpus::new("f");
        corpus.add(SeedEntry {
            origin: "low".into(),
            data: vec![0],
            priority: 10,
        });
        corpus.add(SeedEntry {
            origin: "high".into(),
            data: vec![1],
            priority: 100,
        });
        corpus.add(SeedEntry {
            origin: "mid".into(),
            data: vec![2],
            priority: 50,
        });
        assert_eq!(corpus.len(), 3);
        assert_eq!(corpus.seeds[0].origin, "high");
        assert_eq!(corpus.seeds[1].origin, "mid");
        assert_eq!(corpus.seeds[2].origin, "low");
    }

    #[test]
    fn test_seed_corpus_top_seeds() {
        let mut corpus = SeedCorpus::new("f");
        for i in 0..5 {
            corpus.add(SeedEntry {
                origin: format!("seed_{i}"),
                data: vec![i as u8],
                priority: i * 10,
            });
        }
        let top = corpus.top_seeds(2);
        assert_eq!(top.len(), 2);
        assert_eq!(top[0].priority, 40);
        assert_eq!(top[1].priority, 30);
    }

    #[test]
    fn test_seed_corpus_top_seeds_exceeds_len() {
        let mut corpus = SeedCorpus::new("f");
        corpus.add(SeedEntry {
            origin: "only".into(),
            data: vec![1],
            priority: 10,
        });
        let top = corpus.top_seeds(100);
        assert_eq!(top.len(), 1);
    }

    #[test]
    fn test_generate_seed_corpus_from_counterexamples() {
        let func = make_func("divide", &[(Ty::i32(), "a"), (Ty::i32(), "b")]);
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Int(42)),
            ("b".into(), CounterexampleValue::Int(0)),
        ]);
        let corpus = generate_seed_corpus(&func, &[cex]);
        // Should have: 1 counterexample + boundary values for 2 params + 1 zero seed
        assert!(!corpus.is_empty());
        // Counterexample should be highest priority
        assert_eq!(corpus.seeds[0].priority, 100);
        assert_eq!(corpus.seeds[0].origin, "counterexample[0]");
    }

    #[test]
    fn test_generate_seed_corpus_no_counterexamples() {
        let func = make_func("f", &[(Ty::i32(), "x")]);
        let corpus = generate_seed_corpus(&func, &[]);
        // Should still have boundary value seeds + zero
        assert!(!corpus.is_empty());
        // No counterexample seed
        assert!(corpus.seeds.iter().all(|s| !s.origin.starts_with("counterexample")));
    }

    #[test]
    fn test_serialize_counterexample_int() {
        let cex = Counterexample::new(vec![
            ("x".into(), CounterexampleValue::Int(42)),
        ]);
        let data = serialize_counterexample(&cex);
        assert_eq!(data, 42i64.to_le_bytes().to_vec());
    }

    #[test]
    fn test_serialize_counterexample_bool() {
        let cex = Counterexample::new(vec![
            ("flag".into(), CounterexampleValue::Bool(true)),
        ]);
        let data = serialize_counterexample(&cex);
        assert_eq!(data, vec![1]);
    }

    #[test]
    fn test_serialize_counterexample_mixed() {
        let cex = Counterexample::new(vec![
            ("flag".into(), CounterexampleValue::Bool(false)),
            ("n".into(), CounterexampleValue::Int(7)),
        ]);
        let data = serialize_counterexample(&cex);
        assert_eq!(data[0], 0); // bool false
        assert_eq!(data.len(), 1 + 8); // 1 byte bool + 8 byte i64
    }

    // --- Typed fuzz target tests ---

    #[test]
    fn test_generate_typed_fuzz_target_single_param() {
        let func = make_func("process", &[(Ty::i32(), "x")]);
        let config = FuzzConfig::default();
        let target = generate_typed_fuzz_target(&func, &[], &config);
        assert_eq!(target.name, "process");
        assert!(target.code.contains("fuzz_target!"));
        assert!(target.code.contains("i32::from_le_bytes"));
        assert!(target.code.contains("data.len() < 4"));
        assert!(target.code.contains("black_box(x)"));
    }

    #[test]
    fn test_generate_typed_fuzz_target_multi_param() {
        let func = make_func("add", &[
            (Ty::i32(), "a"),
            (Ty::Int { width: 64, signed: false }, "b"),
        ]);
        let config = FuzzConfig::default();
        let target = generate_typed_fuzz_target(&func, &[], &config);
        assert!(target.code.contains("data.len() < 12")); // 4 + 8
        assert!(target.code.contains("i32::from_le_bytes"));
        assert!(target.code.contains("u64::from_le_bytes"));
    }

    #[test]
    fn test_generate_typed_fuzz_target_with_constraints() {
        let func = make_func("bounded", &[(Ty::i32(), "x")]);
        let constraints = vec![Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )];
        let config = FuzzConfig::default();
        let target = generate_typed_fuzz_target(&func, &constraints, &config);
        assert!(target.code.contains("Constraint [0]"));
        assert!(target.code.contains("x > 0_i64"));
    }

    #[test]
    fn test_generate_typed_fuzz_target_bool_param() {
        let func = make_func("toggle", &[(Ty::Bool, "flag")]);
        let config = FuzzConfig::default();
        let target = generate_typed_fuzz_target(&func, &[], &config);
        assert!(target.code.contains("data.len() < 1"));
        assert!(target.code.contains("data[0] != 0"));
    }

    #[test]
    fn test_byte_size_for_types() {
        assert_eq!(byte_size_for_ty(&Ty::Bool), 1);
        assert_eq!(byte_size_for_ty(&Ty::i32()), 4);
        assert_eq!(byte_size_for_ty(&Ty::Int { width: 64, signed: false }), 8);
        assert_eq!(byte_size_for_ty(&Ty::Float { width: 32 }), 4);
        assert_eq!(byte_size_for_ty(&Ty::Float { width: 64 }), 8);
        assert_eq!(byte_size_for_ty(&Ty::Unit), 0);
    }

    #[test]
    fn test_deserialize_expr_types() {
        assert_eq!(deserialize_expr("bool", 0, 1), "data[0] != 0");
        assert!(deserialize_expr("i32", 0, 4).contains("i32::from_le_bytes"));
        assert!(deserialize_expr("f64", 4, 8).contains("f64::from_le_bytes"));
        assert!(deserialize_expr("f64", 4, 8).contains("data[4..12]"));
    }

    #[test]
    fn test_serialize_boundary_value_i32() {
        let data = serialize_boundary_value("i32::MAX", &Ty::i32());
        assert_eq!(data, i32::MAX.to_le_bytes().to_vec());
    }

    #[test]
    fn test_serialize_boundary_value_i32_min() {
        let data = serialize_boundary_value("i32::MIN", &Ty::i32());
        assert_eq!(data, i32::MIN.to_le_bytes().to_vec());
    }

    #[test]
    fn test_serialize_boundary_value_literal() {
        let data = serialize_boundary_value("42", &Ty::i32());
        assert_eq!(data, 42i32.to_le_bytes().to_vec());
    }
}
