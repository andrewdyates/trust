// trust-testgen: Property-based test generation from specification attributes
//
// Generates proptest-style property tests from #[requires] and #[ensures]
// annotations. Given a FunctionSpec, produces Rust test code that:
//   - Generates random inputs satisfying preconditions
//   - Asserts postconditions on the result
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::FunctionSpec;
use std::fmt::Write;

use crate::{sanitize_ident, GeneratedTest};

/// Strategy for generating test inputs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum InputStrategy {
    /// Uniformly random values within type bounds.
    Random,
    /// Boundary values (MIN, MAX, 0, 1, -1, etc.).
    Boundary,
    /// Small-scope hypothesis: enumerate small values exhaustively.
    SmallScope,
}

impl InputStrategy {
    /// Returns the iteration count for this strategy.
    #[must_use]
    pub fn iteration_count(&self) -> usize {
        match self {
            InputStrategy::Random => 100,
            InputStrategy::Boundary => 1,
            InputStrategy::SmallScope => 1,
        }
    }
}

/// Generator for property-based tests from function specifications.
pub struct PropertyTestGenerator {
    strategy: InputStrategy,
}

impl PropertyTestGenerator {
    /// Create a new generator with the given input strategy.
    #[must_use]
    pub fn new(strategy: InputStrategy) -> Self {
        Self { strategy }
    }

    /// Generate a property test from a function specification.
    ///
    /// Returns `None` if the spec has no requires or ensures clauses.
    #[must_use]
    pub fn generate(&self, func_name: &str, spec: &FunctionSpec) -> Option<GeneratedTest> {
        if spec.is_empty() {
            return None;
        }
        Some(generate_property_test(func_name, spec, self.strategy))
    }
}

impl Default for PropertyTestGenerator {
    fn default() -> Self {
        Self::new(InputStrategy::Boundary)
    }
}

/// Generate a property test from a `FunctionSpec`.
///
/// Produces a Rust `#[test]` function that:
/// - For each `#[requires(expr)]`: filters inputs satisfying the precondition
/// - For each `#[ensures(expr)]`: asserts the postcondition on the result
///
/// The generated test uses boundary values by default. Pass a different
/// `InputStrategy` for alternative input generation.
#[must_use]
pub fn generate_property_test(
    func_name: &str,
    spec: &FunctionSpec,
    strategy: InputStrategy,
) -> GeneratedTest {
    let sanitized = sanitize_ident(func_name);
    let strategy_suffix = match strategy {
        InputStrategy::Random => "random",
        InputStrategy::Boundary => "boundary",
        InputStrategy::SmallScope => "small_scope",
    };
    let name = format!("test_property_{sanitized}_{strategy_suffix}");

    let mut body = String::new();
    let mut boundary_values = Vec::new();

    // Comment header
    let _ = writeln!(body, 
        "    // Property test for `{func_name}` (strategy: {strategy_suffix})"
    );

    // Precondition guards
    if !spec.requires.is_empty() {
        body.push_str("    // Preconditions:\n");
        for req in &spec.requires {
            let _ = writeln!(body, "    //   requires: {req}");
        }
    }

    // Postcondition assertions
    if !spec.ensures.is_empty() {
        body.push_str("    // Postconditions:\n");
        for ens in &spec.ensures {
            let _ = writeln!(body, "    //   ensures: {ens}");
        }
    }

    // Invariants
    if !spec.invariants.is_empty() {
        body.push_str("    // Invariants:\n");
        for inv in &spec.invariants {
            let _ = writeln!(body, "    //   invariant: {inv}");
        }
    }

    body.push('\n');

    // Generate input values based on strategy
    match strategy {
        InputStrategy::Random => {
            body.push_str(
                "    // Random input generation (100 iterations)\n\
                 \x20   use std::collections::hash_map::DefaultHasher;\n\
                 \x20   use std::hash::{Hash, Hasher};\n\
                 \x20   let mut hasher = DefaultHasher::new();\n\
                 \x20   for seed in 0..100u64 {\n\
                 \x20       seed.hash(&mut hasher);\n\
                 \x20       let val = hasher.finish() as i64;\n",
            );
            boundary_values.push("random(0..100)".into());
            append_precondition_filter(&mut body, spec, "        ");
            append_postcondition_check(&mut body, spec, func_name, "        ");
            body.push_str("    }\n");
        }
        InputStrategy::Boundary => {
            let values = extract_boundary_values_from_spec(spec);
            boundary_values.clone_from(&values);
            let values_str = if values.is_empty() {
                "i64::MIN, -1, 0, 1, i64::MAX".to_string()
            } else {
                values.join(", ")
            };
            let _ = write!(body, 
                "    let boundary_values: &[i64] = &[{values_str}];\n\
                 \x20   for &val in boundary_values {{\n"
            );
            append_precondition_filter(&mut body, spec, "        ");
            append_postcondition_check(&mut body, spec, func_name, "        ");
            body.push_str("    }\n");
        }
        InputStrategy::SmallScope => {
            body.push_str(
                "    // Small-scope: enumerate small values exhaustively\n\
                 \x20   for val in -10i64..=10 {\n",
            );
            boundary_values.push("-10..=10".into());
            append_precondition_filter(&mut body, spec, "        ");
            append_postcondition_check(&mut body, spec, func_name, "        ");
            body.push_str("    }\n");
        }
    }

    let code = format!("#[test]\nfn {name}() {{\n{body}}}");

    GeneratedTest { name, code, boundary_values }
}

/// Append precondition filter lines to the body.
fn append_precondition_filter(body: &mut String, spec: &FunctionSpec, indent: &str) {
    for req in &spec.requires {
        let constraint = spec_expr_to_rust_constraint(req, "val");
        let _ = write!(body, 
            "{indent}// Guard: requires {req}\n\
             {indent}if !({constraint}) {{ continue; }}\n"
        );
    }
}

/// Append postcondition assertion lines to the body.
fn append_postcondition_check(
    body: &mut String,
    spec: &FunctionSpec,
    func_name: &str,
    indent: &str,
) {
    if spec.ensures.is_empty() {
        let _ = write!(body, 
            "{indent}// No postcondition — just verify the function accepts this input.\n\
             {indent}// PLACEHOLDER: wire up call to `{func_name}(val)`\n\
             {indent}let _ = val;\n"
        );
    } else {
        let _ = write!(body, 
            "{indent}// PLACEHOLDER: call `{func_name}(val)` and bind result\n\
             {indent}let result = val; // placeholder\n"
        );
        for ens in &spec.ensures {
            let assertion = spec_expr_to_rust_constraint(ens, "result");
            let _ = write!(body, 
                "{indent}// Assert: ensures {ens}\n\
                 {indent}assert!({assertion}, \"postcondition violated: {ens}\");\n"
            );
        }
    }
}

/// Heuristically convert a spec expression to a Rust boolean expression.
///
/// Handles simple patterns like `x > 0`, `result >= a + b`, etc.
/// For expressions it cannot parse, returns a `true` placeholder with a comment.
pub fn spec_expr_to_rust_constraint(expr: &str, binding: &str) -> String {
    let expr = expr.trim();

    // Replace `result` with the binding name
    let expr = expr.replace("result", binding);

    // Check if it looks like a simple comparison
    if expr.contains(">=")
        || expr.contains("<=")
        || expr.contains(">")
        || expr.contains("<")
        || expr.contains("==")
        || expr.contains("!=")
        || expr.contains("&&")
        || expr.contains("||")
    {
        return expr;
    }

    // Fallback: wrap as-is, assuming it is a boolean expression
    if expr.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == ' ') {
        return expr;
    }

    // Cannot translate — return a true placeholder
    format!("true /* PLACEHOLDER: translate spec: {expr} */")
}

/// Extract boundary values from spec requires clauses.
///
/// Looks for patterns like `x > 0` and generates boundary values around
/// the constants found in the expressions.
#[must_use]
pub fn extract_boundary_values_from_spec(spec: &FunctionSpec) -> Vec<String> {
    let mut values = vec![
        "i64::MIN".to_string(),
        "-1".to_string(),
        "0".to_string(),
        "1".to_string(),
        "i64::MAX".to_string(),
    ];

    for req in &spec.requires {
        // Extract integer literals from the expression
        for token in req.split(|c: char| !c.is_ascii_digit() && c != '-') {
            if let Ok(n) = token.parse::<i64>() {
                // Add the constant and its neighbors
                if n != 0 && n != 1 && n != -1 {
                    values.push(format!("{n}"));
                    if n > i64::MIN {
                        values.push(format!("{}", n - 1));
                    }
                    if n < i64::MAX {
                        values.push(format!("{}", n + 1));
                    }
                }
            }
        }
    }

    values.sort();
    values.dedup();
    values
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_spec(requires: &[&str], ensures: &[&str]) -> FunctionSpec {
        FunctionSpec {
            requires: requires.iter().map(|s| s.to_string()).collect(),
            ensures: ensures.iter().map(|s| s.to_string()).collect(),
            invariants: vec![],
        }
    }

    #[test]
    fn test_generate_property_test_basic() {
        let spec = make_spec(&["x > 0"], &["result > 0"]);
        let test = generate_property_test("compute", &spec, InputStrategy::Boundary);
        assert_eq!(test.name, "test_property_compute_boundary");
        assert!(test.code.contains("#[test]"));
        assert!(test.code.contains("requires: x > 0"));
        assert!(test.code.contains("ensures: result > 0"));
        assert!(test.code.contains("boundary_values"));
    }

    #[test]
    fn test_generate_property_test_random_strategy() {
        let spec = make_spec(&["x > 0"], &["result >= 0"]);
        let test = generate_property_test("process", &spec, InputStrategy::Random);
        assert_eq!(test.name, "test_property_process_random");
        assert!(test.code.contains("100"));
        assert!(test.code.contains("seed"));
    }

    #[test]
    fn test_generate_property_test_small_scope() {
        let spec = make_spec(&[], &["result >= 0"]);
        let test = generate_property_test("f", &spec, InputStrategy::SmallScope);
        assert_eq!(test.name, "test_property_f_small_scope");
        assert!(test.code.contains("-10i64..=10"));
    }

    #[test]
    fn test_generator_returns_none_for_empty_spec() {
        let generator = PropertyTestGenerator::default();
        let spec = FunctionSpec::default();
        assert!(generator.generate("f", &spec).is_none());
    }

    #[test]
    fn test_generator_returns_some_for_nonempty_spec() {
        let generator = PropertyTestGenerator::new(InputStrategy::Boundary);
        let spec = make_spec(&["x > 0"], &[]);
        let result = generator.generate("f", &spec);
        assert!(result.is_some());
        assert!(result.unwrap().code.contains("x > 0"));
    }

    #[test]
    fn test_spec_expr_to_rust_constraint_simple_comparison() {
        assert_eq!(
            spec_expr_to_rust_constraint("x > 0", "val"),
            "x > 0"
        );
        assert_eq!(
            spec_expr_to_rust_constraint("result >= 0", "val"),
            "val >= 0"
        );
        assert_eq!(
            spec_expr_to_rust_constraint("result == x + 1", "out"),
            "out == x + 1"
        );
    }

    #[test]
    fn test_spec_expr_to_rust_constraint_boolean_ops() {
        assert_eq!(
            spec_expr_to_rust_constraint("x > 0 && y > 0", "val"),
            "x > 0 && y > 0"
        );
    }

    #[test]
    fn test_spec_expr_to_rust_constraint_fallback() {
        let result = spec_expr_to_rust_constraint("forall(x: ???)", "val");
        assert!(result.contains("PLACEHOLDER"));
    }

    #[test]
    fn test_extract_boundary_values_includes_constants() {
        let spec = make_spec(&["x > 10"], &[]);
        let values = extract_boundary_values_from_spec(&spec);
        assert!(values.contains(&"10".to_string()));
        assert!(values.contains(&"9".to_string()));
        assert!(values.contains(&"11".to_string()));
        assert!(values.contains(&"0".to_string()));
    }

    #[test]
    fn test_extract_boundary_values_empty_spec() {
        let spec = FunctionSpec::default();
        let values = extract_boundary_values_from_spec(&spec);
        // Should still contain the baseline boundary values
        assert!(values.contains(&"0".to_string()));
        assert!(values.contains(&"i64::MIN".to_string()));
        assert!(values.contains(&"i64::MAX".to_string()));
    }

    #[test]
    fn test_input_strategy_iteration_count() {
        assert_eq!(InputStrategy::Random.iteration_count(), 100);
        assert_eq!(InputStrategy::Boundary.iteration_count(), 1);
        assert_eq!(InputStrategy::SmallScope.iteration_count(), 1);
    }

    #[test]
    fn test_property_test_with_invariant() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec![],
            invariants: vec!["n >= 0".to_string()],
        };
        let test = generate_property_test("loop_fn", &spec, InputStrategy::Boundary);
        assert!(test.code.contains("invariant: n >= 0"));
    }

    #[test]
    fn test_property_test_multiple_requires_ensures() {
        let spec = make_spec(
            &["x > 0", "y > 0"],
            &["result > x", "result > y"],
        );
        let test = generate_property_test("multi", &spec, InputStrategy::Boundary);
        // Both requires should appear as guards
        assert!(test.code.contains("requires: x > 0"));
        assert!(test.code.contains("requires: y > 0"));
        // Both ensures should appear as assertions
        assert!(test.code.contains("ensures: result > x"));
        assert!(test.code.contains("ensures: result > y"));
    }

    #[test]
    fn test_default_generator_uses_boundary() {
        let generator = PropertyTestGenerator::default();
        let spec = make_spec(&["x > 0"], &["result > 0"]);
        let test = generator.generate("f", &spec).unwrap();
        assert!(test.name.contains("boundary"));
    }
}
