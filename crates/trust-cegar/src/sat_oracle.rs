// trust-cegar: SAT oracle trait for IC3/PDR model checking
//
// Abstracts the satisfiability checking backend so IC3 can use either:
// - StructuralSatOracle: fast boolean simplification (for tests, fallback)
// - SmtSatOracle: real z4 SMT queries (for production verification)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::io::Write as _;
use std::process::{Command, Stdio};
use std::fmt::Write;

use trust_types::{Formula, Sort};

use crate::error::CegarError;
use crate::ic3::{Cube, SatResult, structural_sat_check};
use crate::z4_bridge::formula_to_smtlib;

// ---------------------------------------------------------------------------
// SAT oracle trait
// ---------------------------------------------------------------------------

/// Oracle for satisfiability queries in IC3/PDR.
///
/// IC3 issues many SAT queries per iteration (init check, predecessor search,
/// inductiveness check, clause propagation). The oracle abstraction lets us
/// swap between a fast structural checker (for tests) and a real SMT solver
/// (for production).
pub trait SatOracle: Send + Sync {
    /// Check satisfiability of a formula.
    ///
    /// # Errors
    /// Returns `CegarError::SolverError` if the backend fails.
    fn check_sat(&self, formula: &Formula) -> Result<SatResult, CegarError>;

    /// Human-readable name of this oracle (for logging/debugging).
    fn name(&self) -> &str;
}

// ---------------------------------------------------------------------------
// Structural oracle (existing behavior)
// ---------------------------------------------------------------------------

/// SAT oracle using structural boolean simplification.
///
/// This is the original IC3 checker: fast but incomplete. Returns `Sat(None)`
/// for any formula it cannot decide, which is conservative (see ic3.rs docs).
/// Used as the default in tests and when z4 is unavailable.
pub(crate) struct StructuralSatOracle;

impl SatOracle for StructuralSatOracle {
    fn check_sat(&self, formula: &Formula) -> Result<SatResult, CegarError> {
        Ok(structural_sat_check(formula))
    }

    fn name(&self) -> &str {
        "structural"
    }
}

// ---------------------------------------------------------------------------
// SMT oracle (z4 subprocess)
// ---------------------------------------------------------------------------

/// SAT oracle using z4 SMT solver via subprocess.
///
/// Serializes the formula to SMT-LIB2, invokes z4, and parses the result.
/// This gives IC3 full SMT-level reasoning for all queries.
///
/// When z4 is unavailable or returns an error, falls back to the structural
/// oracle to maintain availability.
pub(crate) struct SmtSatOracle {
    /// Path to the z4 binary.
    solver_path: String,
    /// Arguments for z4 (default: ["-smt2", "-in"]).
    solver_args: Vec<String>,
    /// Timeout per query in milliseconds.
    timeout_ms: u64,
    /// Fallback oracle for when z4 is unavailable.
    fallback: StructuralSatOracle,
}

impl SmtSatOracle {
    /// Create a new SMT oracle with default z4 path.
    pub(crate) fn new() -> Self {
        Self {
            solver_path: "z4".to_string(),
            solver_args: vec!["-smt2".to_string(), "-in".to_string()],
            timeout_ms: 10_000, // 10s per IC3 query
            fallback: StructuralSatOracle,
        }
    }

    /// Create with a custom solver path.
    pub(crate) fn with_solver_path(path: impl Into<String>) -> Self {
        Self {
            solver_path: path.into(),
            ..Self::new()
        }
    }

    /// Set the per-query timeout in milliseconds.
    #[must_use]
    pub(crate) fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Generate an SMT-LIB2 script for a satisfiability check.
    ///
    /// The script declares variables, asserts the formula, and checks sat.
    /// If sat, requests a model for counterexample extraction.
    fn generate_script(&self, formula: &Formula) -> String {
        let mut script = String::new();

        // Use ALL logic to handle mixed int/bool/bv formulas.
        script.push_str("(set-logic ALL)\n");

        // Collect and declare variables.
        let mut vars = BTreeSet::new();
        collect_vars(formula, &mut vars);
        for (name, sort) in &vars {
            let _ = writeln!(script, 
                "(declare-const {} {})",
                name,
                sort.to_smtlib()
            );
        }

        // Assert the formula.
        let _ = writeln!(script, "(assert {})", formula_to_smtlib(formula));

        // Check sat and get model if sat.
        script.push_str("(check-sat)\n");
        script.push_str("(get-model)\n");
        script.push_str("(exit)\n");

        script
    }

    /// Run z4 on a script and return raw stdout.
    fn run_solver(&self, script: &str) -> Result<String, String> {
        let mut child = Command::new(&self.solver_path)
            .args(&self.solver_args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("failed to spawn {}: {e}", self.solver_path))?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin
                .write_all(script.as_bytes())
                .map_err(|e| format!("failed to write to solver stdin: {e}"))?;
        }

        let output = child
            .wait_with_output()
            .map_err(|e| format!("failed to read solver output: {e}"))?;

        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        if !stderr.is_empty() && !stdout.contains("sat") {
            return Err(format!("solver stderr: {stderr}"));
        }

        Ok(stdout)
    }

    /// Parse z4 output into a SatResult.
    ///
    /// - "unsat" -> Unsat
    /// - "sat" + model -> Sat(Some(cube)) with model extraction
    /// - "sat" without model -> Sat(None)
    /// - "unknown" or error -> falls back to structural
    fn parse_output(&self, output: &str, formula: &Formula) -> Result<SatResult, CegarError> {
        let trimmed = output.trim();

        if trimmed.starts_with("unsat") {
            return Ok(SatResult::Unsat);
        }

        if trimmed.starts_with("sat") {
            // Try to extract a model (cube) from the define-fun lines.
            let model = parse_model_to_cube(trimmed);
            return Ok(SatResult::Sat(model));
        }

        if trimmed.starts_with("unknown") {
            // Solver timed out or gave up -- fall back to structural.
            return self.fallback.check_sat(formula);
        }

        // Unexpected output -- fall back.
        self.fallback.check_sat(formula)
    }
}

impl SatOracle for SmtSatOracle {
    fn check_sat(&self, formula: &Formula) -> Result<SatResult, CegarError> {
        let script = self.generate_script(formula);

        match self.run_solver(&script) {
            Ok(output) => self.parse_output(&output, formula),
            Err(_e) => {
                // z4 not available or crashed -- fall back to structural.
                self.fallback.check_sat(formula)
            }
        }
    }

    fn name(&self) -> &str {
        "z4-smt"
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Recursively collect all free variables (with sorts) from a formula.
fn collect_vars(formula: &Formula, vars: &mut BTreeSet<(String, Sort)>) {
    formula.visit(&mut |node| {
        if let Formula::Var(name, sort) = node {
            vars.insert((name.clone(), sort.clone()));
        }
    });
}

/// Parse a z4 model into a Cube of equalities.
///
/// Extracts `(define-fun name () Sort value)` lines and produces
/// literals like `name = value`.
fn parse_model_to_cube(output: &str) -> Option<Cube> {
    let mut literals = Vec::new();

    for line in output.lines() {
        let trimmed = line.trim();
        if !trimmed.contains("define-fun") {
            continue;
        }

        // Parse: (define-fun <name> () <sort> <value>)
        if let Some((name, sort, value)) = parse_define_fun_to_formula(trimmed) {
            // Create literal: name = value
            let var = Formula::Var(name, sort);
            literals.push(Formula::Eq(Box::new(var), Box::new(value)));
        }
    }

    if literals.is_empty() {
        None
    } else {
        Some(Cube::new(literals))
    }
}

/// Parse a single `(define-fun name () Sort value)` line into (name, sort, value).
fn parse_define_fun_to_formula(line: &str) -> Option<(String, Sort, Formula)> {
    let content = line.trim().trim_start_matches('(');
    let rest = content.strip_prefix("define-fun ")?;

    // Extract name.
    let name_end = rest.find(|c: char| c.is_whitespace())?;
    let name = rest[..name_end].to_string();
    let rest = rest[name_end..].trim();

    // Skip "()" parameter list.
    let rest = rest.strip_prefix("()")?.trim();

    // Extract sort.
    let (sort_str, rest) = if rest.starts_with('(') {
        let depth = find_matching_paren(rest)?;
        (&rest[..=depth], rest[depth + 1..].trim())
    } else {
        let end = rest.find(|c: char| c.is_whitespace())?;
        (&rest[..end], rest[end..].trim())
    };

    // Parse sort.
    let sort = parse_sort(sort_str);

    // Parse value.
    let value_str = rest.trim_end_matches(')').trim();
    let value = parse_value(&sort, value_str)?;

    Some((name, sort, value))
}

/// Find the matching closing paren for an opening paren at position 0.
fn find_matching_paren(s: &str) -> Option<usize> {
    let mut depth = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Parse an SMT-LIB2 sort string.
fn parse_sort(s: &str) -> Sort {
    match s {
        "Bool" => Sort::Bool,
        "Int" => Sort::Int,
        _ if s.contains("BitVec") => {
            // (_ BitVec N)
            let inner = s.trim_start_matches("(_ BitVec").trim_end_matches(')').trim();
            let width: u32 = inner.parse().unwrap_or(32);
            Sort::BitVec(width)
        }
        _ => Sort::Int, // Default fallback.
    }
}

/// Parse a model value given a sort.
fn parse_value(sort: &Sort, s: &str) -> Option<Formula> {
    let s = s.trim();
    match sort {
        Sort::Bool => match s {
            "true" => Some(Formula::Bool(true)),
            "false" => Some(Formula::Bool(false)),
            _ => None,
        },
        Sort::Int => {
            if s.starts_with("(-") || s.starts_with("(- ") {
                let inner = s
                    .trim_start_matches('(')
                    .trim_start_matches('-')
                    .trim()
                    .trim_end_matches(')');
                let n: i128 = inner.parse().ok()?;
                Some(Formula::Int(-n))
            } else {
                let n: i128 = s.parse().ok()?;
                Some(Formula::Int(n))
            }
        }
        Sort::BitVec(w) => {
            if let Some(hex) = s.strip_prefix("#x") {
                let n = u128::from_str_radix(hex, 16).ok()?;
                Some(Formula::BitVec { value: n as i128, width: *w })
            } else if let Some(bin) = s.strip_prefix("#b") {
                let n = u128::from_str_radix(bin, 2).ok()?;
                Some(Formula::BitVec { value: n as i128, width: *w })
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Check if z4 is available on the system.
#[must_use]
pub(crate) fn z4_available() -> bool {
    Command::new("z4")
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|s| s.success())
}

/// Create the best available SAT oracle.
///
/// Returns `SmtSatOracle` if z4 is on PATH, otherwise `StructuralSatOracle`.
#[must_use]
pub(crate) fn default_oracle() -> Box<dyn SatOracle> {
    if z4_available() {
        Box::new(SmtSatOracle::new())
    } else {
        Box::new(StructuralSatOracle)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_structural_oracle_trivially_false() {
        let oracle = StructuralSatOracle;
        let result = oracle.check_sat(&Formula::Bool(false)).expect("should not error");
        assert_eq!(result, SatResult::Unsat);
    }

    #[test]
    fn test_structural_oracle_trivially_true() {
        let oracle = StructuralSatOracle;
        let result = oracle.check_sat(&Formula::Bool(true)).expect("should not error");
        assert_eq!(result, SatResult::Sat(None));
    }

    #[test]
    fn test_structural_oracle_contradiction() {
        let oracle = StructuralSatOracle;
        let x = Formula::Var("x".into(), Sort::Bool);
        let formula = Formula::And(vec![x.clone(), Formula::Not(Box::new(x))]);
        let result = oracle.check_sat(&formula).expect("should not error");
        assert_eq!(result, SatResult::Unsat);
    }

    #[test]
    fn test_structural_oracle_name() {
        let oracle = StructuralSatOracle;
        assert_eq!(oracle.name(), "structural");
    }

    #[test]
    fn test_smt_oracle_name() {
        let oracle = SmtSatOracle::new();
        assert_eq!(oracle.name(), "z4-smt");
    }

    #[test]
    fn test_smt_oracle_with_timeout() {
        let oracle = SmtSatOracle::new().with_timeout(5000);
        assert_eq!(oracle.timeout_ms, 5000);
    }

    #[test]
    fn test_smt_oracle_generate_script() {
        let oracle = SmtSatOracle::new();
        let x = Formula::Var("x".into(), Sort::Int);
        let formula = Formula::Lt(Box::new(x), Box::new(Formula::Int(10)));
        let script = oracle.generate_script(&formula);

        assert!(script.contains("(set-logic ALL)"));
        assert!(script.contains("(declare-const x Int)"));
        assert!(script.contains("(assert (< x 10))"));
        assert!(script.contains("(check-sat)"));
        assert!(script.contains("(exit)"));
    }

    #[test]
    fn test_smt_oracle_parse_unsat() {
        let oracle = SmtSatOracle::new();
        let result = oracle
            .parse_output("unsat\n", &Formula::Bool(false))
            .expect("should parse");
        assert_eq!(result, SatResult::Unsat);
    }

    #[test]
    fn test_smt_oracle_parse_sat_no_model() {
        let oracle = SmtSatOracle::new();
        let result = oracle
            .parse_output("sat\n", &Formula::Bool(true))
            .expect("should parse");
        assert_eq!(result, SatResult::Sat(None));
    }

    #[test]
    fn test_smt_oracle_parse_sat_with_model() {
        let oracle = SmtSatOracle::new();
        let output = "sat\n(model\n  (define-fun x () Int 42)\n)\n";
        let result = oracle
            .parse_output(output, &Formula::Bool(true))
            .expect("should parse");
        match result {
            SatResult::Sat(Some(cube)) => {
                assert_eq!(cube.len(), 1);
                // The literal should be x = 42.
                assert_eq!(
                    cube.literals[0],
                    Formula::Eq(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(42)),
                    )
                );
            }
            other => panic!("expected Sat(Some(_)), got: {other:?}"),
        }
    }

    #[test]
    fn test_smt_oracle_parse_unknown_falls_back() {
        let oracle = SmtSatOracle::new();
        // unknown should fall back to structural checker
        let result = oracle
            .parse_output("unknown\n", &Formula::Bool(true))
            .expect("should parse");
        // Structural on Bool(true) returns Sat(None)
        assert_eq!(result, SatResult::Sat(None));
    }

    #[test]
    fn test_smt_oracle_fallback_on_missing_binary() {
        // Use a non-existent binary path -- should fall back to structural.
        let oracle = SmtSatOracle::with_solver_path("/nonexistent/z4");
        let result = oracle
            .check_sat(&Formula::Bool(false))
            .expect("should fall back");
        assert_eq!(result, SatResult::Unsat);
    }

    #[test]
    fn test_default_oracle_returns_something() {
        let oracle = default_oracle();
        // Should work regardless of z4 availability.
        let result = oracle
            .check_sat(&Formula::Bool(false))
            .expect("should not error");
        assert_eq!(result, SatResult::Unsat);
    }

    #[test]
    fn test_parse_model_to_cube_int() {
        let output = "sat\n(model\n  (define-fun a () Int 5)\n  (define-fun b () Int 10)\n)\n";
        let cube = parse_model_to_cube(output).expect("should parse model");
        assert_eq!(cube.len(), 2);
    }

    #[test]
    fn test_parse_model_to_cube_bool() {
        let output = "sat\n(model\n  (define-fun flag () Bool true)\n)\n";
        let cube = parse_model_to_cube(output).expect("should parse model");
        assert_eq!(cube.len(), 1);
        assert_eq!(
            cube.literals[0],
            Formula::Eq(
                Box::new(Formula::Var("flag".into(), Sort::Bool)),
                Box::new(Formula::Bool(true)),
            )
        );
    }

    #[test]
    fn test_parse_model_to_cube_empty() {
        let output = "sat\n";
        assert!(parse_model_to_cube(output).is_none());
    }

    #[test]
    fn test_collect_vars_from_formula() {
        let mut vars = BTreeSet::new();
        let formula = Formula::And(vec![
            Formula::Var("x".into(), Sort::Int),
            Formula::Var("y".into(), Sort::Bool),
            Formula::Int(42),
        ]);
        collect_vars(&formula, &mut vars);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&("x".to_string(), Sort::Int)));
        assert!(vars.contains(&("y".to_string(), Sort::Bool)));
    }

    #[test]
    fn test_parse_sort_basic() {
        assert_eq!(parse_sort("Bool"), Sort::Bool);
        assert_eq!(parse_sort("Int"), Sort::Int);
        assert_eq!(parse_sort("(_ BitVec 32)"), Sort::BitVec(32));
    }

    #[test]
    fn test_parse_value_int() {
        assert_eq!(
            parse_value(&Sort::Int, "42"),
            Some(Formula::Int(42))
        );
        assert_eq!(
            parse_value(&Sort::Int, "(- 7)"),
            Some(Formula::Int(-7))
        );
    }

    #[test]
    fn test_parse_value_bool() {
        assert_eq!(
            parse_value(&Sort::Bool, "true"),
            Some(Formula::Bool(true))
        );
        assert_eq!(
            parse_value(&Sort::Bool, "false"),
            Some(Formula::Bool(false))
        );
    }

    #[test]
    fn test_parse_value_bitvec() {
        assert_eq!(
            parse_value(&Sort::BitVec(32), "#x0000000a"),
            Some(Formula::BitVec { value: 10, width: 32 })
        );
        assert_eq!(
            parse_value(&Sort::BitVec(4), "#b1010"),
            Some(Formula::BitVec { value: 10, width: 4 })
        );
    }

    // Integration test: if z4 is available, test a real query.
    #[test]
    fn test_smt_oracle_real_query_if_z4_available() {
        if !z4_available() {
            // z4 not installed; skip gracefully (test still passes).
            return;
        }

        let oracle = SmtSatOracle::new();

        // Trivially unsat: x < 0 AND x > 0 AND x = 0
        let x = Formula::Var("x".into(), Sort::Int);
        let unsat_formula = Formula::And(vec![
            Formula::Lt(Box::new(x.clone()), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(0))),
        ]);
        let result = oracle.check_sat(&unsat_formula).expect("should not error");
        assert_eq!(result, SatResult::Unsat, "x < 0 AND x > 0 should be unsat");

        // Trivially sat: x > 5
        let sat_formula = Formula::Gt(Box::new(x), Box::new(Formula::Int(5)));
        let result = oracle.check_sat(&sat_formula).expect("should not error");
        assert!(
            matches!(result, SatResult::Sat(_)),
            "x > 5 should be sat"
        );
    }
}
