// trust-testgen: Regression test suite management
//
// Captures counterexamples and verification failures as persistent regression
// tests. Supports minimization, serialization, and diffing between suite versions.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use std::fmt::Write;

use serde::{Deserialize, Serialize};
use trust_types::{Counterexample, CounterexampleValue, VcKind, VerificationCondition, VerificationResult};

use crate::{sanitize_ident, vc_kind_suffix, GeneratedTest};

/// Error type for regression suite operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum RegressionError {
    #[error("serialization failed: {0}")]
    Serialize(#[from] serde_json::Error),

    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("duplicate test name: {name}")]
    DuplicateName { name: String },
}

/// A single regression test capturing a specific verification failure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RegressionTest {
    /// Unique test name (e.g., `regression_add_numbers_arithmetic_overflow_0`).
    pub(crate) test_name: String,
    /// Fully qualified source function path.
    pub(crate) source_function: String,
    /// The kind of verification condition that failed.
    pub(crate) vc_kind_tag: String,
    /// Concrete input values as (variable_name, value_string) pairs.
    pub(crate) input_values: Vec<(String, String)>,
    /// Expected output or behavior description (if known).
    pub(crate) expected_output: Option<String>,
    /// Commit hash when this regression test was discovered.
    pub(crate) discovered_at: Option<String>,
}

impl RegressionTest {
    /// Create a new regression test.
    #[must_use]
    pub fn new(
        test_name: impl Into<String>,
        source_function: impl Into<String>,
        vc_kind_tag: impl Into<String>,
    ) -> Self {
        Self {
            test_name: test_name.into(),
            source_function: source_function.into(),
            vc_kind_tag: vc_kind_tag.into(),
            input_values: Vec::new(),
            expected_output: None,
            discovered_at: None,
        }
    }

    /// Set input values.
    #[must_use]
    pub fn with_inputs(mut self, inputs: Vec<(String, String)>) -> Self {
        self.input_values = inputs;
        self
    }

    /// Set the commit hash where this was discovered.
    #[must_use]
    pub fn with_discovered_at(mut self, commit: impl Into<String>) -> Self {
        self.discovered_at = Some(commit.into());
        self
    }

    /// Set expected output.
    #[must_use]
    pub fn with_expected_output(mut self, output: impl Into<String>) -> Self {
        self.expected_output = Some(output.into());
        self
    }

    /// Generate a `GeneratedTest` from this regression test.
    #[must_use]
    pub fn to_generated_test(&self) -> GeneratedTest {
        let mut body = String::new();
        let _ = writeln!(body, 
            "    // Regression test for {} ({})",
            self.source_function, self.vc_kind_tag,
        );
        if let Some(ref commit) = self.discovered_at {
            let _ = writeln!(body, "    // Discovered at commit: {commit}");
        }

        for (name, value) in &self.input_values {
            let sanitized = sanitize_ident(name);
            let _ = writeln!(body, "    let {sanitized} = {value};");
        }

        if let Some(ref expected) = self.expected_output {
            let _ = write!(body, 
                "    // Expected: {expected}\n\
                 \x20   let _ = ({});\n",
                self.input_values
                    .iter()
                    .map(|(n, _)| sanitize_ident(n))
                    .collect::<Vec<_>>()
                    .join(", "),
            );
        } else {
            body.push_str("    // PLACEHOLDER: wire up function call and assertion\n");
        }

        let code = format!("#[test]\nfn {}() {{\n{body}}}", self.test_name);

        GeneratedTest {
            name: self.test_name.clone(),
            code,
            boundary_values: self
                .input_values
                .iter()
                .map(|(n, v)| format!("{n} = {v}"))
                .collect(),
        }
    }
}

/// A collection of regression tests with metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegressionSuite {
    /// Human-readable suite name.
    pub(crate) name: String,
    /// Suite version, incremented on each modification.
    pub(crate) version: u64,
    /// The regression tests.
    pub(crate) tests: Vec<RegressionTest>,
}

impl RegressionSuite {
    /// Create a new empty regression suite.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            version: 1,
            tests: Vec::new(),
        }
    }

    /// Number of tests in the suite.
    #[must_use]
    pub fn len(&self) -> usize {
        self.tests.len()
    }

    /// Whether the suite is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.tests.is_empty()
    }

    /// Add a regression test. Returns error if name already exists.
    pub fn add(&mut self, test: RegressionTest) -> Result<(), RegressionError> {
        if self.tests.iter().any(|t| t.test_name == test.test_name) {
            return Err(RegressionError::DuplicateName { name: test.test_name });
        }
        self.tests.push(test);
        self.version += 1;
        Ok(())
    }

    /// Add a regression test from a counterexample.
    ///
    /// Creates a `RegressionTest` from the counterexample's variable assignments
    /// and the VC kind, then adds it to the suite.
    pub fn add_from_counterexample(
        &mut self,
        cex: &Counterexample,
        vc_kind: &VcKind,
        function_path: &str,
        commit_hash: Option<&str>,
    ) -> Result<(), RegressionError> {
        let sanitized_func = sanitize_ident(function_path);
        let kind_tag = vc_kind_suffix(vc_kind);
        let idx = self.tests.len();
        let test_name = format!("regression_{sanitized_func}_{kind_tag}_{idx}");

        let input_values: Vec<(String, String)> = cex
            .assignments
            .iter()
            .map(|(name, val)| (name.clone(), format_cex_value(val)))
            .collect();

        let mut test = RegressionTest::new(test_name, function_path, kind_tag)
            .with_inputs(input_values);

        if let Some(commit) = commit_hash {
            test = test.with_discovered_at(commit);
        }

        self.add(test)
    }

    /// Add a regression test from a verification failure (VC + result pair).
    ///
    /// If the result contains a counterexample, its values are captured.
    /// Otherwise, a placeholder regression test is created.
    pub fn add_from_verification_failure(
        &mut self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        commit_hash: Option<&str>,
    ) -> Result<(), RegressionError> {
        match result {
            VerificationResult::Failed { counterexample: Some(cex), .. } => {
                self.add_from_counterexample(cex, &vc.kind, &vc.function, commit_hash)
            }
            VerificationResult::Failed { counterexample: None, .. }
            | VerificationResult::Unknown { .. }
            | VerificationResult::Timeout { .. } => {
                let sanitized_func = sanitize_ident(&vc.function);
                let kind_tag = vc_kind_suffix(&vc.kind);
                let idx = self.tests.len();
                let test_name = format!("regression_{sanitized_func}_{kind_tag}_{idx}");

                let mut test = RegressionTest::new(test_name, &vc.function, kind_tag);
                if let Some(commit) = commit_hash {
                    test = test.with_discovered_at(commit);
                }

                self.add(test)
            }
            VerificationResult::Proved { .. } => Ok(()), // Not a failure
            _ => Ok(()),
        }
    }

    /// Serialize the suite to JSON.
    pub fn to_json(&self) -> Result<String, RegressionError> {
        serde_json::to_string_pretty(self).map_err(RegressionError::from)
    }

    /// Deserialize a suite from JSON.
    pub fn from_json(json: &str) -> Result<Self, RegressionError> {
        serde_json::from_str(json).map_err(RegressionError::from)
    }

    /// Get test names as a set for diffing.
    fn test_name_set(&self) -> FxHashSet<&str> {
        self.tests.iter().map(|t| t.test_name.as_str()).collect()
    }

    /// Build a lookup map from test name to test for diffing.
    fn test_map(&self) -> FxHashMap<&str, &RegressionTest> {
        self.tests.iter().map(|t| (t.test_name.as_str(), t)).collect()
    }
}

/// Result of diffing two regression suites.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SuiteDiff {
    /// Tests present in `new` but not in `old`.
    pub(crate) added: Vec<String>,
    /// Tests present in `old` but not in `new`.
    pub(crate) removed: Vec<String>,
    /// Tests present in both but with different content.
    pub(crate) changed: Vec<String>,
    /// Tests identical in both suites.
    pub(crate) unchanged: Vec<String>,
}

impl SuiteDiff {
    /// Whether the suites are identical.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.added.is_empty() && self.removed.is_empty() && self.changed.is_empty()
    }

    /// Total number of differences.
    #[must_use]
    pub fn diff_count(&self) -> usize {
        self.added.len() + self.removed.len() + self.changed.len()
    }

    /// Human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "+{} added, -{} removed, ~{} changed, ={} unchanged",
            self.added.len(),
            self.removed.len(),
            self.changed.len(),
            self.unchanged.len(),
        )
    }
}

/// Diff two regression suites.
///
/// Compares tests by name, then by content for tests present in both.
#[must_use]
pub fn diff_suites(old: &RegressionSuite, new: &RegressionSuite) -> SuiteDiff {
    let old_names = old.test_name_set();
    let new_names = new.test_name_set();
    let old_map = old.test_map();
    let new_map = new.test_map();

    let added: Vec<String> = new_names
        .difference(&old_names)
        .map(|n| (*n).to_string())
        .collect();

    let removed: Vec<String> = old_names
        .difference(&new_names)
        .map(|n| (*n).to_string())
        .collect();

    let mut changed = Vec::new();
    let mut unchanged = Vec::new();

    for name in old_names.intersection(&new_names) {
        let old_test = old_map[name];
        let new_test = new_map[name];
        if old_test == new_test {
            unchanged.push((*name).to_string());
        } else {
            changed.push((*name).to_string());
        }
    }

    SuiteDiff { added, removed, changed, unchanged }
}

/// Minimize a regression suite by removing redundant tests.
///
/// Two tests are considered redundant if they target the same function and
/// VC kind with the same input values. The first occurrence is kept.
#[must_use]
pub fn minimize_suite(suite: &RegressionSuite) -> RegressionSuite {
    type TestKey = (String, String, Vec<(String, String)>);
    let mut seen: FxHashSet<TestKey> = FxHashSet::default();
    let mut minimized_tests = Vec::new();

    for test in &suite.tests {
        let key = (
            test.source_function.clone(),
            test.vc_kind_tag.clone(),
            test.input_values.clone(),
        );
        if seen.insert(key) {
            minimized_tests.push(test.clone());
        }
    }

    RegressionSuite {
        name: suite.name.clone(),
        version: suite.version + 1,
        tests: minimized_tests,
    }
}

/// Format a counterexample value as a Rust literal string.
fn format_cex_value(val: &CounterexampleValue) -> String {
    match val {
        CounterexampleValue::Bool(b) => format!("{b}"),
        CounterexampleValue::Int(n) => format!("{n}_i128"),
        CounterexampleValue::Uint(n) => format!("{n}_u128"),
        CounterexampleValue::Float(n) => {
            let s = format!("{n}");
            if s.contains('.') { format!("{s}_f64") } else { format!("{s}.0_f64") }
        }
        _ => "unknown".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{BinOp, Formula, SourceSpan, Ty};

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

    // -----------------------------------------------------------------------
    // RegressionTest
    // -----------------------------------------------------------------------

    #[test]
    fn test_regression_test_new() {
        let rt = RegressionTest::new("test_a", "crate::func", "division_by_zero");
        assert_eq!(rt.test_name, "test_a");
        assert_eq!(rt.source_function, "crate::func");
        assert_eq!(rt.vc_kind_tag, "division_by_zero");
        assert!(rt.input_values.is_empty());
        assert!(rt.expected_output.is_none());
        assert!(rt.discovered_at.is_none());
    }

    #[test]
    fn test_regression_test_builder() {
        let rt = RegressionTest::new("test_b", "f", "overflow")
            .with_inputs(vec![("x".into(), "42".into())])
            .with_discovered_at("abc123")
            .with_expected_output("panic");
        assert_eq!(rt.input_values.len(), 1);
        assert_eq!(rt.discovered_at.as_deref(), Some("abc123"));
        assert_eq!(rt.expected_output.as_deref(), Some("panic"));
    }

    #[test]
    fn test_regression_test_to_generated_test() {
        let rt = RegressionTest::new("test_gen", "my::func", "arithmetic_overflow")
            .with_inputs(vec![
                ("a".into(), "i32::MAX".into()),
                ("b".into(), "1".into()),
            ])
            .with_discovered_at("deadbeef");

        let generated = rt.to_generated_test();
        assert_eq!(generated.name, "test_gen");
        assert!(generated.code.contains("#[test]"));
        assert!(generated.code.contains("fn test_gen()"));
        assert!(generated.code.contains("let a = i32::MAX;"));
        assert!(generated.code.contains("let b = 1;"));
        assert!(generated.code.contains("deadbeef"));
        assert_eq!(generated.boundary_values.len(), 2);
    }

    #[test]
    fn test_regression_test_to_generated_test_with_expected() {
        let rt = RegressionTest::new("test_exp", "f", "postcondition")
            .with_inputs(vec![("x".into(), "0".into())])
            .with_expected_output("result > 0");

        let generated = rt.to_generated_test();
        assert!(generated.code.contains("Expected: result > 0"));
    }

    // -----------------------------------------------------------------------
    // RegressionSuite
    // -----------------------------------------------------------------------

    #[test]
    fn test_suite_new_empty() {
        let suite = RegressionSuite::new("my_suite");
        assert_eq!(suite.name, "my_suite");
        assert_eq!(suite.version, 1);
        assert!(suite.is_empty());
        assert_eq!(suite.len(), 0);
    }

    #[test]
    fn test_suite_add() {
        let mut suite = RegressionSuite::new("s");
        let rt = RegressionTest::new("test_1", "f", "overflow");
        suite.add(rt).expect("should add");
        assert_eq!(suite.len(), 1);
        assert_eq!(suite.version, 2);
    }

    #[test]
    fn test_suite_add_duplicate_name_errors() {
        let mut suite = RegressionSuite::new("s");
        suite
            .add(RegressionTest::new("test_dup", "f", "overflow"))
            .expect("first add");
        let result = suite.add(RegressionTest::new("test_dup", "g", "other"));
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("test_dup"));
    }

    #[test]
    fn test_suite_add_from_counterexample() {
        let mut suite = RegressionSuite::new("cex_suite");
        let cex = make_cex(&[
            ("a", CounterexampleValue::Int(i64::MAX as i128)),
            ("b", CounterexampleValue::Int(1)),
        ]);
        let vc_kind = VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::i32(), Ty::i32()),
        };

        suite
            .add_from_counterexample(&cex, &vc_kind, "math::add", Some("abc123"))
            .expect("should add from cex");

        assert_eq!(suite.len(), 1);
        let test = &suite.tests[0];
        assert!(test.test_name.starts_with("regression_math__add_arithmetic_overflow_"));
        assert_eq!(test.source_function, "math::add");
        assert_eq!(test.input_values.len(), 2);
        assert_eq!(test.discovered_at.as_deref(), Some("abc123"));
    }

    #[test]
    fn test_suite_add_from_verification_failure_with_cex() {
        let mut suite = RegressionSuite::new("fail_suite");
        let cex = Counterexample::new(vec![("x".into(), CounterexampleValue::Int(0))]);
        let vc = make_vc(VcKind::DivisionByZero, "math::divide");
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 5,
            counterexample: Some(cex),
        };

        suite
            .add_from_verification_failure(&vc, &result, Some("def456"))
            .expect("should add from failure");

        assert_eq!(suite.len(), 1);
        assert!(suite.tests[0].test_name.contains("division_by_zero"));
    }

    #[test]
    fn test_suite_add_from_verification_failure_without_cex() {
        let mut suite = RegressionSuite::new("no_cex");
        let vc = make_vc(VcKind::Postcondition, "api::check");
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 5,
            counterexample: None,
        };

        suite
            .add_from_verification_failure(&vc, &result, None)
            .expect("should add placeholder");

        assert_eq!(suite.len(), 1);
        assert!(suite.tests[0].input_values.is_empty());
    }

    #[test]
    fn test_suite_add_from_proved_is_noop() {
        let mut suite = RegressionSuite::new("proved");
        let vc = make_vc(VcKind::DivisionByZero, "f");
        let result = VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 5,
            strength: trust_types::ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, };

        suite
            .add_from_verification_failure(&vc, &result, None)
            .expect("should be noop");

        assert!(suite.is_empty());
    }

    #[test]
    fn test_suite_add_from_timeout() {
        let mut suite = RegressionSuite::new("timeout");
        let vc = make_vc(VcKind::IndexOutOfBounds, "buf::get");
        let result = VerificationResult::Timeout {
            solver: "z4".into(),
            timeout_ms: 1000,
        };

        suite
            .add_from_verification_failure(&vc, &result, None)
            .expect("should add");

        assert_eq!(suite.len(), 1);
    }

    // -----------------------------------------------------------------------
    // Serialization
    // -----------------------------------------------------------------------

    #[test]
    fn test_suite_serialization_roundtrip() {
        let mut suite = RegressionSuite::new("roundtrip");
        suite
            .add(
                RegressionTest::new("test_rt", "f::g", "overflow")
                    .with_inputs(vec![("x".into(), "42".into())])
                    .with_discovered_at("abc")
                    .with_expected_output("panic"),
            )
            .expect("add");

        let json = suite.to_json().expect("serialize");
        let deserialized = RegressionSuite::from_json(&json).expect("deserialize");

        assert_eq!(deserialized.name, "roundtrip");
        assert_eq!(deserialized.len(), 1);
        assert_eq!(deserialized.tests[0].test_name, "test_rt");
        assert_eq!(deserialized.tests[0].input_values.len(), 1);
        assert_eq!(deserialized.tests[0].discovered_at.as_deref(), Some("abc"));
        assert_eq!(
            deserialized.tests[0].expected_output.as_deref(),
            Some("panic")
        );
    }

    #[test]
    fn test_suite_empty_serialization_roundtrip() {
        let suite = RegressionSuite::new("empty");
        let json = suite.to_json().expect("serialize");
        let deserialized = RegressionSuite::from_json(&json).expect("deserialize");
        assert!(deserialized.is_empty());
        assert_eq!(deserialized.version, 1);
    }

    #[test]
    fn test_suite_from_json_invalid() {
        let result = RegressionSuite::from_json("not json");
        assert!(result.is_err());
    }

    // -----------------------------------------------------------------------
    // Minimization
    // -----------------------------------------------------------------------

    #[test]
    fn test_minimize_suite_removes_duplicates() {
        let mut suite = RegressionSuite::new("dup");
        // Manually add duplicates (bypass add() uniqueness check by using different names)
        suite.tests.push(
            RegressionTest::new("test_0", "f", "overflow")
                .with_inputs(vec![("x".into(), "1".into())]),
        );
        suite.tests.push(
            RegressionTest::new("test_1", "f", "overflow")
                .with_inputs(vec![("x".into(), "1".into())]),
        );
        suite.tests.push(
            RegressionTest::new("test_2", "g", "overflow")
                .with_inputs(vec![("x".into(), "1".into())]),
        );

        let minimized = minimize_suite(&suite);
        // test_0 and test_1 are redundant (same function, kind, inputs)
        assert_eq!(minimized.len(), 2);
        assert_eq!(minimized.tests[0].test_name, "test_0");
        assert_eq!(minimized.tests[1].test_name, "test_2");
    }

    #[test]
    fn test_minimize_suite_keeps_distinct() {
        let mut suite = RegressionSuite::new("distinct");
        suite.tests.push(
            RegressionTest::new("test_0", "f", "overflow")
                .with_inputs(vec![("x".into(), "1".into())]),
        );
        suite.tests.push(
            RegressionTest::new("test_1", "f", "overflow")
                .with_inputs(vec![("x".into(), "2".into())]),
        );

        let minimized = minimize_suite(&suite);
        assert_eq!(minimized.len(), 2);
    }

    #[test]
    fn test_minimize_empty_suite() {
        let suite = RegressionSuite::new("empty");
        let minimized = minimize_suite(&suite);
        assert!(minimized.is_empty());
    }

    #[test]
    fn test_minimize_increments_version() {
        let suite = RegressionSuite::new("ver");
        assert_eq!(suite.version, 1);
        let minimized = minimize_suite(&suite);
        assert_eq!(minimized.version, 2);
    }

    // -----------------------------------------------------------------------
    // Diffing
    // -----------------------------------------------------------------------

    #[test]
    fn test_diff_identical_suites() {
        let mut suite = RegressionSuite::new("s");
        suite.tests.push(RegressionTest::new("test_a", "f", "overflow"));

        let diff = diff_suites(&suite, &suite);
        assert!(diff.is_empty());
        assert_eq!(diff.diff_count(), 0);
        assert_eq!(diff.unchanged.len(), 1);
    }

    #[test]
    fn test_diff_added_tests() {
        let old = RegressionSuite::new("old");
        let mut new = RegressionSuite::new("new");
        new.tests.push(RegressionTest::new("test_a", "f", "overflow"));

        let diff = diff_suites(&old, &new);
        assert_eq!(diff.added.len(), 1);
        assert!(diff.added.contains(&"test_a".to_string()));
        assert!(diff.removed.is_empty());
        assert!(diff.changed.is_empty());
    }

    #[test]
    fn test_diff_removed_tests() {
        let mut old = RegressionSuite::new("old");
        old.tests.push(RegressionTest::new("test_a", "f", "overflow"));
        let new = RegressionSuite::new("new");

        let diff = diff_suites(&old, &new);
        assert!(diff.added.is_empty());
        assert_eq!(diff.removed.len(), 1);
        assert!(diff.removed.contains(&"test_a".to_string()));
    }

    #[test]
    fn test_diff_changed_tests() {
        let mut old = RegressionSuite::new("old");
        old.tests.push(
            RegressionTest::new("test_a", "f", "overflow")
                .with_inputs(vec![("x".into(), "1".into())]),
        );

        let mut new = RegressionSuite::new("new");
        new.tests.push(
            RegressionTest::new("test_a", "f", "overflow")
                .with_inputs(vec![("x".into(), "2".into())]),
        );

        let diff = diff_suites(&old, &new);
        assert!(diff.added.is_empty());
        assert!(diff.removed.is_empty());
        assert_eq!(diff.changed.len(), 1);
        assert!(diff.changed.contains(&"test_a".to_string()));
    }

    #[test]
    fn test_diff_mixed_changes() {
        let mut old = RegressionSuite::new("old");
        old.tests.push(RegressionTest::new("kept", "f", "a"));
        old.tests.push(
            RegressionTest::new("modified", "g", "b")
                .with_inputs(vec![("x".into(), "old".into())]),
        );
        old.tests.push(RegressionTest::new("removed", "h", "c"));

        let mut new = RegressionSuite::new("new");
        new.tests.push(RegressionTest::new("kept", "f", "a"));
        new.tests.push(
            RegressionTest::new("modified", "g", "b")
                .with_inputs(vec![("x".into(), "new".into())]),
        );
        new.tests.push(RegressionTest::new("added", "i", "d"));

        let diff = diff_suites(&old, &new);
        assert_eq!(diff.added.len(), 1);
        assert_eq!(diff.removed.len(), 1);
        assert_eq!(diff.changed.len(), 1);
        assert_eq!(diff.unchanged.len(), 1);
        assert_eq!(diff.diff_count(), 3);
    }

    #[test]
    fn test_diff_empty_suites() {
        let old = RegressionSuite::new("old");
        let new = RegressionSuite::new("new");
        let diff = diff_suites(&old, &new);
        assert!(diff.is_empty());
    }

    #[test]
    fn test_diff_summary_format() {
        let old = RegressionSuite::new("old");
        let mut new = RegressionSuite::new("new");
        new.tests.push(RegressionTest::new("test_a", "f", "overflow"));

        let diff = diff_suites(&old, &new);
        let summary = diff.summary();
        assert!(summary.contains("+1 added"));
        assert!(summary.contains("-0 removed"));
    }

    // -----------------------------------------------------------------------
    // format_cex_value
    // -----------------------------------------------------------------------

    #[test]
    fn test_format_cex_value_bool() {
        assert_eq!(format_cex_value(&CounterexampleValue::Bool(true)), "true");
        assert_eq!(format_cex_value(&CounterexampleValue::Bool(false)), "false");
    }

    #[test]
    fn test_format_cex_value_int() {
        assert_eq!(format_cex_value(&CounterexampleValue::Int(42)), "42_i128");
        assert_eq!(format_cex_value(&CounterexampleValue::Int(-1)), "-1_i128");
    }

    #[test]
    fn test_format_cex_value_uint() {
        assert_eq!(format_cex_value(&CounterexampleValue::Uint(0)), "0_u128");
    }

    #[test]
    fn test_format_cex_value_float() {
        assert_eq!(
            format_cex_value(&CounterexampleValue::Float(3.125)),
            "3.125_f64"
        );
        assert_eq!(
            format_cex_value(&CounterexampleValue::Float(42.0)),
            "42.0_f64"
        );
    }
}
