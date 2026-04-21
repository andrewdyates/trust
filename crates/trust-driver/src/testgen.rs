// trust-driver/testgen.rs: Counterexample-driven test generation pipeline stage.
//
// When the verify phase returns `VerificationResult::Failed` with a counterexample,
// this stage passes the counterexample to trust-testgen to produce a `#[test]`
// function that reproduces the violation. Generated tests are written to a
// configurable output directory.
//
// Part of #521: Wire trust-testgen into pipeline for counterexample-based test generation
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

use trust_testgen::{
    CounterexampleTestInput, GeneratedTest, TestGenerator, generate_test_from_counterexample,
};
use trust_types::{CrateVerificationResult, VerificationResult};

use crate::VerifyOutput;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the test generation stage.
#[derive(Debug, Clone)]
pub(crate) struct TestgenConfig {
    /// Directory where generated test files are written.
    pub output_dir: PathBuf,
    /// Whether to generate tests from counterexamples (Failed VCs with CEX data).
    pub from_counterexamples: bool,
    /// Whether to generate boundary-value tests from unproved VCs (no CEX).
    pub from_unproved: bool,
}

impl Default for TestgenConfig {
    fn default() -> Self {
        Self {
            output_dir: PathBuf::from("trust_generated_tests"),
            from_counterexamples: true,
            from_unproved: false,
        }
    }
}

// ---------------------------------------------------------------------------
// TestgenOutput
// ---------------------------------------------------------------------------

/// Output of the test generation stage.
#[derive(Debug, Clone, Default)]
pub(crate) struct TestgenOutput {
    /// Number of tests generated from counterexamples.
    pub cex_tests_generated: usize,
    /// Number of tests generated from unproved VCs (boundary-value tests).
    pub boundary_tests_generated: usize,
    /// Path to the generated test file, if any tests were generated.
    pub output_file: Option<PathBuf>,
}

// ---------------------------------------------------------------------------
// Trait
// ---------------------------------------------------------------------------

/// Trait for counterexample-driven test generation after verification.
///
/// Implementations receive the verify output (which may contain detailed
/// per-function results with counterexamples) and produce test files.
pub(crate) trait TestgenStage {
    /// Generate tests from verification results.
    ///
    /// Returns the number of tests generated and the output path.
    fn generate(&self, verify_output: &VerifyOutput) -> TestgenOutput;
}

// ---------------------------------------------------------------------------
// Default implementation
// ---------------------------------------------------------------------------

/// Default test generation stage backed by trust-testgen.
///
/// Extracts counterexamples from `VerifyOutput::detailed_results` and generates
/// `#[test]` functions using `trust_testgen::generate_test_from_counterexample`.
pub(crate) struct DefaultTestgenStage {
    config: TestgenConfig,
}

impl DefaultTestgenStage {
    /// Create a new testgen stage with the given configuration.
    #[must_use]
    pub(crate) fn new(config: TestgenConfig) -> Self {
        Self { config }
    }

    /// Extract counterexample-based tests from detailed verification results.
    fn extract_cex_tests(results: &CrateVerificationResult) -> Vec<GeneratedTest> {
        let mut tests = Vec::new();

        for func in &results.functions {
            for (vc, result) in &func.results {
                if let VerificationResult::Failed {
                    counterexample: Some(ref cex),
                    ..
                } = result
                {
                    let input = CounterexampleTestInput {
                        counterexample: cex,
                        vc_kind: &vc.kind,
                        function_path: &func.function_path,
                    };
                    tests.push(generate_test_from_counterexample(&input));
                }
            }
        }

        tests
    }

    /// Extract boundary-value tests from unproved VCs (no counterexample).
    fn extract_boundary_tests(
        results: &CrateVerificationResult,
        funcs: &[trust_types::VerifiableFunction],
    ) -> Vec<GeneratedTest> {
        let mut tests = Vec::new();

        for func_result in &results.functions {
            // Find the matching VerifiableFunction for this result
            let verifiable_func = funcs.iter().find(|f| f.name == func_result.function_name);

            for (vc, result) in &func_result.results {
                let needs_test = matches!(
                    result,
                    VerificationResult::Failed { counterexample: None, .. }
                        | VerificationResult::Unknown { .. }
                        | VerificationResult::Timeout { .. }
                );

                if needs_test {
                    if let Some(func) = verifiable_func {
                        tests.push(TestGenerator::generate_test(vc, func));
                    }
                }
            }
        }

        tests
    }

    /// Write generated tests to a file in the output directory.
    fn write_test_file(output_dir: &Path, tests: &[GeneratedTest]) -> Option<PathBuf> {
        if tests.is_empty() {
            return None;
        }

        // Create the output directory if it does not exist.
        if let Err(e) = std::fs::create_dir_all(output_dir) {
            eprintln!("trust-testgen: failed to create output dir {}: {e}", output_dir.display());
            return None;
        }

        let file_content = TestGenerator::generate_test_file(tests);
        let output_path = output_dir.join("counterexample_tests.rs");

        match std::fs::write(&output_path, &file_content) {
            Ok(()) => Some(output_path),
            Err(e) => {
                eprintln!(
                    "trust-testgen: failed to write {}: {e}",
                    output_path.display()
                );
                None
            }
        }
    }
}

impl TestgenStage for DefaultTestgenStage {
    fn generate(&self, verify_output: &VerifyOutput) -> TestgenOutput {
        let detailed = match &verify_output.detailed_results {
            Some(results) => results,
            None => return TestgenOutput::default(),
        };

        let mut all_tests = Vec::new();
        let mut cex_count = 0;
        let mut boundary_count = 0;

        // Phase 1: Generate tests from counterexamples
        if self.config.from_counterexamples {
            let cex_tests = Self::extract_cex_tests(detailed);
            cex_count = cex_tests.len();
            all_tests.extend(cex_tests);
        }

        // Phase 2: Boundary-value tests from unproved VCs (no CEX)
        // Note: extract_boundary_tests needs VerifiableFunction data which is not
        // available in VerifyOutput. Boundary tests are generated only when the
        // from_unproved flag is set AND VerifiableFunction data is available
        // from a higher-level caller. For now, this stage focuses on CEX tests.
        let _ = (self.config.from_unproved, &mut boundary_count);

        // Write the test file
        let output_file = Self::write_test_file(&self.config.output_dir, &all_tests);

        TestgenOutput {
            cex_tests_generated: cex_count,
            boundary_tests_generated: boundary_count,
            output_file,
        }
    }
}

// ---------------------------------------------------------------------------
// Convenience function for standalone use
// ---------------------------------------------------------------------------

/// Generate tests from a `VerifyOutput` and write them to the given directory.
///
/// This is a convenience function for callers that do not need the full pipeline
/// integration. Returns the number of tests generated.
#[must_use]
pub(crate) fn generate_tests_from_verify_output(
    verify_output: &VerifyOutput,
    output_dir: &Path,
) -> TestgenOutput {
    let stage = DefaultTestgenStage::new(TestgenConfig {
        output_dir: output_dir.to_path_buf(),
        from_counterexamples: true,
        from_unproved: false,
    });
    stage.generate(verify_output)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_convergence::ProofFrontier;
    use trust_types::{
        BinOp, Counterexample, CounterexampleValue, Formula, FunctionVerificationResult,
        ProofStrength, SourceSpan, Ty, VcKind, VerificationCondition,
    };

    fn make_verify_output_with_cex() -> VerifyOutput {
        let cex = Counterexample::new(vec![
            ("a".to_string(), CounterexampleValue::Int(i128::from(i64::MAX))),
            ("b".to_string(), CounterexampleValue::Int(1)),
        ]);

        let mut crate_result = CrateVerificationResult::new("test_crate");
        crate_result.add_function(FunctionVerificationResult {
            function_path: "test_crate::add".to_string(),
            function_name: "add".to_string(),
            results: vec![
                (
                    VerificationCondition {
                        kind: VcKind::ArithmeticOverflow {
                            op: BinOp::Add,
                            operand_tys: (Ty::i32(), Ty::i32()),
                        },
                        function: "add".to_string(),
                        location: SourceSpan::default(),
                        formula: Formula::Bool(true),
                        contract_metadata: None,
                    },
                    VerificationResult::Failed {
                        solver: "z4".to_string(),
                        time_ms: 10,
                        counterexample: Some(cex),
                    },
                ),
                (
                    VerificationCondition {
                        kind: VcKind::DivisionByZero,
                        function: "add".to_string(),
                        location: SourceSpan::default(),
                        formula: Formula::Bool(false),
                        contract_metadata: None,
                    },
                    VerificationResult::Proved {
                        solver: "z4".to_string(),
                        time_ms: 5,
                        strength: ProofStrength::smt_unsat(),
                        proof_certificate: None,
                solver_warnings: None,
                    },
                ),
            ],
            from_notes: 0,
            with_assumptions: 0,
        });

        VerifyOutput {
            frontier: ProofFrontier {
                trusted: 1,
                certified: 0,
                runtime_checked: 0,
                failed: 1,
                unknown: 0,
            },
            fingerprint: None,
            vcs_dispatched: 2,
            vcs_failed: 1,
            detailed_results: Some(crate_result),
        }
    }

    fn make_verify_output_no_cex() -> VerifyOutput {
        let mut crate_result = CrateVerificationResult::new("test_crate");
        crate_result.add_function(FunctionVerificationResult {
            function_path: "test_crate::div".to_string(),
            function_name: "div".to_string(),
            results: vec![(
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "div".to_string(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Failed {
                    solver: "z4".to_string(),
                    time_ms: 7,
                    counterexample: None,
                },
            )],
            from_notes: 0,
            with_assumptions: 0,
        });

        VerifyOutput {
            frontier: ProofFrontier {
                trusted: 0,
                certified: 0,
                runtime_checked: 0,
                failed: 1,
                unknown: 0,
            },
            fingerprint: None,
            vcs_dispatched: 1,
            vcs_failed: 1,
            detailed_results: Some(crate_result),
        }
    }

    fn make_verify_output_no_detailed() -> VerifyOutput {
        VerifyOutput {
            frontier: ProofFrontier {
                trusted: 3,
                certified: 0,
                runtime_checked: 0,
                failed: 2,
                unknown: 0,
            },
            fingerprint: None,
            vcs_dispatched: 5,
            vcs_failed: 2,
            detailed_results: None,
        }
    }

    #[test]
    fn test_extract_cex_tests_finds_counterexamples() {
        let output = make_verify_output_with_cex();
        let detailed = output.detailed_results.as_ref().unwrap();
        let tests = DefaultTestgenStage::extract_cex_tests(detailed);

        assert_eq!(tests.len(), 1);
        assert!(tests[0].name.contains("cex"));
        assert!(tests[0].name.contains("arithmetic_overflow"));
        assert!(tests[0].code.contains("#[test]"));
        assert!(tests[0].code.contains("#[should_panic]"));
    }

    #[test]
    fn test_extract_cex_tests_empty_when_no_counterexample() {
        let output = make_verify_output_no_cex();
        let detailed = output.detailed_results.as_ref().unwrap();
        let tests = DefaultTestgenStage::extract_cex_tests(detailed);

        assert!(tests.is_empty());
    }

    #[test]
    fn test_generate_no_detailed_results() {
        let output = make_verify_output_no_detailed();
        let stage = DefaultTestgenStage::new(TestgenConfig::default());
        let result = stage.generate(&output);

        assert_eq!(result.cex_tests_generated, 0);
        assert_eq!(result.boundary_tests_generated, 0);
        assert!(result.output_file.is_none());
    }

    #[test]
    fn test_generate_writes_test_file() {
        let output = make_verify_output_with_cex();
        let tmp_dir = tempfile::tempdir().unwrap();
        let config = TestgenConfig {
            output_dir: tmp_dir.path().to_path_buf(),
            from_counterexamples: true,
            from_unproved: false,
        };
        let stage = DefaultTestgenStage::new(config);
        let result = stage.generate(&output);

        assert_eq!(result.cex_tests_generated, 1);
        assert!(result.output_file.is_some());

        let file_path = result.output_file.unwrap();
        assert!(file_path.exists());

        let content = std::fs::read_to_string(&file_path).unwrap();
        assert!(content.contains("#[test]"));
        assert!(content.contains("Auto-generated"));
        assert!(content.contains("trust-testgen"));
    }

    #[test]
    fn test_generate_disabled_counterexamples() {
        let output = make_verify_output_with_cex();
        let tmp_dir = tempfile::tempdir().unwrap();
        let config = TestgenConfig {
            output_dir: tmp_dir.path().to_path_buf(),
            from_counterexamples: false,
            from_unproved: false,
        };
        let stage = DefaultTestgenStage::new(config);
        let result = stage.generate(&output);

        assert_eq!(result.cex_tests_generated, 0);
        assert!(result.output_file.is_none());
    }

    #[test]
    fn test_convenience_function() {
        let output = make_verify_output_with_cex();
        let tmp_dir = tempfile::tempdir().unwrap();
        let result = generate_tests_from_verify_output(&output, tmp_dir.path());

        assert_eq!(result.cex_tests_generated, 1);
        assert!(result.output_file.is_some());
    }

    #[test]
    fn test_multiple_counterexamples_across_functions() {
        let cex1 = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(0)),
        ]);
        let cex2 = Counterexample::new(vec![
            ("idx".to_string(), CounterexampleValue::Uint(100)),
        ]);

        let mut crate_result = CrateVerificationResult::new("multi_cex");
        crate_result.add_function(FunctionVerificationResult {
            function_path: "multi_cex::div".to_string(),
            function_name: "div".to_string(),
            results: vec![(
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "div".to_string(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Failed {
                    solver: "z4".to_string(),
                    time_ms: 5,
                    counterexample: Some(cex1),
                },
            )],
            from_notes: 0,
            with_assumptions: 0,
        });
        crate_result.add_function(FunctionVerificationResult {
            function_path: "multi_cex::access".to_string(),
            function_name: "access".to_string(),
            results: vec![(
                VerificationCondition {
                    kind: VcKind::IndexOutOfBounds,
                    function: "access".to_string(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Failed {
                    solver: "zani".to_string(),
                    time_ms: 15,
                    counterexample: Some(cex2),
                },
            )],
            from_notes: 0,
            with_assumptions: 0,
        });

        let tests = DefaultTestgenStage::extract_cex_tests(&crate_result);
        assert_eq!(tests.len(), 2);
        assert!(tests[0].name.contains("division_by_zero"));
        assert!(tests[1].name.contains("index_out_of_bounds"));
    }
}
