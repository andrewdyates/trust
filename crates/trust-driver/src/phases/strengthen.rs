// trust-driver/phases/strengthen.rs: Production StrengthenPhase implementation.
//
// Bridges trust-driver's `StrengthenPhase` trait to `trust_strengthen::run()`.
// Converts the loop's `VerifyOutput` (aggregate frontier counts) into a
// `CrateVerificationResult` that trust-strengthen can analyze for failure
// patterns and spec proposals.
//
// For M5 initial impl, uses heuristic-only mode (NoOpLlm) — no actual LLM
// calls. The LLM backend can be wired in later.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;

use trust_strengthen::{LlmBackend, NoOpLlm, StrengthenConfig, StrengthenOutput};
use trust_types::{
    CrateVerificationResult, Formula, FunctionVerificationResult, SourceSpan, VcKind,
    VerificationCondition, VerificationResult,
};

use crate::{StrengthenPhase, VerifyOutput};

/// Production `StrengthenPhase` that delegates to `trust_strengthen::run()`.
///
/// Converts the loop's aggregate `VerifyOutput` into a `CrateVerificationResult`
/// with synthetic per-function entries, then runs the strengthen pipeline to
/// generate spec proposals from failure patterns.
pub struct ProductionStrengthenPhase {
    config: StrengthenConfig,
    llm: Box<dyn LlmBackend>,
}

impl ProductionStrengthenPhase {
    /// Create a new production strengthen phase with heuristic-only mode.
    #[must_use]
    pub fn heuristic_only(config: StrengthenConfig) -> Self {
        Self {
            config,
            llm: Box::new(NoOpLlm),
        }
    }

    /// Create a new production strengthen phase with a custom LLM backend.
    pub(crate) fn with_llm(config: StrengthenConfig, llm: Box<dyn LlmBackend>) -> Self {
        Self { config, llm }
    }
}

impl StrengthenPhase for ProductionStrengthenPhase {
    fn strengthen(&self, source_path: &Path, verify_output: &VerifyOutput) -> StrengthenOutput {
        // tRust #684: Use detailed_results when available for VcKind-specific proposals
        // (overflow, div-zero, OOB, etc.) instead of falling back to generic Assertion.
        let crate_result = if let Some(ref detailed) = verify_output.detailed_results {
            detailed.clone()
        } else {
            verify_output_to_crate_result(source_path, verify_output)
        };
        trust_strengthen::run(&crate_result, &self.config, self.llm.as_ref())
    }
}

/// Convert a `VerifyOutput` (aggregate counts) to a `CrateVerificationResult`.
///
/// `VerifyOutput` only carries aggregate frontier counts, not per-function VC
/// details. We synthesize a `CrateVerificationResult` with one synthetic
/// function entry per failed VC, using `VcKind::Assertion` as a generic
/// placeholder. This gives trust-strengthen enough structure to apply its
/// heuristic rules.
///
/// When the verify phase is extended to carry detailed per-function results
/// (e.g., via a `DetailedVerifyOutput`), this conversion can be replaced with
/// a direct mapping.
fn verify_output_to_crate_result(
    source_path: &Path,
    verify_output: &VerifyOutput,
) -> CrateVerificationResult {
    let crate_name = source_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("unknown")
        .to_string();

    // Build a single synthetic function with VCs matching the aggregate counts.
    let mut results = Vec::new();

    // Add proved VCs
    for i in 0..verify_output.frontier.trusted {
        results.push((
            VerificationCondition {
                kind: VcKind::Assertion {
                    message: "synthetic VC".into(),
                },
                function: format!("{crate_name}::fn_{i}"),
                location: SourceSpan::default(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            VerificationResult::Proved {
                solver: "synthetic".into(),
                time_ms: 0,
                strength: trust_types::ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, },
        ));
    }

    // Add failed VCs
    for i in 0..verify_output.vcs_failed {
        results.push((
            VerificationCondition {
                kind: VcKind::Assertion {
                    message: "synthetic VC".into(),
                },
                function: format!("{crate_name}::failed_{i}"),
                location: SourceSpan::default(),
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            VerificationResult::Failed {
                solver: "synthetic".into(),
                time_ms: 0,
                counterexample: None,
            },
        ));
    }

    let function = FunctionVerificationResult {
        function_path: format!("{crate_name}::synthetic"),
        function_name: "synthetic".into(),
        results,
        from_notes: 0,
        with_assumptions: 0,
    };

    CrateVerificationResult {
        crate_name,
        functions: vec![function],
        total_from_notes: 0,
        total_with_assumptions: 0,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ProofFrontier;
    use std::path::PathBuf;

    fn test_verify_output(trusted: u32, failed: usize) -> VerifyOutput {
        VerifyOutput {
            frontier: ProofFrontier {
                trusted,
                certified: 0,
                runtime_checked: 0,
                failed: failed as u32,
                unknown: 0,
            },
            fingerprint: None,
            vcs_dispatched: trusted as usize + failed,
            vcs_failed: failed,
            detailed_results: None,
        }
    }

    #[test]
    fn test_production_strengthen_heuristic_no_failures() {
        let phase = ProductionStrengthenPhase::heuristic_only(StrengthenConfig::default());
        let v_out = test_verify_output(5, 0);
        let result = phase.strengthen(&PathBuf::from("/tmp/test.rs"), &v_out);

        assert!(!result.has_proposals);
        assert_eq!(result.failures_analyzed, 0);
        assert!(result.proposals.is_empty());
    }

    #[test]
    fn test_production_strengthen_heuristic_with_failures() {
        let phase = ProductionStrengthenPhase::heuristic_only(StrengthenConfig::default());
        let v_out = test_verify_output(3, 2);
        let result = phase.strengthen(&PathBuf::from("/tmp/test.rs"), &v_out);

        // trust-strengthen's heuristic rules may or may not produce proposals
        // for VcKind::Assertion, but the pipeline executes without error.
        assert_eq!(result.failures_analyzed, 2);
    }

    #[test]
    fn test_verify_output_to_crate_result_counts() {
        let v_out = test_verify_output(3, 2);
        let result = verify_output_to_crate_result(Path::new("/tmp/my_crate.rs"), &v_out);

        assert_eq!(result.crate_name, "my_crate");
        assert_eq!(result.functions.len(), 1);
        let func = &result.functions[0];
        assert_eq!(func.results.len(), 5); // 3 proved + 2 failed

        let proved = func
            .results
            .iter()
            .filter(|(_, r)| matches!(r, VerificationResult::Proved { .. }))
            .count();
        let failed = func
            .results
            .iter()
            .filter(|(_, r)| matches!(r, VerificationResult::Failed { .. }))
            .count();
        assert_eq!(proved, 3);
        assert_eq!(failed, 2);
    }

    #[test]
    fn test_verify_output_to_crate_result_zero_failures() {
        let v_out = test_verify_output(5, 0);
        let result = verify_output_to_crate_result(Path::new("/tmp/clean.rs"), &v_out);

        assert_eq!(result.crate_name, "clean");
        let func = &result.functions[0];
        assert_eq!(func.results.len(), 5);
        assert!(func
            .results
            .iter()
            .all(|(_, r)| matches!(r, VerificationResult::Proved { .. })));
    }

    #[test]
    fn test_with_llm_constructor() {
        // Verify that with_llm compiles and the phase is usable.
        let phase = ProductionStrengthenPhase::with_llm(
            StrengthenConfig {
                use_llm: true,
                ..Default::default()
            },
            Box::new(NoOpLlm),
        );
        let v_out = test_verify_output(1, 1);
        let result = phase.strengthen(&PathBuf::from("/tmp/test.rs"), &v_out);
        // Just verify it runs without panicking
        assert_eq!(result.failures_analyzed, 1);
    }
}
