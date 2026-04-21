// trust-debug/differential.rs: Differential testing across verification backends
//
// Compares results from multiple backends on the same VC to find disagreements.
// A disagreement (one backend proves, another refutes) indicates either a
// backend bug or a VC at the boundary of decidability.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_router::VerificationBackend;
use trust_types::{VerificationCondition, VerificationResult};

/// A disagreement between two backends on the same VC.
#[derive(Debug, Clone)]
pub(crate) struct Disagreement {
    /// The VC that produced a disagreement.
    pub vc: VerificationCondition,
    /// Name of the first backend.
    pub backend_a: String,
    /// Result from the first backend.
    pub result_a: VerificationResult,
    /// Name of the second backend.
    pub backend_b: String,
    /// Result from the second backend.
    pub result_b: VerificationResult,
}

/// Summary of differential testing across backends.
#[derive(Debug, Clone)]
pub(crate) struct DiffResult {
    /// Number of VCs where all backends agree.
    pub agreements: usize,
    /// Number of VCs where at least two backends disagree.
    pub disagreements: usize,
    /// Number of VCs where at least one backend timed out.
    pub timeouts: usize,
    /// All disagreements found.
    pub disagreement_details: Vec<Disagreement>,
}

/// Differential tester: runs the same VCs through multiple backends and
/// reports where they disagree.
pub(crate) struct DifferentialTester<'a> {
    backends: Vec<&'a dyn VerificationBackend>,
}

impl<'a> DifferentialTester<'a> {
    /// Create a new differential tester with the given backends.
    ///
    /// At least two backends are needed for meaningful comparison.
    pub(crate) fn new(backends: Vec<&'a dyn VerificationBackend>) -> Self {
        Self { backends }
    }

    /// Run all VCs through all backends and report disagreements.
    #[must_use]
    pub(crate) fn test_all(&self, vcs: &[VerificationCondition]) -> DiffResult {
        let mut agreements = 0;
        let mut disagreements = 0;
        let mut timeouts = 0;
        let mut disagreement_details = Vec::new();

        for vc in vcs {
            let results: Vec<(&dyn VerificationBackend, VerificationResult)> = self
                .backends
                .iter()
                .map(|b| (*b, b.verify(vc)))
                .collect();

            let has_timeout = results.iter().any(|(_, r)| matches!(r, VerificationResult::Timeout { .. }));
            if has_timeout {
                timeouts += 1;
            }

            let vc_disagreements = find_disagreements_in_results(vc, &results);
            if vc_disagreements.is_empty() {
                agreements += 1;
            } else {
                disagreements += 1;
                disagreement_details.extend(vc_disagreements);
            }
        }

        DiffResult {
            agreements,
            disagreements,
            timeouts,
            disagreement_details,
        }
    }
}

/// Find all disagreements for a single VC given results from multiple backends.
///
/// A disagreement exists when one backend proves and another fails (or vice
/// versa). Unknown/Timeout results are not considered disagreements by
/// themselves, only Proved vs Failed conflicts are flagged.
pub(crate) fn find_disagreements(
    vc: &VerificationCondition,
    backends: &[&dyn VerificationBackend],
) -> Vec<Disagreement> {
    let results: Vec<(&dyn VerificationBackend, VerificationResult)> = backends
        .iter()
        .map(|b| (*b, b.verify(vc)))
        .collect();

    find_disagreements_in_results(vc, &results)
}

/// Internal: compare results pairwise and collect disagreements.
fn find_disagreements_in_results(
    vc: &VerificationCondition,
    results: &[(&dyn VerificationBackend, VerificationResult)],
) -> Vec<Disagreement> {
    let mut disagreements = Vec::new();

    for i in 0..results.len() {
        for j in (i + 1)..results.len() {
            let (backend_a, result_a) = &results[i];
            let (backend_b, result_b) = &results[j];

            if is_proved_vs_failed(result_a, result_b) {
                disagreements.push(Disagreement {
                    vc: vc.clone(),
                    backend_a: backend_a.name().to_string(),
                    result_a: result_a.clone(),
                    backend_b: backend_b.name().to_string(),
                    result_b: result_b.clone(),
                });
            }
        }
    }

    disagreements
}

/// Check whether one result is Proved and the other is Failed.
fn is_proved_vs_failed(a: &VerificationResult, b: &VerificationResult) -> bool {
    (a.is_proved() && b.is_failed()) || (a.is_failed() && b.is_proved())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::*;

    fn sample_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "test::add".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    struct MockBackend {
        name: &'static str,
        result: VerificationResult,
    }

    impl VerificationBackend for MockBackend {
        fn name(&self) -> &str {
            self.name
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            self.result.clone()
        }
    }

    fn proves_backend(name: &'static str) -> MockBackend {
        MockBackend {
            name,
            result: VerificationResult::Proved {
                solver: name.to_string(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, },
        }
    }

    fn fails_backend(name: &'static str) -> MockBackend {
        MockBackend {
            name,
            result: VerificationResult::Failed {
                solver: name.to_string(),
                time_ms: 1,
                counterexample: None,
            },
        }
    }

    fn timeout_backend(name: &'static str) -> MockBackend {
        MockBackend {
            name,
            result: VerificationResult::Timeout {
                solver: name.to_string(),
                timeout_ms: 5000,
            },
        }
    }

    fn unknown_backend(name: &'static str) -> MockBackend {
        MockBackend {
            name,
            result: VerificationResult::Unknown {
                solver: name.to_string(),
                time_ms: 100,
                reason: "inconclusive".to_string(),
            },
        }
    }

    #[test]
    fn test_two_backends_agree_proved() {
        let b1 = proves_backend("z4");
        let b2 = proves_backend("sunder");
        let vcs = vec![sample_vc()];

        let tester = DifferentialTester::new(vec![&b1, &b2]);
        let result = tester.test_all(&vcs);

        assert_eq!(result.agreements, 1);
        assert_eq!(result.disagreements, 0);
        assert!(result.disagreement_details.is_empty());
    }

    #[test]
    fn test_two_backends_agree_failed() {
        let b1 = fails_backend("z4");
        let b2 = fails_backend("sunder");
        let vcs = vec![sample_vc()];

        let tester = DifferentialTester::new(vec![&b1, &b2]);
        let result = tester.test_all(&vcs);

        assert_eq!(result.agreements, 1);
        assert_eq!(result.disagreements, 0);
    }

    #[test]
    fn test_disagreement_proved_vs_failed() {
        let b1 = proves_backend("z4");
        let b2 = fails_backend("sunder");
        let vcs = vec![sample_vc()];

        let tester = DifferentialTester::new(vec![&b1, &b2]);
        let result = tester.test_all(&vcs);

        assert_eq!(result.agreements, 0);
        assert_eq!(result.disagreements, 1);
        assert_eq!(result.disagreement_details.len(), 1);

        let d = &result.disagreement_details[0];
        assert_eq!(d.backend_a, "z4");
        assert_eq!(d.backend_b, "sunder");
        assert!(d.result_a.is_proved());
        assert!(d.result_b.is_failed());
    }

    #[test]
    fn test_timeout_counted_separately() {
        let b1 = proves_backend("z4");
        let b2 = timeout_backend("slow-solver");
        let vcs = vec![sample_vc()];

        let tester = DifferentialTester::new(vec![&b1, &b2]);
        let result = tester.test_all(&vcs);

        assert_eq!(result.timeouts, 1);
        // Timeout vs Proved is NOT a disagreement (timeout is inconclusive)
        assert_eq!(result.disagreements, 0);
        assert_eq!(result.agreements, 1);
    }

    #[test]
    fn test_unknown_not_disagreement() {
        let b1 = proves_backend("z4");
        let b2 = unknown_backend("uncertain");
        let vcs = vec![sample_vc()];

        let tester = DifferentialTester::new(vec![&b1, &b2]);
        let result = tester.test_all(&vcs);

        assert_eq!(result.disagreements, 0);
        assert_eq!(result.agreements, 1);
    }

    #[test]
    fn test_three_backends_one_disagrees() {
        let b1 = proves_backend("z4");
        let b2 = proves_backend("sunder");
        let b3 = fails_backend("zani");
        let vcs = vec![sample_vc()];

        let tester = DifferentialTester::new(vec![&b1, &b2, &b3]);
        let result = tester.test_all(&vcs);

        assert_eq!(result.disagreements, 1);
        // z4 vs zani, sunder vs zani = 2 disagreement pairs
        assert_eq!(result.disagreement_details.len(), 2);
    }

    #[test]
    fn test_multiple_vcs() {
        let b1 = proves_backend("z4");
        let b2 = fails_backend("sunder");
        let vcs = vec![sample_vc(), sample_vc(), sample_vc()];

        let tester = DifferentialTester::new(vec![&b1, &b2]);
        let result = tester.test_all(&vcs);

        assert_eq!(result.agreements, 0);
        assert_eq!(result.disagreements, 3);
        assert_eq!(result.disagreement_details.len(), 3);
    }

    #[test]
    fn test_empty_vcs() {
        let b1 = proves_backend("z4");
        let b2 = fails_backend("sunder");
        let vcs: Vec<VerificationCondition> = vec![];

        let tester = DifferentialTester::new(vec![&b1, &b2]);
        let result = tester.test_all(&vcs);

        assert_eq!(result.agreements, 0);
        assert_eq!(result.disagreements, 0);
        assert_eq!(result.timeouts, 0);
    }

    #[test]
    fn test_find_disagreements_fn() {
        let b1 = proves_backend("z4");
        let b2 = fails_backend("sunder");
        let vc = sample_vc();

        let disagreements = find_disagreements(&vc, &[&b1, &b2]);
        assert_eq!(disagreements.len(), 1);
        assert_eq!(disagreements[0].backend_a, "z4");
        assert_eq!(disagreements[0].backend_b, "sunder");
    }

    #[test]
    fn test_disagreement_captures_vc() {
        let b1 = proves_backend("z4");
        let b2 = fails_backend("sunder");
        let vc = sample_vc();

        let disagreements = find_disagreements(&vc, &[&b1, &b2]);
        assert_eq!(disagreements[0].vc.function, "test::add");
    }

    #[test]
    fn test_single_backend_no_disagreements() {
        let b1 = proves_backend("z4");
        let vc = sample_vc();

        let disagreements = find_disagreements(&vc, &[&b1]);
        assert!(disagreements.is_empty());
    }
}
