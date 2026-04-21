// trust-debug/diff_diagnosis.rs: Differential diagnosis for proof regressions
//
// Identifies why a previously-passing proof now fails by comparing VC sets,
// analyzing code/spec changes, detecting solver divergence, and suggesting fixes.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::{SourceSpan, VcKind, VerificationCondition, VerificationResult};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A proof regression: a function that previously proved now fails.
#[derive(Debug, Clone)]
pub(crate) struct ProofRegression {
    /// Fully qualified function name.
    pub function: String,
    /// The result from the previous (passing) run.
    pub old_result: VerificationResult,
    /// The result from the current (failing) run.
    pub new_result: VerificationResult,
    /// VCs from the previous run.
    pub old_vcs: Vec<VerificationCondition>,
    /// VCs from the current run.
    pub new_vcs: Vec<VerificationCondition>,
    /// Source location of the function.
    pub location: SourceSpan,
}

/// Possible causes for a proof regression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum RegressionCause {
    /// The function's implementation changed.
    CodeChange {
        /// Description of what changed (e.g. "new basic block added").
        description: String,
    },
    /// The specification (pre/postconditions) changed.
    SpecChange {
        /// Description of the spec change.
        description: String,
    },
    /// The solver produced a different result on equivalent VCs.
    SolverDivergence {
        /// Which solver diverged.
        solver: String,
    },
    /// A dependency (callee) changed its contract or implementation.
    DependencyChange {
        /// The callee whose change caused the regression.
        callee: String,
    },
    /// The solver timed out (previously completed within budget).
    Timeout {
        /// Solver that timed out.
        solver: String,
        /// Timeout budget in milliseconds.
        timeout_ms: u64,
    },
}

/// A ranked cause with supporting evidence.
#[derive(Debug, Clone)]
pub(crate) struct RankedCause {
    /// The cause.
    pub cause: RegressionCause,
    /// Confidence score in [0.0, 1.0].
    pub confidence: f64,
    /// Evidence strings supporting this diagnosis.
    pub evidence: Vec<String>,
}

// f64 fields prevent Eq -- only derive PartialEq.
impl PartialEq for RankedCause {
    fn eq(&self, other: &Self) -> bool {
        self.cause == other.cause
            && self.confidence == other.confidence
            && self.evidence == other.evidence
    }
}

/// Full diagnosis report for a proof regression.
#[derive(Debug, Clone)]
pub(crate) struct DiagnosisReport {
    /// The function that regressed.
    pub function: String,
    /// Ranked list of probable causes (highest confidence first).
    pub causes: Vec<RankedCause>,
    /// Suggested remediation steps.
    pub suggestions: Vec<String>,
    /// Summary of VC differences between old and new runs.
    pub vc_diff: VcDiff,
}

/// Differences between two sets of VCs.
///
/// Stores VC kind descriptions as strings because `VcKind` does not implement
/// `PartialEq` (it contains `Ty` and other non-comparable types).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct VcDiff {
    /// Descriptions of VCs present in old but not in new (removed).
    pub removed: Vec<String>,
    /// Descriptions of VCs present in new but not in old (added).
    pub added: Vec<String>,
    /// Descriptions of VCs present in both but with changed formulas.
    pub changed: Vec<String>,
    /// Count of VCs identical in both runs.
    pub unchanged: usize,
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Diagnose a proof regression, producing a ranked report of causes and fixes.
#[must_use]
pub(crate) fn diagnose_regression(regression: &ProofRegression) -> DiagnosisReport {
    let vc_diff = compare_vc_sets(&regression.old_vcs, &regression.new_vcs);
    let cause = identify_cause(regression, &vc_diff);
    let suggestions = suggest_fix(&cause);

    DiagnosisReport {
        function: regression.function.clone(),
        causes: cause,
        suggestions,
        vc_diff,
    }
}

/// Compare two VC sets and produce a diff of what changed.
#[must_use]
pub(crate) fn compare_vc_sets(old: &[VerificationCondition], new: &[VerificationCondition]) -> VcDiff {
    let old_map = vc_fingerprints(old);
    let new_map = vc_fingerprints(new);

    let old_keys: FxHashSet<&String> = old_map.keys().collect();
    let new_keys: FxHashSet<&String> = new_map.keys().collect();

    let removed: Vec<String> = old_keys
        .difference(&new_keys)
        .filter_map(|k| old_map.get(*k).map(|vc| vc.kind.description()))
        .collect();

    let added: Vec<String> = new_keys
        .difference(&old_keys)
        .filter_map(|k| new_map.get(*k).map(|vc| vc.kind.description()))
        .collect();

    let common_keys: FxHashSet<&String> = old_keys.intersection(&new_keys).copied().collect();

    let mut changed = Vec::new();
    let mut unchanged = 0usize;

    for key in &common_keys {
        let old_vc = &old_map[*key];
        let new_vc = &new_map[*key];
        // Compare formula string representation as a proxy for structural equality.
        if format!("{:?}", old_vc.formula) != format!("{:?}", new_vc.formula) {
            changed.push(new_vc.kind.description());
        } else {
            unchanged += 1;
        }
    }

    VcDiff { removed, added, changed, unchanged }
}

/// Identify the most likely causes of a regression given the VC diff.
#[must_use]
pub(crate) fn identify_cause(regression: &ProofRegression, vc_diff: &VcDiff) -> Vec<RankedCause> {
    let mut causes = Vec::new();

    // Check for timeout.
    if let VerificationResult::Timeout { solver, timeout_ms } = &regression.new_result {
        causes.push(RankedCause {
            cause: RegressionCause::Timeout {
                solver: solver.clone(),
                timeout_ms: *timeout_ms,
            },
            confidence: 0.9,
            evidence: vec![format!(
                "New result is Timeout ({}ms) from solver '{}'",
                timeout_ms, solver
            )],
        });
    }

    // Check for VC structural changes (implies code change).
    if !vc_diff.added.is_empty() || !vc_diff.removed.is_empty() {
        let mut evidence = Vec::new();
        if !vc_diff.added.is_empty() {
            evidence.push(format!("{} new VCs added", vc_diff.added.len()));
        }
        if !vc_diff.removed.is_empty() {
            evidence.push(format!("{} VCs removed", vc_diff.removed.len()));
        }
        causes.push(RankedCause {
            cause: RegressionCause::CodeChange {
                description: format!(
                    "{} VCs added, {} removed",
                    vc_diff.added.len(),
                    vc_diff.removed.len()
                ),
            },
            confidence: 0.8,
            evidence,
        });
    }

    // Check for formula changes on same VC kinds (implies spec or code change).
    if !vc_diff.changed.is_empty() {
        let has_contract_vc = vc_diff.changed.iter().any(|desc| {
            desc.contains("precondition") || desc.contains("postcondition")
        });

        if has_contract_vc {
            causes.push(RankedCause {
                cause: RegressionCause::SpecChange {
                    description: format!(
                        "{} contract VCs changed",
                        vc_diff.changed.len()
                    ),
                },
                confidence: 0.85,
                evidence: vec![format!(
                    "{} VCs have changed formulas, including contract VCs",
                    vc_diff.changed.len()
                )],
            });
        } else {
            causes.push(RankedCause {
                cause: RegressionCause::CodeChange {
                    description: format!("{} VC formulas changed", vc_diff.changed.len()),
                },
                confidence: 0.7,
                evidence: vec![format!(
                    "{} VCs have changed formulas (no contract VCs)",
                    vc_diff.changed.len()
                )],
            });
        }
    }

    // Check for dependency changes: look for Precondition VCs referencing callees.
    let old_callees = extract_callees(&regression.old_vcs);
    let new_callees = extract_callees(&regression.new_vcs);
    let new_only: Vec<&String> = new_callees.difference(&old_callees).collect();
    let removed_only: Vec<&String> = old_callees.difference(&new_callees).collect();

    if !new_only.is_empty() || !removed_only.is_empty() {
        for callee in &new_only {
            causes.push(RankedCause {
                cause: RegressionCause::DependencyChange {
                    callee: callee.to_string(),
                },
                confidence: 0.6,
                evidence: vec![format!("New precondition VC for callee '{}'", callee)],
            });
        }
        for callee in &removed_only {
            causes.push(RankedCause {
                cause: RegressionCause::DependencyChange {
                    callee: callee.to_string(),
                },
                confidence: 0.5,
                evidence: vec![format!("Removed precondition VC for callee '{}'", callee)],
            });
        }
    }

    // Check for solver divergence: same VCs, different result.
    if vc_diff.added.is_empty()
        && vc_diff.removed.is_empty()
        && vc_diff.changed.is_empty()
        && vc_diff.unchanged > 0
    {
        let solver_name = match &regression.new_result {
            VerificationResult::Failed { solver, .. }
            | VerificationResult::Unknown { solver, .. }
            | VerificationResult::Timeout { solver, .. }
            | VerificationResult::Proved { solver, .. } => solver.clone(),
            _ => "unknown".to_string(),
        };
        causes.push(RankedCause {
            cause: RegressionCause::SolverDivergence {
                solver: solver_name.clone(),
            },
            confidence: 0.95,
            evidence: vec![
                "All VCs are structurally identical between runs".to_string(),
                format!("Solver '{}' returned different result", solver_name),
            ],
        });
    }

    // Sort by confidence descending.
    causes.sort_by(|a, b| {
        b.confidence
            .partial_cmp(&a.confidence)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    causes
}

/// Suggest remediation steps for the ranked causes.
#[must_use]
pub(crate) fn suggest_fix(causes: &[RankedCause]) -> Vec<String> {
    let mut suggestions = Vec::new();

    for ranked in causes {
        match &ranked.cause {
            RegressionCause::CodeChange { description } => {
                suggestions.push(format!(
                    "Review code change: {}. Check git diff for the function.",
                    description
                ));
                suggestions.push(
                    "Run `git log -p -- <file>` to identify the commit that changed the function."
                        .to_string(),
                );
            }
            RegressionCause::SpecChange { description } => {
                suggestions.push(format!(
                    "Review spec change: {}. Verify the new spec is satisfiable.",
                    description
                ));
                suggestions.push(
                    "Check if the postcondition is too strong or the precondition too weak."
                        .to_string(),
                );
            }
            RegressionCause::SolverDivergence { solver } => {
                suggestions.push(format!(
                    "Solver '{}' diverged on identical VCs. Try a different backend.",
                    solver
                ));
                suggestions.push(
                    "Run differential testing to confirm the divergence.".to_string(),
                );
            }
            RegressionCause::DependencyChange { callee } => {
                suggestions.push(format!(
                    "Dependency '{}' changed. Check its contract for breaking changes.",
                    callee
                ));
                suggestions.push(format!(
                    "Run `cargo trust verify -- {}` to re-verify the dependency.",
                    callee
                ));
            }
            RegressionCause::Timeout { solver, timeout_ms } => {
                suggestions.push(format!(
                    "Solver '{}' timed out at {}ms. Try increasing the timeout or simplifying the VC.",
                    solver, timeout_ms
                ));
                suggestions.push(
                    "Check if a code change introduced non-linear arithmetic or quantifiers."
                        .to_string(),
                );
            }
        }
    }

    suggestions.dedup();
    suggestions
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a fingerprint map: key = "function::kind_description", value = VC.
fn vc_fingerprints(vcs: &[VerificationCondition]) -> FxHashMap<String, &VerificationCondition> {
    let mut map = FxHashMap::default();
    for vc in vcs {
        let key = format!("{}::{}", vc.function, vc.kind.description());
        map.insert(key, vc);
    }
    map
}

/// Extract callee names from Precondition VCs.
fn extract_callees(vcs: &[VerificationCondition]) -> FxHashSet<String> {
    let mut callees = FxHashSet::default();
    for vc in vcs {
        if let VcKind::Precondition { callee } = &vc.kind {
            callees.insert(callee.clone());
        }
    }
    callees
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::*;

    fn make_vc(function: &str, kind: VcKind, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: function.to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "z4".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
    }

    fn failed_result() -> VerificationResult {
        VerificationResult::Failed {
            solver: "z4".to_string(),
            time_ms: 15,
            counterexample: None,
        }
    }

    fn timeout_result() -> VerificationResult {
        VerificationResult::Timeout {
            solver: "z4".to_string(),
            timeout_ms: 5000,
        }
    }

    fn sample_regression() -> ProofRegression {
        let old_vc = make_vc(
            "test::add",
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            Formula::Bool(true),
        );
        let new_vc = make_vc(
            "test::add",
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            Formula::Bool(false),
        );
        ProofRegression {
            function: "test::add".to_string(),
            old_result: proved_result(),
            new_result: failed_result(),
            old_vcs: vec![old_vc],
            new_vcs: vec![new_vc],
            location: SourceSpan::default(),
        }
    }

    // --- Test 1: diagnose_regression returns a report ---
    #[test]
    fn test_diagnose_regression_returns_report() {
        let regression = sample_regression();
        let report = diagnose_regression(&regression);

        assert_eq!(report.function, "test::add");
        assert!(!report.causes.is_empty(), "should identify at least one cause");
        assert!(!report.suggestions.is_empty(), "should suggest at least one fix");
    }

    // --- Test 2: compare_vc_sets detects added VCs ---
    #[test]
    fn test_compare_vc_sets_added() {
        let old: Vec<VerificationCondition> = vec![];
        let new = vec![make_vc(
            "test::f",
            VcKind::DivisionByZero,
            Formula::Bool(true),
        )];

        let diff = compare_vc_sets(&old, &new);
        assert_eq!(diff.added.len(), 1);
        assert_eq!(diff.removed.len(), 0);
        assert_eq!(diff.unchanged, 0);
    }

    // --- Test 3: compare_vc_sets detects removed VCs ---
    #[test]
    fn test_compare_vc_sets_removed() {
        let old = vec![make_vc(
            "test::f",
            VcKind::DivisionByZero,
            Formula::Bool(true),
        )];
        let new: Vec<VerificationCondition> = vec![];

        let diff = compare_vc_sets(&old, &new);
        assert_eq!(diff.removed.len(), 1);
        assert_eq!(diff.added.len(), 0);
    }

    // --- Test 4: compare_vc_sets detects changed formulas ---
    #[test]
    fn test_compare_vc_sets_changed() {
        let old = vec![make_vc(
            "test::f",
            VcKind::DivisionByZero,
            Formula::Bool(true),
        )];
        let new = vec![make_vc(
            "test::f",
            VcKind::DivisionByZero,
            Formula::Bool(false),
        )];

        let diff = compare_vc_sets(&old, &new);
        assert_eq!(diff.changed.len(), 1);
        assert_eq!(diff.unchanged, 0);
    }

    // --- Test 5: compare_vc_sets detects unchanged VCs ---
    #[test]
    fn test_compare_vc_sets_unchanged() {
        let vc = make_vc("test::f", VcKind::DivisionByZero, Formula::Bool(true));
        let old = vec![vc.clone()];
        let new = vec![vc];

        let diff = compare_vc_sets(&old, &new);
        assert_eq!(diff.unchanged, 1);
        assert_eq!(diff.added.len(), 0);
        assert_eq!(diff.removed.len(), 0);
        assert_eq!(diff.changed.len(), 0);
    }

    // --- Test 6: identify_cause detects timeout ---
    #[test]
    fn test_identify_cause_timeout() {
        let regression = ProofRegression {
            function: "test::slow".to_string(),
            old_result: proved_result(),
            new_result: timeout_result(),
            old_vcs: vec![make_vc(
                "test::slow",
                VcKind::DivisionByZero,
                Formula::Bool(true),
            )],
            new_vcs: vec![make_vc(
                "test::slow",
                VcKind::DivisionByZero,
                Formula::Bool(true),
            )],
            location: SourceSpan::default(),
        };
        let diff = compare_vc_sets(&regression.old_vcs, &regression.new_vcs);
        let causes = identify_cause(&regression, &diff);

        assert!(
            causes.iter().any(|c| matches!(&c.cause, RegressionCause::Timeout { .. })),
            "should identify timeout cause"
        );
    }

    // --- Test 7: identify_cause detects solver divergence ---
    #[test]
    fn test_identify_cause_solver_divergence() {
        let vc = make_vc("test::f", VcKind::DivisionByZero, Formula::Bool(true));
        let regression = ProofRegression {
            function: "test::f".to_string(),
            old_result: proved_result(),
            new_result: failed_result(),
            old_vcs: vec![vc.clone()],
            new_vcs: vec![vc],
            location: SourceSpan::default(),
        };
        let diff = compare_vc_sets(&regression.old_vcs, &regression.new_vcs);
        let causes = identify_cause(&regression, &diff);

        assert!(
            causes
                .iter()
                .any(|c| matches!(&c.cause, RegressionCause::SolverDivergence { .. })),
            "should identify solver divergence when VCs are identical"
        );
    }

    // --- Test 8: identify_cause detects code change ---
    #[test]
    fn test_identify_cause_code_change() {
        let old_vc = make_vc("test::f", VcKind::DivisionByZero, Formula::Bool(true));
        let new_vc = make_vc(
            "test::f",
            VcKind::IndexOutOfBounds,
            Formula::Bool(true),
        );
        let regression = ProofRegression {
            function: "test::f".to_string(),
            old_result: proved_result(),
            new_result: failed_result(),
            old_vcs: vec![old_vc],
            new_vcs: vec![new_vc],
            location: SourceSpan::default(),
        };
        let diff = compare_vc_sets(&regression.old_vcs, &regression.new_vcs);
        let causes = identify_cause(&regression, &diff);

        assert!(
            causes
                .iter()
                .any(|c| matches!(&c.cause, RegressionCause::CodeChange { .. })),
            "should identify code change when VCs differ structurally"
        );
    }

    // --- Test 9: identify_cause detects spec change ---
    #[test]
    fn test_identify_cause_spec_change() {
        let old_vc = make_vc(
            "test::f",
            VcKind::Postcondition,
            Formula::Bool(true),
        );
        let new_vc = make_vc(
            "test::f",
            VcKind::Postcondition,
            Formula::Bool(false),
        );
        let regression = ProofRegression {
            function: "test::f".to_string(),
            old_result: proved_result(),
            new_result: failed_result(),
            old_vcs: vec![old_vc],
            new_vcs: vec![new_vc],
            location: SourceSpan::default(),
        };
        let diff = compare_vc_sets(&regression.old_vcs, &regression.new_vcs);
        let causes = identify_cause(&regression, &diff);

        assert!(
            causes
                .iter()
                .any(|c| matches!(&c.cause, RegressionCause::SpecChange { .. })),
            "should identify spec change when contract VCs change"
        );
    }

    // --- Test 10: identify_cause detects dependency change ---
    #[test]
    fn test_identify_cause_dependency_change() {
        let old_vc = make_vc(
            "test::f",
            VcKind::Precondition { callee: "dep::old_fn".to_string() },
            Formula::Bool(true),
        );
        let new_vc = make_vc(
            "test::f",
            VcKind::Precondition { callee: "dep::new_fn".to_string() },
            Formula::Bool(true),
        );
        let regression = ProofRegression {
            function: "test::f".to_string(),
            old_result: proved_result(),
            new_result: failed_result(),
            old_vcs: vec![old_vc],
            new_vcs: vec![new_vc],
            location: SourceSpan::default(),
        };
        let diff = compare_vc_sets(&regression.old_vcs, &regression.new_vcs);
        let causes = identify_cause(&regression, &diff);

        assert!(
            causes
                .iter()
                .any(|c| matches!(&c.cause, RegressionCause::DependencyChange { .. })),
            "should identify dependency change when callee VCs differ"
        );
    }

    // --- Test 11: suggest_fix produces suggestions for each cause type ---
    #[test]
    fn test_suggest_fix_all_cause_types() {
        let causes = vec![
            RankedCause {
                cause: RegressionCause::CodeChange {
                    description: "new block".to_string(),
                },
                confidence: 0.8,
                evidence: vec![],
            },
            RankedCause {
                cause: RegressionCause::SpecChange {
                    description: "postcondition changed".to_string(),
                },
                confidence: 0.7,
                evidence: vec![],
            },
            RankedCause {
                cause: RegressionCause::SolverDivergence {
                    solver: "z4".to_string(),
                },
                confidence: 0.6,
                evidence: vec![],
            },
            RankedCause {
                cause: RegressionCause::DependencyChange {
                    callee: "dep::f".to_string(),
                },
                confidence: 0.5,
                evidence: vec![],
            },
            RankedCause {
                cause: RegressionCause::Timeout {
                    solver: "z4".to_string(),
                    timeout_ms: 5000,
                },
                confidence: 0.4,
                evidence: vec![],
            },
        ];

        let suggestions = suggest_fix(&causes);
        assert!(
            suggestions.len() >= 5,
            "should produce suggestions for each cause: got {}",
            suggestions.len()
        );
    }

    // --- Test 12: causes sorted by confidence descending ---
    #[test]
    fn test_causes_sorted_by_confidence() {
        let regression = ProofRegression {
            function: "test::f".to_string(),
            old_result: proved_result(),
            new_result: timeout_result(),
            old_vcs: vec![make_vc(
                "test::f",
                VcKind::DivisionByZero,
                Formula::Bool(true),
            )],
            new_vcs: vec![
                make_vc("test::f", VcKind::DivisionByZero, Formula::Bool(true)),
                make_vc("test::f", VcKind::IndexOutOfBounds, Formula::Bool(true)),
            ],
            location: SourceSpan::default(),
        };
        let report = diagnose_regression(&regression);

        for window in report.causes.windows(2) {
            assert!(
                window[0].confidence >= window[1].confidence,
                "causes should be sorted by confidence descending: {} < {}",
                window[0].confidence,
                window[1].confidence,
            );
        }
    }

    // --- Test 13: empty VCs produce empty diff ---
    #[test]
    fn test_compare_vc_sets_both_empty() {
        let diff = compare_vc_sets(&[], &[]);
        assert_eq!(diff.added.len(), 0);
        assert_eq!(diff.removed.len(), 0);
        assert_eq!(diff.changed.len(), 0);
        assert_eq!(diff.unchanged, 0);
    }

    // --- Test 14: suggest_fix returns empty for no causes ---
    #[test]
    fn test_suggest_fix_empty_causes() {
        let suggestions = suggest_fix(&[]);
        assert!(suggestions.is_empty());
    }
}
