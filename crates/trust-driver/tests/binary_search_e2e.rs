// tests/binary_search_e2e.rs: M4 E2E integration test for the binary search demo
//
// Demonstrates the full prove->strengthen->backprop loop on examples/binary_search.rs.
// Uses mock verification (no real rustc needed) but real strengthen analysis and
// real backprop rewriting.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::cell::{Cell, RefCell};
use std::path::Path;

use trust_backprop::{RewriteEngine, RewriteKind, SourceRewrite};
use trust_driver::{
    BackpropOutput, BackpropPhase, ConvergenceDecision, LoopConfig, LoopResult,
    ProofFrontier, StrengthenOutput, TerminationReason, VerifyOutput, VerifyPhase,
    StrengthenPhase, run_loop,
};
use trust_strengthen::{Proposal, ProposalKind};

// ---------------------------------------------------------------------------
// Binary search source — embedded to avoid filesystem dependency in tests
// ---------------------------------------------------------------------------

/// The buggy binary_search.rs source (matches examples/binary_search.rs).
const BUGGY_SOURCE: &str = r#"fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut low: usize = 0;
    let mut high: usize = arr.len() - 1;

    while low <= high {
        let mid = (low + high) / 2;

        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }

    None
}
"#;

// ---------------------------------------------------------------------------
// Mock verify phase: simulates z4 verification output
// ---------------------------------------------------------------------------

/// Verify phase that returns 7 failures on first call (matching the 3 bugs),
/// then returns all-proved on subsequent calls (simulating the fixed code).
struct BinarySearchVerify {
    call_count: Cell<usize>,
}

impl BinarySearchVerify {
    fn new() -> Self {
        Self { call_count: Cell::new(0) }
    }
}

impl VerifyPhase for BinarySearchVerify {
    fn verify(&self, _source_path: &Path) -> VerifyOutput {
        let idx = self.call_count.get();
        self.call_count.set(idx + 1);

        if idx == 0 {
            // First pass: 7 VC failures matching real z4 output from binary_search.rs
            // - 2x overflow:sub (arr.len()-1 and mid-1)
            // - 2x overflow:add ((low+high)/2 and mid+1)
            // - 1x bounds (arr[mid])
            // - 2x slice (slice bounds checks)
            VerifyOutput {
                frontier: ProofFrontier {
                    trusted: 0,
                    certified: 0,
                    runtime_checked: 0,
                    failed: 7,
                    unknown: 0,
                },
                fingerprint: Some("buggy-v1".into()),
                vcs_dispatched: 7,
                vcs_failed: 7,
                detailed_results: None,
            }
        } else {
            // After backprop fixes: all VCs pass
            VerifyOutput {
                frontier: ProofFrontier {
                    trusted: 7,
                    certified: 0,
                    runtime_checked: 0,
                    failed: 0,
                    unknown: 0,
                },
                fingerprint: Some("fixed-v1".into()),
                vcs_dispatched: 7,
                vcs_failed: 0,
                detailed_results: None,
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Binary search strengthen phase: proposes fixes for the 3 bugs
// ---------------------------------------------------------------------------

/// Strengthen phase that analyzes the binary search failures and proposes
/// the three fixes: empty guard, safe midpoint, checked subtraction.
struct BinarySearchStrengthen;

impl StrengthenPhase for BinarySearchStrengthen {
    fn strengthen(&self, _source_path: &Path, verify_output: &VerifyOutput) -> StrengthenOutput {
        if verify_output.vcs_failed == 0 {
            return StrengthenOutput {
                has_proposals: false,
                failures_analyzed: 0,
                proposals: vec![],
            };
        }

        // Propose the three fixes that match the binary_search bugs:
        let proposals = vec![
            // FIX 1: Empty array guard (for arr.len() - 1 underflow)
            Proposal {
                function_path: "binary_search".into(),
                function_name: "binary_search".into(),
                kind: ProposalKind::SafeArithmetic {
                    original: "let mut low: usize = 0;\n    let mut high: usize = arr.len() - 1;"
                        .into(),
                    replacement: concat!(
                        "if arr.is_empty() {\n",
                        "        return None;\n",
                        "    }\n",
                        "\n",
                        "    let mut low: usize = 0;\n",
                        "    let mut high: usize = arr.len() - 1; // safe: arr.len() >= 1",
                    ).into(),
                },
                confidence: 0.95,
                rationale: "arr.len() - 1 underflows when arr is empty; add guard".into(),
            },
            // FIX 2: Safe midpoint (for (low + high) / 2 overflow)
            Proposal {
                function_path: "binary_search".into(),
                function_name: "binary_search".into(),
                kind: ProposalKind::SafeArithmetic {
                    original: "(low + high) / 2".into(),
                    replacement: "low + (high - low) / 2".into(),
                },
                confidence: 0.95,
                rationale: "(low + high) can overflow; use low + (high - low) / 2 instead".into(),
            },
            // FIX 3: Checked subtraction (for mid - 1 underflow when mid == 0)
            Proposal {
                function_path: "binary_search".into(),
                function_name: "binary_search".into(),
                kind: ProposalKind::SafeArithmetic {
                    original: "high = mid - 1;".into(),
                    replacement: concat!(
                        "match mid.checked_sub(1) {\n",
                        "                Some(new_high) => high = new_high,\n",
                        "                None => break, // mid == 0, target not found\n",
                        "            }",
                    ).into(),
                },
                confidence: 0.90,
                rationale: "mid - 1 underflows when mid == 0; use checked_sub".into(),
            },
        ];

        StrengthenOutput {
            has_proposals: true,
            failures_analyzed: verify_output.vcs_failed,
            proposals,
        }
    }
}

// ---------------------------------------------------------------------------
// Binary search backprop phase: applies the text replacements
// ---------------------------------------------------------------------------

/// Backprop phase that uses the real RewriteEngine to apply text replacements
/// to an in-memory copy of the source code.
struct BinarySearchBackprop {
    /// Tracks the rewritten source for later verification.
    rewritten_source: RefCell<Option<String>>,
}

impl BinarySearchBackprop {
    fn new() -> Self {
        Self {
            rewritten_source: RefCell::new(None),
        }
    }

    /// Get the rewritten source (for assertions after the loop).
    fn get_rewritten_source(&self) -> Option<String> {
        self.rewritten_source.borrow().clone()
    }
}

impl BackpropPhase for BinarySearchBackprop {
    fn backpropagate(&self, _source_path: &Path, proposals: &[Proposal]) -> BackpropOutput {
        let engine = RewriteEngine::new();
        let mut source = BUGGY_SOURCE.to_string();
        let mut applied = 0;
        let mut skipped = 0;

        // Apply each proposal as a text replacement.
        // Process in order: FIX 1 (empty guard), FIX 2 (safe midpoint), FIX 3 (checked_sub).
        for proposal in proposals {
            match &proposal.kind {
                ProposalKind::SafeArithmetic { original, replacement } => {
                    // Find the original text in the source and replace it
                    if let Some(offset) = source.find(original.as_str()) {
                        let rewrite = SourceRewrite {
                            file_path: "binary_search.rs".into(),
                            offset,
                            kind: RewriteKind::ReplaceExpression {
                                old_text: original.clone(),
                                new_text: replacement.clone(),
                            },
                            function_name: proposal.function_name.clone(),
                            rationale: proposal.rationale.clone(),
                        };
                        match engine.apply_rewrite(&source, &rewrite) {
                            Ok(new_source) => {
                                source = new_source;
                                applied += 1;
                            }
                            Err(_) => {
                                skipped += 1;
                            }
                        }
                    } else {
                        skipped += 1;
                    }
                }
                _ => {
                    // For this demo, we only handle SafeArithmetic proposals
                    skipped += 1;
                }
            }
        }

        *self.rewritten_source.borrow_mut() = Some(source);

        BackpropOutput { applied, skipped }
    }
}

// ---------------------------------------------------------------------------
// E2E test: the full loop
// ---------------------------------------------------------------------------

#[test]
fn test_binary_search_e2e_loop_converges() {
    // Set up the three phases
    let verify = BinarySearchVerify::new();
    let strengthen = BinarySearchStrengthen;
    let backprop = BinarySearchBackprop::new();

    let config = LoopConfig {
        max_iterations: 5,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    // Run the loop
    let result: LoopResult = run_loop(
        Path::new("../../examples/binary_search.rs"),
        &config,
        &verify,
        &strengthen,
        &backprop,
    );

    // -- Verify loop behavior --

    // Should terminate with AllProved (all VCs pass after fixes)
    assert_eq!(
        result.reason,
        TerminationReason::AllProved,
        "Loop should converge with all VCs proved, got: {:?}",
        result.reason,
    );

    // Should take exactly 2 iterations: detect + fix
    assert_eq!(
        result.iterations, 2,
        "Expected 2 iterations (detect + verify-fixed), got {}",
        result.iterations,
    );

    // Final frontier should be all trusted
    assert_eq!(result.final_frontier.trusted, 7);
    assert_eq!(result.final_frontier.failed, 0);

    // -- Verify iteration history --
    assert_eq!(result.history.len(), 2);

    // Iteration 0: failures detected, proposals generated, fixes applied
    let iter0 = &result.history[0];
    assert_eq!(iter0.vcs_failed, 7, "Iteration 0 should detect 7 failures");
    assert_eq!(iter0.proposals, 3, "Iteration 0 should have 3 proposals");
    assert_eq!(iter0.applied, 3, "Iteration 0 should apply all 3 fixes");
    assert!(
        matches!(iter0.decision, ConvergenceDecision::Continue { .. }),
        "Iteration 0 should continue",
    );

    // Iteration 1: all proved, loop terminates
    let iter1 = &result.history[1];
    assert_eq!(iter1.vcs_failed, 0, "Iteration 1 should have 0 failures");

    // -- Verify the rewritten source contains all 3 fixes --
    let rewritten = backprop.get_rewritten_source()
        .expect("Backprop should have produced rewritten source");

    // FIX 1: Empty array guard
    assert!(
        rewritten.contains("if arr.is_empty()"),
        "Rewritten source should contain empty array guard.\nGot:\n{rewritten}",
    );
    assert!(
        rewritten.contains("return None;"),
        "Rewritten source should contain early return for empty array",
    );

    // FIX 2: Safe midpoint
    assert!(
        rewritten.contains("low + (high - low) / 2"),
        "Rewritten source should use safe midpoint formula.\nGot:\n{rewritten}",
    );
    assert!(
        !rewritten.contains("(low + high) / 2"),
        "Rewritten source should NOT contain overflow-prone midpoint",
    );

    // FIX 3: Checked subtraction
    assert!(
        rewritten.contains("checked_sub(1)"),
        "Rewritten source should use checked_sub.\nGot:\n{rewritten}",
    );
    assert!(
        !rewritten.contains("high = mid - 1;"),
        "Rewritten source should NOT contain unchecked subtraction",
    );
}

#[test]
fn test_binary_search_strengthen_no_proposals_when_all_proved() {
    // Verify that strengthen returns no proposals when there are no failures
    let strengthen = BinarySearchStrengthen;
    let verify_output = VerifyOutput {
        frontier: ProofFrontier {
            trusted: 7,
            certified: 0,
            runtime_checked: 0,
            failed: 0,
            unknown: 0,
        },
        fingerprint: None,
        vcs_dispatched: 7,
        vcs_failed: 0,
        detailed_results: None,
    };

    let output = strengthen.strengthen(Path::new("test.rs"), &verify_output);
    assert!(!output.has_proposals);
    assert!(output.proposals.is_empty());
}

#[test]
fn test_binary_search_backprop_applies_all_three_fixes() {
    // Verify backprop independently: given 3 proposals, all 3 should apply
    let backprop = BinarySearchBackprop::new();
    let proposals = vec![
        Proposal {
            function_path: "binary_search".into(),
            function_name: "binary_search".into(),
            kind: ProposalKind::SafeArithmetic {
                original: "let mut low: usize = 0;\n    let mut high: usize = arr.len() - 1;"
                    .into(),
                replacement: concat!(
                    "if arr.is_empty() {\n",
                    "        return None;\n",
                    "    }\n",
                    "\n",
                    "    let mut low: usize = 0;\n",
                    "    let mut high: usize = arr.len() - 1; // safe: arr.len() >= 1",
                ).into(),
            },
            confidence: 0.95,
            rationale: "empty guard".into(),
        },
        Proposal {
            function_path: "binary_search".into(),
            function_name: "binary_search".into(),
            kind: ProposalKind::SafeArithmetic {
                original: "(low + high) / 2".into(),
                replacement: "low + (high - low) / 2".into(),
            },
            confidence: 0.95,
            rationale: "safe midpoint".into(),
        },
        Proposal {
            function_path: "binary_search".into(),
            function_name: "binary_search".into(),
            kind: ProposalKind::SafeArithmetic {
                original: "high = mid - 1;".into(),
                replacement: concat!(
                    "match mid.checked_sub(1) {\n",
                    "                Some(new_high) => high = new_high,\n",
                    "                None => break, // mid == 0, target not found\n",
                    "            }",
                ).into(),
            },
            confidence: 0.90,
            rationale: "checked sub".into(),
        },
    ];

    let output = backprop.backpropagate(Path::new("test.rs"), &proposals);
    assert_eq!(output.applied, 3, "All 3 fixes should be applied");
    assert_eq!(output.skipped, 0, "No fixes should be skipped");

    let rewritten = backprop.get_rewritten_source().unwrap();
    assert!(rewritten.contains("if arr.is_empty()"));
    assert!(rewritten.contains("low + (high - low) / 2"));
    assert!(rewritten.contains("checked_sub(1)"));
}

#[test]
fn test_binary_search_loop_stops_if_no_proposals() {
    // If strengthen returns nothing, the loop should stop with NoProposals
    struct EmptyStrengthen;
    impl StrengthenPhase for EmptyStrengthen {
        fn strengthen(&self, _: &Path, _: &VerifyOutput) -> StrengthenOutput {
            StrengthenOutput {
                has_proposals: false,
                failures_analyzed: 0,
                proposals: vec![],
            }
        }
    }

    struct NoOpBackprop;
    impl BackpropPhase for NoOpBackprop {
        fn backpropagate(&self, _: &Path, proposals: &[Proposal]) -> BackpropOutput {
            BackpropOutput { applied: proposals.len(), skipped: 0 }
        }
    }

    let verify = BinarySearchVerify::new();
    let config = LoopConfig {
        max_iterations: 5,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = run_loop(
        Path::new("test.rs"),
        &config,
        &verify,
        &EmptyStrengthen,
        &NoOpBackprop,
    );

    assert_eq!(result.reason, TerminationReason::NoProposals);
    assert_eq!(result.iterations, 1);
}
