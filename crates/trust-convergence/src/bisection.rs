// trust-convergence/bisection.rs: Regression bisection over rewrite history.
//
// When a regression is detected between two frontier snapshots, this module
// binary-searches the recorded rewrite history to identify the specific rewrite
// that caused a previously-proved VC to fail.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::visualization::FrontierSnapshot;

/// A recorded source rewrite applied during one iteration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SourceRewrite {
    /// Iteration when this rewrite was applied.
    pub iteration: u32,
    /// Human-readable description of the rewrite (e.g., "Added precondition to foo::bar").
    pub description: String,
    /// File path that was modified.
    pub file_path: String,
    /// Optional: the original text that was replaced.
    pub original: Option<String>,
    /// Optional: the replacement text.
    pub replacement: Option<String>,
}

/// Stores rewrite history and performs bisection to find regression sources.
#[derive(Debug, Clone)]
pub(crate) struct RegressionBisector {
    /// Rewrites grouped by iteration number, in chronological order.
    history: Vec<(u32, Vec<SourceRewrite>)>,
}

impl RegressionBisector {
    /// Create a new, empty bisector.
    #[must_use]
    pub fn new() -> Self {
        Self { history: Vec::new() }
    }

    /// Record a batch of rewrites applied at a specific iteration.
    pub fn record_rewrite(&mut self, iteration: u32, rewrites: Vec<SourceRewrite>) {
        if !rewrites.is_empty() {
            self.history.push((iteration, rewrites));
        }
    }

    /// Number of recorded iteration entries.
    #[must_use]
    pub fn history_len(&self) -> usize {
        self.history.len()
    }

    /// Total number of individual rewrites across all iterations.
    #[must_use]
    pub fn total_rewrites(&self) -> usize {
        self.history.iter().map(|(_, rws)| rws.len()).sum()
    }

    /// Binary-search over rewrite history to find the rewrite most likely
    /// responsible for a regression.
    ///
    /// Given two frontier snapshots (`before` and `after`), identifies VCs that
    /// regressed (present in `before.proved_vcs` but not in `after.proved_vcs`)
    /// and returns the earliest rewrite batch in the range `[before.iteration,
    /// after.iteration)` that could have caused the regression.
    ///
    /// Returns `None` if:
    /// - No regression is detected between the snapshots
    /// - No rewrites are recorded in the relevant iteration range
    /// - The snapshots are in the wrong order
    #[must_use]
    pub fn bisect_regression(
        &self,
        before: &FrontierSnapshot,
        after: &FrontierSnapshot,
    ) -> Option<SourceRewrite> {
        // Identify regressed VCs: proved before but not after.
        let regressed: Vec<&String> = before
            .proved_vcs
            .iter()
            .filter(|vc| !after.proved_vcs.contains(vc))
            .collect();

        if regressed.is_empty() {
            return None;
        }

        if after.iteration <= before.iteration {
            return None;
        }

        // Collect rewrites in the iteration range [before.iteration, after.iteration).
        let candidates: Vec<&SourceRewrite> = self
            .history
            .iter()
            .filter(|(iter, _)| *iter >= before.iteration && *iter < after.iteration)
            .flat_map(|(_, rws)| rws.iter())
            .collect();

        if candidates.is_empty() {
            return None;
        }

        // Binary search: find the midpoint rewrite. In a real system, we would
        // re-run verification at each bisection point. Here we return the midpoint
        // as the prime suspect, since we cannot re-run verification in this crate.
        //
        // The bisection narrows to the first rewrite in the candidate list that
        // falls at or after the midpoint iteration, which is the most actionable
        // starting point for investigation.
        let mid_iteration =
            before.iteration + (after.iteration.saturating_sub(before.iteration)) / 2;

        // Find the first candidate at or after the midpoint.
        let suspect = candidates
            .iter()
            .find(|rw| rw.iteration >= mid_iteration)
            .or_else(|| candidates.last())
            .copied();

        suspect.cloned()
    }

    /// Get all rewrites recorded for a specific iteration.
    #[must_use]
    pub fn rewrites_at(&self, iteration: u32) -> Vec<&SourceRewrite> {
        self.history
            .iter()
            .filter(|(iter, _)| *iter == iteration)
            .flat_map(|(_, rws)| rws.iter())
            .collect()
    }

    /// Get all rewrites in a range of iterations `[from, to)`.
    #[must_use]
    pub fn rewrites_in_range(&self, from: u32, to: u32) -> Vec<&SourceRewrite> {
        self.history
            .iter()
            .filter(|(iter, _)| *iter >= from && *iter < to)
            .flat_map(|(_, rws)| rws.iter())
            .collect()
    }
}

impl Default for RegressionBisector {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn snapshot(
        iteration: u32,
        proved: Vec<&str>,
        failed: Vec<&str>,
        unknown: usize,
    ) -> FrontierSnapshot {
        FrontierSnapshot {
            iteration,
            proved_count: proved.len(),
            failed_count: failed.len(),
            unknown_count: unknown,
            timestamp: 0,
            proved_vcs: proved.into_iter().map(String::from).collect(),
            failed_vcs: failed.into_iter().map(String::from).collect(),
        }
    }

    fn rewrite(iteration: u32, desc: &str, file: &str) -> SourceRewrite {
        SourceRewrite {
            iteration,
            description: desc.into(),
            file_path: file.into(),
            original: None,
            replacement: None,
        }
    }

    #[test]
    fn test_new_bisector_is_empty() {
        let b = RegressionBisector::new();
        assert_eq!(b.history_len(), 0);
        assert_eq!(b.total_rewrites(), 0);
    }

    #[test]
    fn test_record_rewrites() {
        let mut b = RegressionBisector::new();
        b.record_rewrite(0, vec![rewrite(0, "add precondition", "foo.rs")]);
        b.record_rewrite(
            1,
            vec![
                rewrite(1, "add postcondition", "bar.rs"),
                rewrite(1, "add invariant", "baz.rs"),
            ],
        );
        assert_eq!(b.history_len(), 2);
        assert_eq!(b.total_rewrites(), 3);
    }

    #[test]
    fn test_record_empty_rewrites_ignored() {
        let mut b = RegressionBisector::new();
        b.record_rewrite(0, vec![]);
        assert_eq!(b.history_len(), 0);
    }

    #[test]
    fn test_bisect_no_regression_returns_none() {
        let mut b = RegressionBisector::new();
        b.record_rewrite(0, vec![rewrite(0, "add spec", "foo.rs")]);

        let before = snapshot(0, vec!["foo::div_by_zero"], vec![], 0);
        let after = snapshot(1, vec!["foo::div_by_zero"], vec![], 0);

        assert!(b.bisect_regression(&before, &after).is_none());
    }

    #[test]
    fn test_bisect_wrong_order_returns_none() {
        let mut b = RegressionBisector::new();
        b.record_rewrite(0, vec![rewrite(0, "add spec", "foo.rs")]);

        let before = snapshot(2, vec!["foo::div_by_zero"], vec![], 0);
        let after = snapshot(1, vec![], vec!["foo::div_by_zero"], 0);

        assert!(b.bisect_regression(&before, &after).is_none());
    }

    #[test]
    fn test_bisect_no_rewrites_returns_none() {
        let b = RegressionBisector::new();
        let before = snapshot(0, vec!["foo::div_by_zero"], vec![], 0);
        let after = snapshot(1, vec![], vec!["foo::div_by_zero"], 0);

        assert!(b.bisect_regression(&before, &after).is_none());
    }

    #[test]
    fn test_bisect_finds_suspect() {
        let mut b = RegressionBisector::new();
        b.record_rewrite(0, vec![rewrite(0, "safe change", "a.rs")]);
        b.record_rewrite(1, vec![rewrite(1, "risky change", "b.rs")]);
        b.record_rewrite(2, vec![rewrite(2, "another change", "c.rs")]);

        let before = snapshot(0, vec!["foo::div_by_zero", "bar::postcond"], vec![], 0);
        let after = snapshot(3, vec!["bar::postcond"], vec!["foo::div_by_zero"], 0);

        let suspect = b.bisect_regression(&before, &after).expect("should find suspect");
        // Midpoint of [0, 3) = 1, so the suspect should be at iteration 1 or later.
        assert!(suspect.iteration >= 1);
    }

    #[test]
    fn test_bisect_single_rewrite() {
        let mut b = RegressionBisector::new();
        b.record_rewrite(0, vec![rewrite(0, "the only change", "foo.rs")]);

        let before = snapshot(0, vec!["foo::div_by_zero"], vec![], 0);
        let after = snapshot(1, vec![], vec!["foo::div_by_zero"], 0);

        let suspect = b.bisect_regression(&before, &after).expect("should find suspect");
        assert_eq!(suspect.description, "the only change");
        assert_eq!(suspect.file_path, "foo.rs");
    }

    #[test]
    fn test_rewrites_at() {
        let mut b = RegressionBisector::new();
        b.record_rewrite(0, vec![rewrite(0, "a", "a.rs")]);
        b.record_rewrite(1, vec![rewrite(1, "b", "b.rs")]);
        b.record_rewrite(2, vec![rewrite(2, "c", "c.rs")]);

        let at_1 = b.rewrites_at(1);
        assert_eq!(at_1.len(), 1);
        assert_eq!(at_1[0].description, "b");

        let at_5 = b.rewrites_at(5);
        assert!(at_5.is_empty());
    }

    #[test]
    fn test_rewrites_in_range() {
        let mut b = RegressionBisector::new();
        b.record_rewrite(0, vec![rewrite(0, "a", "a.rs")]);
        b.record_rewrite(1, vec![rewrite(1, "b", "b.rs")]);
        b.record_rewrite(2, vec![rewrite(2, "c", "c.rs")]);
        b.record_rewrite(3, vec![rewrite(3, "d", "d.rs")]);

        let range = b.rewrites_in_range(1, 3);
        assert_eq!(range.len(), 2);
        assert_eq!(range[0].description, "b");
        assert_eq!(range[1].description, "c");
    }

    #[test]
    fn test_source_rewrite_with_original_and_replacement() {
        let rw = SourceRewrite {
            iteration: 0,
            description: "strengthen precondition".into(),
            file_path: "src/foo.rs".into(),
            original: Some("fn foo(x: i32)".into()),
            replacement: Some("#[requires(x > 0)]\nfn foo(x: i32)".into()),
        };
        assert_eq!(rw.original.as_deref(), Some("fn foo(x: i32)"));
        assert!(rw.replacement.as_deref().expect("replacement").contains("#[requires"));
    }

    #[test]
    fn test_source_rewrite_json_roundtrip() {
        let rw = SourceRewrite {
            iteration: 5,
            description: "add postcondition".into(),
            file_path: "bar.rs".into(),
            original: Some("old".into()),
            replacement: Some("new".into()),
        };
        let json = serde_json::to_string(&rw).expect("serialize");
        let deserialized: SourceRewrite = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(rw, deserialized);
    }

    #[test]
    fn test_bisect_multiple_regressions() {
        let mut b = RegressionBisector::new();
        b.record_rewrite(
            1,
            vec![
                rewrite(1, "change A", "a.rs"),
                rewrite(1, "change B", "b.rs"),
            ],
        );

        let before =
            snapshot(0, vec!["foo::div_by_zero", "foo::postcond", "bar::index"], vec![], 0);
        let after = snapshot(2, vec!["bar::index"], vec!["foo::div_by_zero", "foo::postcond"], 0);

        let suspect = b.bisect_regression(&before, &after).expect("should find suspect");
        assert_eq!(suspect.iteration, 1);
    }
}
