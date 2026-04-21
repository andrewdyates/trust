// trust-symex/src/merge_heuristic.rs — State merging heuristics for symbolic execution
//
// Decides when merging two symbolic states is beneficial vs. harmful.
// Uses Jaccard similarity on variable sets, constraint complexity estimates,
// and coverage-gain metrics to score merge candidates.
//
// Part of #272
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Decision produced by the heuristic after evaluating a merge candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MergeDecision {
    /// The two states should be merged — expected net benefit.
    Merge,
    /// Merging is not worthwhile — keep states separate.
    Skip,
    /// Decision cannot be made yet; re-evaluate after more exploration.
    Defer,
}

/// Which similarity metric to apply when comparing two symbolic states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SimilarityMetric {
    /// Compare the structure of symbolic expressions (variable sets).
    Structural,
    /// Compare the concrete value ranges of variables.
    ValueBased,
    /// Compare the path-constraint histories.
    PathBased,
}

/// A pair of states being considered for merging, together with their score.
#[derive(Debug, Clone)]
pub(crate) struct MergeCandidate {
    /// Identifier of the first state.
    pub state_a_id: usize,
    /// Identifier of the second state.
    pub state_b_id: usize,
    /// Composite score for this candidate pair.
    pub score: MergeScore,
}

/// Quantitative score capturing how beneficial a merge would be.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct MergeScore {
    /// Jaccard similarity of the two variable sets (0.0 .. 1.0).
    pub similarity: f64,
    /// Estimated constraint complexity of state A.
    pub constraint_complexity_a: usize,
    /// Estimated constraint complexity of state B.
    pub constraint_complexity_b: usize,
    /// Estimated constraint complexity after merging.
    pub estimated_merged_complexity: usize,
    /// Fraction of new coverage gained by merging (0.0 .. 1.0).
    pub coverage_gain: f64,
}

// ---------------------------------------------------------------------------
// Heuristic
// ---------------------------------------------------------------------------

/// Configurable heuristic that decides whether two symbolic states should be
/// merged based on similarity, complexity, and coverage metrics.
#[derive(Debug, Clone)]
pub(crate) struct MergeHeuristic {
    /// Maximum allowed merged constraint complexity.
    pub max_complexity: usize,
    /// Minimum similarity required to consider merging (0.0 .. 1.0).
    pub min_similarity: f64,
    /// Weight given to coverage gain in the final decision (0.0 .. 1.0).
    pub coverage_weight: f64,
}

impl Default for MergeHeuristic {
    fn default() -> Self {
        Self {
            max_complexity: 1000,
            min_similarity: 0.5,
            coverage_weight: 0.3,
        }
    }
}

impl MergeHeuristic {
    /// Create a new heuristic with the given parameters.
    pub(crate) fn new(max_complexity: usize, min_similarity: f64, coverage_weight: f64) -> Self {
        Self {
            max_complexity,
            min_similarity,
            coverage_weight,
        }
    }

    /// Decide whether to merge, skip, or defer based on a [`MergeScore`].
    ///
    /// Decision rules:
    /// 1. If similarity is below the minimum threshold, **Skip**.
    /// 2. If the estimated merged complexity exceeds the maximum, **Defer**
    ///    (might become feasible after simplification).
    /// 3. Compute a weighted score: `similarity * (1 - w) + coverage_gain * w`.
    ///    If the weighted score >= 0.4 the merge is accepted; otherwise skip.
    pub(crate) fn should_merge(&self, score: &MergeScore) -> MergeDecision {
        // Gate 1: similarity floor
        if score.similarity < self.min_similarity {
            return MergeDecision::Skip;
        }

        // Gate 2: complexity ceiling
        if score.estimated_merged_complexity > self.max_complexity {
            return MergeDecision::Defer;
        }

        // Gate 3: weighted score
        let weighted = score.similarity * (1.0 - self.coverage_weight)
            + score.coverage_gain * self.coverage_weight;

        if weighted >= 0.4 {
            MergeDecision::Merge
        } else {
            MergeDecision::Skip
        }
    }

    /// Compute Jaccard similarity between two variable sets.
    ///
    /// J(A, B) = |A intersect B| / |A union B|.  Returns 1.0 when both sets
    /// are empty (vacuously identical).
    pub(crate) fn similarity_score(
        vars_a: &FxHashSet<String>,
        vars_b: &FxHashSet<String>,
    ) -> f64 {
        let intersection = vars_a.intersection(vars_b).count();
        let union = vars_a.union(vars_b).count();
        if union == 0 {
            return 1.0;
        }
        intersection as f64 / union as f64
    }

    /// Estimate constraint complexity as the product of the number of
    /// constraints and the number of variables.  A zero in either dimension
    /// yields complexity 0.
    pub(crate) fn constraint_complexity(num_constraints: usize, num_variables: usize) -> usize {
        num_constraints.saturating_mul(num_variables)
    }

    /// Estimate the fraction of new coverage gained by merging the two states.
    ///
    /// `coverage_gain = |covered_a union covered_b| / total`
    ///
    /// We approximate `|A union B|` as `min(covered_a + covered_b, total)`
    /// (upper bound — the actual union may be smaller due to overlap, but the
    /// heuristic errs on the side of optimism to encourage merging).
    ///
    /// Returns 0.0 when `total` is 0.
    pub(crate) fn coverage_gain(
        covered_a: usize,
        covered_b: usize,
        total: usize,
    ) -> f64 {
        if total == 0 {
            return 0.0;
        }
        let union_approx = (covered_a + covered_b).min(total);
        union_approx as f64 / total as f64
    }

    /// Build a full [`MergeCandidate`] for two states identified by their
    /// variable sets, constraint counts, and coverage numbers.
    ///
    /// The candidate's `state_a_id` and `state_b_id` are set to 0; callers
    /// should overwrite them with the actual identifiers.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn evaluate_candidate(
        &self,
        vars_a: &FxHashSet<String>,
        vars_b: &FxHashSet<String>,
        constraints_a: usize,
        constraints_b: usize,
        covered_a: usize,
        covered_b: usize,
        total: usize,
    ) -> MergeCandidate {
        let similarity = Self::similarity_score(vars_a, vars_b);
        let complexity_a = Self::constraint_complexity(constraints_a, vars_a.len());
        let complexity_b = Self::constraint_complexity(constraints_b, vars_b.len());

        // Estimate merged complexity: union of variables times sum of constraints,
        // minus a discount proportional to similarity (shared constraints collapse).
        let merged_vars = vars_a.union(vars_b).count();
        let raw_merged = (constraints_a + constraints_b).saturating_mul(merged_vars);
        let discount = (raw_merged as f64 * similarity * 0.5) as usize;
        let estimated_merged_complexity = raw_merged.saturating_sub(discount);

        let cov_gain = Self::coverage_gain(covered_a, covered_b, total);

        MergeCandidate {
            state_a_id: 0,
            state_b_id: 0,
            score: MergeScore {
                similarity,
                constraint_complexity_a: complexity_a,
                constraint_complexity_b: complexity_b,
                estimated_merged_complexity,
                coverage_gain: cov_gain,
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn set_of(items: &[&str]) -> FxHashSet<String> {
        items.iter().map(|s| (*s).to_owned()).collect()
    }

    // -- MergeDecision / Default ------------------------------------------

    #[test]
    fn test_default_heuristic_values() {
        let h = MergeHeuristic::default();
        assert_eq!(h.max_complexity, 1000);
        assert!((h.min_similarity - 0.5).abs() < f64::EPSILON);
        assert!((h.coverage_weight - 0.3).abs() < f64::EPSILON);
    }

    #[test]
    fn test_new_heuristic_custom_values() {
        let h = MergeHeuristic::new(500, 0.7, 0.5);
        assert_eq!(h.max_complexity, 500);
        assert!((h.min_similarity - 0.7).abs() < f64::EPSILON);
        assert!((h.coverage_weight - 0.5).abs() < f64::EPSILON);
    }

    // -- similarity_score -------------------------------------------------

    #[test]
    fn test_similarity_identical_sets() {
        let a = set_of(&["x", "y", "z"]);
        let b = set_of(&["x", "y", "z"]);
        let score = MergeHeuristic::similarity_score(&a, &b);
        assert!((score - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_similarity_disjoint_sets() {
        let a = set_of(&["x", "y"]);
        let b = set_of(&["w", "z"]);
        let score = MergeHeuristic::similarity_score(&a, &b);
        assert!((score - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_similarity_partial_overlap() {
        let a = set_of(&["x", "y", "z"]);
        let b = set_of(&["y", "z", "w"]);
        // intersection = {y, z} = 2, union = {x, y, z, w} = 4 => 0.5
        let score = MergeHeuristic::similarity_score(&a, &b);
        assert!((score - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_similarity_both_empty() {
        let a: FxHashSet<String> = FxHashSet::default();
        let b: FxHashSet<String> = FxHashSet::default();
        let score = MergeHeuristic::similarity_score(&a, &b);
        assert!((score - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_similarity_one_empty() {
        let a = set_of(&["x"]);
        let b: FxHashSet<String> = FxHashSet::default();
        // intersection = 0, union = 1 => 0.0
        let score = MergeHeuristic::similarity_score(&a, &b);
        assert!((score - 0.0).abs() < f64::EPSILON);
    }

    // -- constraint_complexity --------------------------------------------

    #[test]
    fn test_constraint_complexity_basic() {
        assert_eq!(MergeHeuristic::constraint_complexity(10, 5), 50);
    }

    #[test]
    fn test_constraint_complexity_zero() {
        assert_eq!(MergeHeuristic::constraint_complexity(0, 100), 0);
        assert_eq!(MergeHeuristic::constraint_complexity(100, 0), 0);
    }

    // -- coverage_gain ----------------------------------------------------

    #[test]
    fn test_coverage_gain_basic() {
        // covered_a=3, covered_b=4, total=10 => min(7, 10)/10 = 0.7
        let gain = MergeHeuristic::coverage_gain(3, 4, 10);
        assert!((gain - 0.7).abs() < f64::EPSILON);
    }

    #[test]
    fn test_coverage_gain_exceeds_total() {
        // covered_a=6, covered_b=7, total=10 => min(13, 10)/10 = 1.0
        let gain = MergeHeuristic::coverage_gain(6, 7, 10);
        assert!((gain - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_coverage_gain_zero_total() {
        let gain = MergeHeuristic::coverage_gain(5, 5, 0);
        assert!((gain - 0.0).abs() < f64::EPSILON);
    }

    // -- should_merge -----------------------------------------------------

    #[test]
    fn test_should_merge_high_similarity_good_coverage() {
        let h = MergeHeuristic::default(); // min_sim=0.5, max_cx=1000, w=0.3
        let score = MergeScore {
            similarity: 0.8,
            constraint_complexity_a: 100,
            constraint_complexity_b: 120,
            estimated_merged_complexity: 400,
            coverage_gain: 0.6,
        };
        // weighted = 0.8*0.7 + 0.6*0.3 = 0.56 + 0.18 = 0.74 >= 0.4
        assert_eq!(h.should_merge(&score), MergeDecision::Merge);
    }

    #[test]
    fn test_should_merge_low_similarity_skips() {
        let h = MergeHeuristic::default();
        let score = MergeScore {
            similarity: 0.2,
            constraint_complexity_a: 10,
            constraint_complexity_b: 10,
            estimated_merged_complexity: 20,
            coverage_gain: 1.0,
        };
        assert_eq!(h.should_merge(&score), MergeDecision::Skip);
    }

    #[test]
    fn test_should_merge_excessive_complexity_defers() {
        let h = MergeHeuristic::new(100, 0.3, 0.3);
        let score = MergeScore {
            similarity: 0.9,
            constraint_complexity_a: 80,
            constraint_complexity_b: 80,
            estimated_merged_complexity: 150, // > 100
            coverage_gain: 0.8,
        };
        assert_eq!(h.should_merge(&score), MergeDecision::Defer);
    }

    #[test]
    fn test_should_merge_low_weighted_score_skips() {
        let h = MergeHeuristic::new(1000, 0.5, 0.3);
        let score = MergeScore {
            similarity: 0.5,
            constraint_complexity_a: 50,
            constraint_complexity_b: 50,
            estimated_merged_complexity: 90,
            coverage_gain: 0.0,
        };
        // weighted = 0.5*0.7 + 0.0*0.3 = 0.35 < 0.4
        assert_eq!(h.should_merge(&score), MergeDecision::Skip);
    }

    // -- evaluate_candidate -----------------------------------------------

    #[test]
    fn test_evaluate_candidate_builds_score() {
        let h = MergeHeuristic::default();
        let vars_a = set_of(&["x", "y", "z"]);
        let vars_b = set_of(&["y", "z", "w"]);

        let candidate = h.evaluate_candidate(
            &vars_a, &vars_b,
            /* constraints_a */ 5,
            /* constraints_b */ 5,
            /* covered_a */ 3,
            /* covered_b */ 4,
            /* total */ 10,
        );

        // Similarity: J = 2/4 = 0.5
        assert!((candidate.score.similarity - 0.5).abs() < f64::EPSILON);

        // Complexity A: 5 * 3 = 15, B: 5 * 3 = 15
        assert_eq!(candidate.score.constraint_complexity_a, 15);
        assert_eq!(candidate.score.constraint_complexity_b, 15);

        // Merged: (5+5)*4 = 40, discount = floor(40*0.5*0.5) = 10, result = 30
        assert_eq!(candidate.score.estimated_merged_complexity, 30);

        // Coverage gain: min(3+4, 10)/10 = 0.7
        assert!((candidate.score.coverage_gain - 0.7).abs() < f64::EPSILON);

        // Default ids are 0
        assert_eq!(candidate.state_a_id, 0);
        assert_eq!(candidate.state_b_id, 0);
    }
}
