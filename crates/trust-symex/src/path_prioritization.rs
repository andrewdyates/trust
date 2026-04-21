// trust-symex path prioritization heuristics
//
// ML-inspired path prioritization for smarter symbolic execution exploration.
// Extracts features from symbolic paths and uses a weighted model to compute
// priority scores, enabling adaptive exploration strategies.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::path::PathConstraint;
use crate::state::SymbolicValue;

/// Features extracted from a symbolic execution path for prioritization.
///
/// These features characterize a path's exploration potential and are used
/// by `PriorityModel` to compute a priority score.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub(crate) struct PathFeatures {
    /// Number of branch decisions on this path.
    pub depth: usize,
    /// Total number of branch points encountered (including re-visits).
    pub branch_count: usize,
    /// Complexity of the accumulated path constraint (higher = harder to solve).
    pub constraint_complexity: f64,
    /// Novelty score: how much new coverage this path is likely to provide.
    pub novelty_score: f64,
}

impl Default for PathFeatures {
    fn default() -> Self {
        Self {
            depth: 0,
            branch_count: 0,
            constraint_complexity: 0.0,
            novelty_score: 1.0,
        }
    }
}

/// Weights for feature-based path prioritization.
///
/// Each weight controls how much a given feature influences the final
/// priority score. Negative weights penalize the feature; positive weights
/// reward it.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub(crate) struct PriorityModel {
    /// Weight for path depth (typically negative to penalize deep paths).
    pub depth_weight: f64,
    /// Weight for branch count.
    pub branch_weight: f64,
    /// Weight for constraint complexity (typically negative to avoid hard paths).
    pub complexity_weight: f64,
    /// Weight for novelty score (typically positive to prefer novel paths).
    pub novelty_weight: f64,
    /// Learning rate for weight updates.
    pub learning_rate: f64,
}

impl Default for PriorityModel {
    fn default() -> Self {
        Self {
            depth_weight: -0.1,
            branch_weight: 0.05,
            complexity_weight: -0.2,
            novelty_weight: 1.0,
            learning_rate: 0.01,
        }
    }
}

impl PriorityModel {
    /// Create a model with custom weights.
    #[must_use]
    pub(crate) fn new(
        depth_weight: f64,
        branch_weight: f64,
        complexity_weight: f64,
        novelty_weight: f64,
    ) -> Self {
        Self {
            depth_weight,
            branch_weight,
            complexity_weight,
            novelty_weight,
            learning_rate: 0.01,
        }
    }

    /// Create a model tuned for a specific strategy.
    #[must_use]
    pub(crate) fn for_strategy(strategy: PrioritizationStrategy) -> Self {
        match strategy {
            PrioritizationStrategy::Depth => Self {
                depth_weight: -1.0,
                branch_weight: 0.0,
                complexity_weight: 0.0,
                novelty_weight: 0.0,
                learning_rate: 0.01,
            },
            PrioritizationStrategy::Novelty => Self {
                depth_weight: 0.0,
                branch_weight: 0.0,
                complexity_weight: 0.0,
                novelty_weight: 1.0,
                learning_rate: 0.01,
            },
            PrioritizationStrategy::Complexity => Self {
                depth_weight: 0.0,
                branch_weight: 0.0,
                complexity_weight: -1.0,
                novelty_weight: 0.0,
                learning_rate: 0.01,
            },
            PrioritizationStrategy::Balanced => Self::default(),
        }
    }
}

/// Computed priority value for a symbolic path.
///
/// Higher values indicate higher priority for exploration.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub(crate) struct PathPriority {
    /// The computed priority score.
    pub score: f64,
    /// The features that were used to compute this score.
    pub features: PathFeatures,
}

impl PathPriority {
    /// Create a new priority from a score and features.
    #[must_use]
    pub(crate) fn new(score: f64, features: PathFeatures) -> Self {
        Self { score, features }
    }
}

/// Strategy for how path features influence prioritization.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum PrioritizationStrategy {
    /// Prefer shallow paths (low depth).
    Depth,
    /// Prefer novel paths (high novelty score).
    Novelty,
    /// Prefer simple paths (low constraint complexity).
    Complexity,
    /// Balanced combination of all features.
    Balanced,
}

/// Extract features from a path constraint and its associated state.
///
/// Computes depth, branch count, constraint complexity, and a baseline
/// novelty score. Novelty starts at 1.0 and should be adjusted externally
/// based on coverage information.
#[must_use]
pub(crate) fn extract_features(path: &PathConstraint, novelty_score: f64) -> PathFeatures {
    let depth = path.depth();
    let branch_count = path.decisions().len();
    let constraint_complexity = compute_constraint_complexity(path);

    PathFeatures {
        depth,
        branch_count,
        constraint_complexity,
        novelty_score,
    }
}

/// Compute a complexity score for the path's accumulated constraints.
///
/// Measures the total AST size of all constraint conditions. Larger
/// expressions are harder for SMT solvers to handle.
fn compute_constraint_complexity(path: &PathConstraint) -> f64 {
    path.decisions()
        .iter()
        .map(|d| symbolic_value_complexity(&d.condition))
        .sum()
}

/// Recursively compute the AST node count of a symbolic value.
fn symbolic_value_complexity(val: &SymbolicValue) -> f64 {
    match val {
        SymbolicValue::Concrete(_) | SymbolicValue::Symbol(_) => 1.0,
        SymbolicValue::BinOp(lhs, _, rhs) => {
            1.0 + symbolic_value_complexity(lhs) + symbolic_value_complexity(rhs)
        }
        SymbolicValue::Ite(cond, then_val, else_val) => {
            1.0 + symbolic_value_complexity(cond)
                + symbolic_value_complexity(then_val)
                + symbolic_value_complexity(else_val)
        }
        SymbolicValue::Not(inner)
        | SymbolicValue::BitwiseNot(inner)
        | SymbolicValue::Neg(inner) => 1.0 + symbolic_value_complexity(inner),
    }
}

/// Compute the priority of a path using the given model and features.
///
/// The score is a linear combination of features weighted by the model.
#[must_use]
pub(crate) fn compute_priority(model: &PriorityModel, features: &PathFeatures) -> PathPriority {
    let score = model.depth_weight * features.depth as f64
        + model.branch_weight * features.branch_count as f64
        + model.complexity_weight * features.constraint_complexity
        + model.novelty_weight * features.novelty_score;

    PathPriority {
        score,
        features: features.clone(),
    }
}

/// Update model weights based on exploration outcome.
///
/// After exploring a path, we observe whether it was "successful" (e.g.,
/// found new coverage, hit a bug, or produced a useful counterexample).
/// The `reward` is positive for good outcomes, negative for wasted
/// exploration. Weights are adjusted via gradient-like update.
pub(crate) fn update_model(model: &mut PriorityModel, features: &PathFeatures, reward: f64) {
    let lr = model.learning_rate;
    model.depth_weight += lr * reward * features.depth as f64;
    model.branch_weight += lr * reward * features.branch_count as f64;
    model.complexity_weight += lr * reward * features.constraint_complexity;
    model.novelty_weight += lr * reward * features.novelty_score;
}

#[cfg(test)]
mod tests {
    use trust_types::BinOp;

    use super::*;
    use crate::path::PathConstraint;
    use crate::state::SymbolicValue;

    fn make_path(num_constraints: usize) -> PathConstraint {
        let mut path = PathConstraint::new();
        for _ in 0..num_constraints {
            path.add_constraint(SymbolicValue::Concrete(1), true);
        }
        path
    }

    fn make_complex_path() -> PathConstraint {
        let mut path = PathConstraint::new();
        // Add a constraint with a complex expression tree
        let expr = SymbolicValue::bin_op(
            SymbolicValue::bin_op(
                SymbolicValue::Symbol("x".into()),
                BinOp::Add,
                SymbolicValue::Concrete(1),
            ),
            BinOp::Lt,
            SymbolicValue::bin_op(
                SymbolicValue::Symbol("y".into()),
                BinOp::Mul,
                SymbolicValue::Concrete(2),
            ),
        );
        path.add_constraint(expr, true);
        path
    }

    #[test]
    fn test_path_prioritization_extract_features_empty_path() {
        let path = PathConstraint::new();
        let features = extract_features(&path, 1.0);
        assert_eq!(features.depth, 0);
        assert_eq!(features.branch_count, 0);
        assert_eq!(features.constraint_complexity, 0.0);
        assert_eq!(features.novelty_score, 1.0);
    }

    #[test]
    fn test_path_prioritization_extract_features_simple_path() {
        let path = make_path(3);
        let features = extract_features(&path, 0.5);
        assert_eq!(features.depth, 3);
        assert_eq!(features.branch_count, 3);
        // Each Concrete(1) has complexity 1.0
        assert_eq!(features.constraint_complexity, 3.0);
        assert_eq!(features.novelty_score, 0.5);
    }

    #[test]
    fn test_path_prioritization_extract_features_complex_path() {
        let path = make_complex_path();
        let features = extract_features(&path, 0.8);
        assert_eq!(features.depth, 1);
        assert_eq!(features.branch_count, 1);
        // BinOp(BinOp(Symbol, _, Concrete), _, BinOp(Symbol, _, Concrete))
        // = 1 + (1 + 1 + 1) + (1 + 1 + 1) = 7
        assert_eq!(features.constraint_complexity, 7.0);
        assert_eq!(features.novelty_score, 0.8);
    }

    #[test]
    fn test_path_prioritization_compute_priority_default_model() {
        let model = PriorityModel::default();
        let features = PathFeatures {
            depth: 5,
            branch_count: 5,
            constraint_complexity: 10.0,
            novelty_score: 0.9,
        };
        let priority = compute_priority(&model, &features);
        // -0.1*5 + 0.05*5 + -0.2*10 + 1.0*0.9 = -0.5 + 0.25 - 2.0 + 0.9 = -1.35
        let expected = -0.1 * 5.0 + 0.05 * 5.0 + -0.2 * 10.0 + 1.0 * 0.9;
        assert!((priority.score - expected).abs() < 1e-10);
    }

    #[test]
    fn test_path_prioritization_compute_priority_depth_strategy() {
        let model = PriorityModel::for_strategy(PrioritizationStrategy::Depth);
        let shallow = PathFeatures { depth: 2, branch_count: 2, constraint_complexity: 1.0, novelty_score: 0.5 };
        let deep = PathFeatures { depth: 20, branch_count: 20, constraint_complexity: 1.0, novelty_score: 0.5 };
        let p_shallow = compute_priority(&model, &shallow);
        let p_deep = compute_priority(&model, &deep);
        // Depth strategy should prefer shallow paths (higher score)
        assert!(p_shallow.score > p_deep.score);
    }

    #[test]
    fn test_path_prioritization_compute_priority_novelty_strategy() {
        let model = PriorityModel::for_strategy(PrioritizationStrategy::Novelty);
        let novel = PathFeatures { depth: 10, branch_count: 10, constraint_complexity: 5.0, novelty_score: 1.0 };
        let stale = PathFeatures { depth: 2, branch_count: 2, constraint_complexity: 1.0, novelty_score: 0.1 };
        let p_novel = compute_priority(&model, &novel);
        let p_stale = compute_priority(&model, &stale);
        // Novelty strategy should prefer novel paths regardless of depth
        assert!(p_novel.score > p_stale.score);
    }

    #[test]
    fn test_path_prioritization_compute_priority_complexity_strategy() {
        let model = PriorityModel::for_strategy(PrioritizationStrategy::Complexity);
        let simple = PathFeatures { depth: 10, branch_count: 10, constraint_complexity: 2.0, novelty_score: 0.5 };
        let complex = PathFeatures { depth: 2, branch_count: 2, constraint_complexity: 50.0, novelty_score: 0.5 };
        let p_simple = compute_priority(&model, &simple);
        let p_complex = compute_priority(&model, &complex);
        // Complexity strategy should prefer simpler paths (higher score)
        assert!(p_simple.score > p_complex.score);
    }

    #[test]
    fn test_path_prioritization_update_model_positive_reward() {
        let mut model = PriorityModel::default();
        let features = PathFeatures { depth: 5, branch_count: 3, constraint_complexity: 2.0, novelty_score: 0.8 };
        let original_novelty = model.novelty_weight;
        update_model(&mut model, &features, 1.0);
        // Positive reward should increase novelty weight (novelty_score > 0)
        assert!(model.novelty_weight > original_novelty);
    }

    #[test]
    fn test_path_prioritization_update_model_negative_reward() {
        let mut model = PriorityModel::default();
        let features = PathFeatures { depth: 5, branch_count: 3, constraint_complexity: 2.0, novelty_score: 0.8 };
        let original_novelty = model.novelty_weight;
        update_model(&mut model, &features, -1.0);
        // Negative reward should decrease novelty weight
        assert!(model.novelty_weight < original_novelty);
    }

    #[test]
    fn test_path_prioritization_update_model_zero_reward() {
        let mut model = PriorityModel::default();
        let original = model.clone();
        let features = PathFeatures { depth: 5, branch_count: 3, constraint_complexity: 2.0, novelty_score: 0.8 };
        update_model(&mut model, &features, 0.0);
        // Zero reward should not change weights
        assert_eq!(model.depth_weight, original.depth_weight);
        assert_eq!(model.novelty_weight, original.novelty_weight);
    }

    #[test]
    fn test_path_prioritization_model_for_strategy_balanced() {
        let model = PriorityModel::for_strategy(PrioritizationStrategy::Balanced);
        let default = PriorityModel::default();
        assert_eq!(model.depth_weight, default.depth_weight);
        assert_eq!(model.novelty_weight, default.novelty_weight);
    }

    #[test]
    fn test_path_prioritization_path_priority_ordering() {
        let model = PriorityModel::default();
        let path_a = make_path(2);
        let path_b = make_path(10);
        let features_a = extract_features(&path_a, 0.9);
        let features_b = extract_features(&path_b, 0.1);
        let prio_a = compute_priority(&model, &features_a);
        let prio_b = compute_priority(&model, &features_b);
        // Shallow path with high novelty should beat deep path with low novelty
        assert!(prio_a.score > prio_b.score);
    }

    #[test]
    fn test_path_prioritization_symbolic_value_complexity_ite() {
        let expr = SymbolicValue::ite(
            SymbolicValue::Symbol("c".into()),
            SymbolicValue::Concrete(1),
            SymbolicValue::Concrete(0),
        );
        // Ite(Symbol, Concrete, Concrete) = 1 + 1 + 1 + 1 = 4
        assert_eq!(symbolic_value_complexity(&expr), 4.0);
    }

    #[test]
    fn test_path_prioritization_symbolic_value_complexity_not() {
        let expr = SymbolicValue::Not(Box::new(SymbolicValue::Symbol("x".into())));
        // Not(Symbol) = 1 + 1 = 2
        assert_eq!(symbolic_value_complexity(&expr), 2.0);
    }

    #[test]
    fn test_path_prioritization_default_features() {
        let features = PathFeatures::default();
        assert_eq!(features.depth, 0);
        assert_eq!(features.branch_count, 0);
        assert_eq!(features.constraint_complexity, 0.0);
        assert_eq!(features.novelty_score, 1.0);
    }
}
