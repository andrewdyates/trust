// trust-router/batching.rs: VC batching for efficient batch solving
//
// tRust: Groups verification conditions into batches for efficient dispatch.
// Supports grouping by VcKind, by function, by complexity tier, or treating
// each VC independently. Batches are ordered to solve easy ones first.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::VerificationCondition;

use crate::timeout::vc_complexity_score;

/// tRust: Strategy for grouping VCs into batches.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum BatchStrategy {
    /// Group VCs by their VcKind discriminant.
    ByKind,
    /// Group VCs by the function they belong to.
    ByFunction,
    /// Group VCs into complexity tiers (low, medium, high).
    ByComplexity,
    /// Each VC is its own batch (no grouping).
    Independent,
}

/// tRust: A batch of verification conditions to solve together.
#[derive(Debug, Clone)]
pub struct VcBatch {
    /// The VCs in this batch.
    pub vcs: Vec<VerificationCondition>,
    /// Estimated total time for this batch in milliseconds.
    pub estimated_total_time_ms: u64,
    /// Priority (lower = higher priority, solved first).
    pub priority: u32,
    /// Label describing this batch.
    pub label: String,
}

impl VcBatch {
    /// Number of VCs in this batch.
    #[must_use]
    pub fn len(&self) -> usize {
        self.vcs.len()
    }

    /// Whether this batch is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.vcs.is_empty()
    }
}

/// tRust: Groups VCs into batches using the given strategy.
#[must_use]
pub fn batch_vcs(
    vcs: &[VerificationCondition],
    strategy: &BatchStrategy,
) -> Vec<VcBatch> {
    match strategy {
        BatchStrategy::ByKind => batch_by_kind(vcs),
        BatchStrategy::ByFunction => batch_by_function(vcs),
        BatchStrategy::ByComplexity => batch_by_complexity(vcs),
        BatchStrategy::Independent => batch_independent(vcs),
    }
}

/// tRust: Sort batches by estimated difficulty (easiest first).
pub fn optimize_batch_order(batches: &mut [VcBatch]) {
    batches.sort_by(|a, b| {
        a.priority
            .cmp(&b.priority)
            .then_with(|| {
                a.estimated_total_time_ms.cmp(&b.estimated_total_time_ms)
            })
            .then_with(|| a.vcs.len().cmp(&b.vcs.len()))
    });
}

/// tRust: Batcher that holds configuration and groups VCs.
pub struct VcBatcher {
    strategy: BatchStrategy,
    base_time_estimate_ms: u64,
}

impl VcBatcher {
    /// Create a batcher with the given strategy.
    #[must_use]
    pub fn new(strategy: BatchStrategy) -> Self {
        Self {
            strategy,
            base_time_estimate_ms: 1000,
        }
    }

    /// Set the base time estimate per VC.
    #[must_use]
    pub fn with_base_time_estimate_ms(mut self, ms: u64) -> Self {
        self.base_time_estimate_ms = ms;
        self
    }

    /// Get the configured strategy.
    #[must_use]
    pub fn strategy(&self) -> &BatchStrategy {
        &self.strategy
    }

    /// Batch VCs and optimize order (easy first).
    #[must_use]
    pub fn batch_and_optimize(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<VcBatch> {
        let mut batches = batch_vcs(vcs, &self.strategy);

        for batch in &mut batches {
            batch.estimated_total_time_ms = batch
                .vcs
                .iter()
                .map(|vc| {
                    let score = vc_complexity_score(vc);
                    (score * self.base_time_estimate_ms as f64) as u64
                })
                .sum();
        }

        optimize_batch_order(&mut batches);
        batches
    }
}

impl Default for VcBatcher {
    fn default() -> Self {
        Self::new(BatchStrategy::ByKind)
    }
}

// -- Batching implementations --

fn batch_by_kind(vcs: &[VerificationCondition]) -> Vec<VcBatch> {
    let mut groups: FxHashMap<String, Vec<VerificationCondition>> = FxHashMap::default();

    for vc in vcs {
        let key = vc
            .kind
            .description()
            .split(':')
            .next()
            .unwrap_or("unknown")
            .to_string();
        groups.entry(key).or_default().push(vc.clone());
    }

    groups
        .into_iter()
        .map(|(label, group_vcs)| {
            let estimated = estimate_batch_time(&group_vcs);
            let priority = compute_batch_priority(&group_vcs);
            VcBatch {
                vcs: group_vcs,
                estimated_total_time_ms: estimated,
                priority,
                label,
            }
        })
        .collect()
}

fn batch_by_function(vcs: &[VerificationCondition]) -> Vec<VcBatch> {
    let mut groups: FxHashMap<String, Vec<VerificationCondition>> = FxHashMap::default();

    for vc in vcs {
        groups
            .entry(vc.function.clone())
            .or_default()
            .push(vc.clone());
    }

    groups
        .into_iter()
        .map(|(label, group_vcs)| {
            let estimated = estimate_batch_time(&group_vcs);
            let priority = compute_batch_priority(&group_vcs);
            VcBatch {
                vcs: group_vcs,
                estimated_total_time_ms: estimated,
                priority,
                label,
            }
        })
        .collect()
}

fn batch_by_complexity(vcs: &[VerificationCondition]) -> Vec<VcBatch> {
    let mut low = Vec::new();
    let mut medium = Vec::new();
    let mut high = Vec::new();

    for vc in vcs {
        let score = vc_complexity_score(vc);
        if score < 5.0 {
            low.push(vc.clone());
        } else if score < 20.0 {
            medium.push(vc.clone());
        } else {
            high.push(vc.clone());
        }
    }

    let mut batches = Vec::new();

    if !low.is_empty() {
        let estimated = estimate_batch_time(&low);
        batches.push(VcBatch {
            vcs: low,
            estimated_total_time_ms: estimated,
            priority: 0,
            label: "low-complexity".to_string(),
        });
    }

    if !medium.is_empty() {
        let estimated = estimate_batch_time(&medium);
        batches.push(VcBatch {
            vcs: medium,
            estimated_total_time_ms: estimated,
            priority: 1,
            label: "medium-complexity".to_string(),
        });
    }

    if !high.is_empty() {
        let estimated = estimate_batch_time(&high);
        batches.push(VcBatch {
            vcs: high,
            estimated_total_time_ms: estimated,
            priority: 2,
            label: "high-complexity".to_string(),
        });
    }

    batches
}

fn batch_independent(vcs: &[VerificationCondition]) -> Vec<VcBatch> {
    vcs.iter()
        .enumerate()
        .map(|(i, vc)| {
            let score = vc_complexity_score(vc);
            let estimated = (score * 1000.0) as u64;
            let priority = score as u32;
            VcBatch {
                vcs: vec![vc.clone()],
                estimated_total_time_ms: estimated,
                priority,
                label: format!("vc_{i}_{}", vc.function),
            }
        })
        .collect()
}

fn estimate_batch_time(vcs: &[VerificationCondition]) -> u64 {
    vcs.iter()
        .map(|vc| (vc_complexity_score(vc) * 1000.0) as u64)
        .sum()
}

fn compute_batch_priority(vcs: &[VerificationCondition]) -> u32 {
    if vcs.is_empty() {
        return u32::MAX;
    }
    let total: f64 = vcs.iter().map(vc_complexity_score).sum();
    let avg = total / vcs.len() as f64;
    avg as u32
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    fn test_vc(name: &str, kind: VcKind) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: name.to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        }
    }

    fn complex_formula_vc(name: &str) -> VerificationCondition {
        let x = Formula::Var("x".to_string(), Sort::Int);
        let y = Formula::Var("y".to_string(), Sort::Int);
        let body = Formula::Gt(Box::new(x), Box::new(y));
        let formula = Formula::Forall(
            vec![
                ("x".to_string(), Sort::Int),
                ("y".to_string(), Sort::Int),
            ],
            Box::new(Formula::Forall(
                vec![("z".to_string(), Sort::Int)],
                Box::new(body),
            )),
        );

        VerificationCondition {
            kind: VcKind::Postcondition,
            function: name.to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    #[test]
    fn test_batch_by_kind_groups_correctly() {
        let vcs = vec![
            test_vc("fn_a", VcKind::DivisionByZero),
            test_vc("fn_b", VcKind::DivisionByZero),
            test_vc("fn_c", VcKind::Postcondition),
        ];

        let batches = batch_vcs(&vcs, &BatchStrategy::ByKind);
        assert_eq!(batches.len(), 2);

        let total_vcs: usize = batches.iter().map(|b| b.len()).sum();
        assert_eq!(total_vcs, 3);

        let div_batch = batches
            .iter()
            .find(|b| b.label.contains("division"))
            .unwrap();
        assert_eq!(div_batch.len(), 2);
    }

    #[test]
    fn test_batch_by_function_groups_correctly() {
        let vcs = vec![
            test_vc("fn_a", VcKind::DivisionByZero),
            test_vc("fn_a", VcKind::Postcondition),
            test_vc("fn_b", VcKind::DivisionByZero),
        ];

        let batches = batch_vcs(&vcs, &BatchStrategy::ByFunction);
        assert_eq!(batches.len(), 2);

        let fn_a = batches.iter().find(|b| b.label == "fn_a").unwrap();
        assert_eq!(fn_a.len(), 2);

        let fn_b = batches.iter().find(|b| b.label == "fn_b").unwrap();
        assert_eq!(fn_b.len(), 1);
    }

    #[test]
    fn test_batch_by_complexity_tiers() {
        let mut vcs = vec![
            test_vc("simple1", VcKind::DivisionByZero),
            test_vc("simple2", VcKind::DivisionByZero),
        ];
        vcs.push(complex_formula_vc("complex1"));

        let batches = batch_vcs(&vcs, &BatchStrategy::ByComplexity);
        assert!(!batches.is_empty());

        let total: usize = batches.iter().map(|b| b.len()).sum();
        assert_eq!(total, 3);
    }

    #[test]
    fn test_batch_independent_one_per_vc() {
        let vcs = vec![
            test_vc("fn_a", VcKind::DivisionByZero),
            test_vc("fn_b", VcKind::Postcondition),
            test_vc("fn_c", VcKind::IndexOutOfBounds),
        ];

        let batches = batch_vcs(&vcs, &BatchStrategy::Independent);
        assert_eq!(batches.len(), 3);
        for batch in &batches {
            assert_eq!(batch.len(), 1);
        }
    }

    #[test]
    fn test_optimize_batch_order_easy_first() {
        let mut batches = vec![
            VcBatch {
                vcs: vec![],
                estimated_total_time_ms: 5000,
                priority: 2,
                label: "hard".to_string(),
            },
            VcBatch {
                vcs: vec![],
                estimated_total_time_ms: 100,
                priority: 0,
                label: "easy".to_string(),
            },
            VcBatch {
                vcs: vec![],
                estimated_total_time_ms: 1000,
                priority: 1,
                label: "medium".to_string(),
            },
        ];

        optimize_batch_order(&mut batches);
        assert_eq!(batches[0].label, "easy");
        assert_eq!(batches[1].label, "medium");
        assert_eq!(batches[2].label, "hard");
    }

    #[test]
    fn test_optimize_batch_order_tiebreak_by_time() {
        let mut batches = vec![
            VcBatch {
                vcs: vec![],
                estimated_total_time_ms: 5000,
                priority: 1,
                label: "slow".to_string(),
            },
            VcBatch {
                vcs: vec![],
                estimated_total_time_ms: 100,
                priority: 1,
                label: "fast".to_string(),
            },
        ];

        optimize_batch_order(&mut batches);
        assert_eq!(batches[0].label, "fast");
        assert_eq!(batches[1].label, "slow");
    }

    #[test]
    fn test_batch_empty_input() {
        let vcs: Vec<VerificationCondition> = vec![];
        for strategy in [
            BatchStrategy::ByKind,
            BatchStrategy::ByFunction,
            BatchStrategy::ByComplexity,
            BatchStrategy::Independent,
        ] {
            let batches = batch_vcs(&vcs, &strategy);
            assert!(
                batches.is_empty(),
                "empty input should produce empty batches for {strategy:?}"
            );
        }
    }

    #[test]
    fn test_vc_batch_len_and_is_empty() {
        let batch = VcBatch {
            vcs: vec![test_vc("fn_a", VcKind::DivisionByZero)],
            estimated_total_time_ms: 100,
            priority: 0,
            label: "test".to_string(),
        };
        assert_eq!(batch.len(), 1);
        assert!(!batch.is_empty());

        let empty = VcBatch {
            vcs: vec![],
            estimated_total_time_ms: 0,
            priority: 0,
            label: "empty".to_string(),
        };
        assert_eq!(empty.len(), 0);
        assert!(empty.is_empty());
    }

    #[test]
    fn test_vc_batcher_batch_and_optimize() {
        let vcs = vec![
            test_vc("fn_a", VcKind::DivisionByZero),
            test_vc("fn_b", VcKind::Postcondition),
            test_vc("fn_c", VcKind::DivisionByZero),
        ];

        let batcher = VcBatcher::new(BatchStrategy::ByKind);
        let batches = batcher.batch_and_optimize(&vcs);
        assert_eq!(batches.len(), 2);
    }

    #[test]
    fn test_vc_batcher_default() {
        let batcher = VcBatcher::default();
        assert_eq!(*batcher.strategy(), BatchStrategy::ByKind);
    }

    #[test]
    fn test_vc_batcher_custom_base_time() {
        let batcher = VcBatcher::new(BatchStrategy::Independent)
            .with_base_time_estimate_ms(500);

        let vcs = vec![test_vc("fn_a", VcKind::DivisionByZero)];
        let batches = batcher.batch_and_optimize(&vcs);
        assert_eq!(batches.len(), 1);
        assert!(batches[0].estimated_total_time_ms > 0);
    }

    #[test]
    fn test_batch_strategy_eq() {
        assert_eq!(BatchStrategy::ByKind, BatchStrategy::ByKind);
        assert_ne!(BatchStrategy::ByKind, BatchStrategy::ByFunction);
    }

    #[test]
    fn test_batch_preserves_all_vcs() {
        let vcs: Vec<_> = (0..20)
            .map(|i| test_vc(&format!("fn_{i}"), VcKind::DivisionByZero))
            .collect();

        for strategy in [
            BatchStrategy::ByKind,
            BatchStrategy::ByFunction,
            BatchStrategy::ByComplexity,
            BatchStrategy::Independent,
        ] {
            let batches = batch_vcs(&vcs, &strategy);
            let total: usize = batches.iter().map(|b| b.len()).sum();
            assert_eq!(
                total, 20,
                "all VCs must be preserved for {strategy:?}"
            );
        }
    }

    #[test]
    fn test_batch_by_complexity_separates_simple_and_complex() {
        let mut vcs = vec![test_vc("simple", VcKind::DivisionByZero)];
        vcs.push(complex_formula_vc("hard"));

        let batches = batch_vcs(&vcs, &BatchStrategy::ByComplexity);
        assert!(
            batches.len() >= 2,
            "simple and complex should be in different tiers"
        );

        let low = batches.iter().find(|b| b.label == "low-complexity");
        let other = batches.iter().find(|b| b.label != "low-complexity");
        assert!(low.is_some(), "should have a low-complexity batch");
        assert!(other.is_some(), "should have a higher-complexity batch");
    }
}
