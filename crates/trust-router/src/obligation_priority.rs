// trust-router/obligation_priority.rs: Proof obligation prioritization
//
// tRust: Smart ordering of proof obligations for early failure detection
// and cache utilization. Obligations are scored by estimated difficulty,
// dependency depth, cache likelihood, failure history, and formula size.
// The scheduler produces a dependency-respecting parallel batch plan.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};

/// tRust: Priority metadata for a single proof obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObligationPriority {
    /// Unique identifier for this obligation.
    pub obligation_id: String,
    /// Composite priority score (lower = higher priority, checked first).
    pub score: u64,
    /// Factor breakdown that produced the score.
    pub factors: PriorityFactors,
}

/// tRust: Individual factors contributing to an obligation's priority score.
///
/// All fields are `u32` to keep the struct `Eq`-derivable (no floats).
/// Each factor is in the range 0..=100 (normalized weight).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct PriorityFactors {
    /// How hard the obligation is expected to be (0 = trivial, 100 = very hard).
    pub estimated_difficulty: u32,
    /// Depth in the dependency graph (0 = no dependencies).
    pub dependency_depth: u32,
    /// Likelihood of a cache hit (0 = unlikely, 100 = very likely).
    pub cache_likelihood: u32,
    /// Number of prior failures for this obligation or similar ones.
    pub failure_history: u32,
    /// Formula size score (AST node count or similar metric).
    pub size_score: u32,
}

impl PriorityFactors {
    /// Compute composite score: lower = check sooner.
    ///
    /// Strategy: prefer easy obligations first (fast wins), those with
    /// failure history (likely to fail again), and those with cache hits.
    /// Dependency depth pushes obligations later (wait for prerequisites).
    #[must_use]
    pub fn composite_score(&self) -> u64 {
        // Weights: difficulty pulls score up (defer hard ones when prefer_easy),
        // failure history pulls score down (check likely failures first),
        // cache likelihood pulls score down (cheap to verify),
        // dependency depth pushes up (wait for deps),
        // size pushes up slightly (bigger formulas take longer).
        let base = u64::from(self.estimated_difficulty) * 3
            + u64::from(self.dependency_depth) * 5
            + u64::from(self.size_score) * 2;
        let reduction =
            u64::from(self.failure_history) * 4 + u64::from(self.cache_likelihood) * 2;
        base.saturating_sub(reduction)
    }
}

/// tRust: Configuration for the obligation scheduler.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchedulingConfig {
    /// Maximum number of obligations to verify in parallel.
    pub max_parallel: usize,
    /// When true, easy obligations are checked first (early successes).
    pub prefer_easy_first: bool,
    /// When true, dependency ordering is enforced.
    pub respect_dependencies: bool,
}

impl Default for SchedulingConfig {
    fn default() -> Self {
        Self {
            max_parallel: 4,
            prefer_easy_first: true,
            respect_dependencies: true,
        }
    }
}

/// tRust: Result of batch scheduling.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScheduleResult {
    /// Obligation IDs in priority order (flattened).
    pub ordered_ids: Vec<String>,
    /// Rough estimate of total verification time in milliseconds.
    pub estimated_total_time_ms: u64,
    /// Parallel batches: each inner Vec can be verified concurrently.
    pub parallel_batches: Vec<Vec<String>>,
}

/// tRust: Proof obligation scheduler.
///
/// Collects obligations with their priority factors, then produces
/// a prioritized ordering and parallel batch plan.
pub struct ObligationScheduler {
    config: SchedulingConfig,
    obligations: FxHashMap<String, PriorityFactors>,
}

impl ObligationScheduler {
    /// Create a new scheduler with the given configuration.
    #[must_use]
    pub fn new(config: SchedulingConfig) -> Self {
        Self {
            config,
            obligations: FxHashMap::default(),
        }
    }

    /// Add (or update) an obligation with its priority factors.
    pub fn add_obligation(&mut self, id: &str, factors: PriorityFactors) {
        self.obligations.insert(id.to_string(), factors);
    }

    /// Return all obligations sorted by priority (lowest score first).
    #[must_use]
    pub fn prioritize(&self) -> Vec<ObligationPriority> {
        let mut priorities: Vec<ObligationPriority> = self
            .obligations
            .iter()
            .map(|(id, factors)| {
                let mut score = factors.composite_score();
                // When prefer_easy_first is disabled, invert the difficulty
                // contribution so hard obligations are checked first.
                if !self.config.prefer_easy_first {
                    // Remove difficulty contribution, add inverse.
                    let difficulty_contrib = u64::from(factors.estimated_difficulty) * 3;
                    let inv_difficulty = (300u64).saturating_sub(difficulty_contrib);
                    score = score.saturating_sub(difficulty_contrib) + inv_difficulty;
                }
                ObligationPriority {
                    obligation_id: id.clone(),
                    score,
                    factors: *factors,
                }
            })
            .collect();
        priorities.sort_by_key(|p| (p.score, p.obligation_id.clone()));
        priorities
    }

    /// Estimate difficulty for a specific obligation.
    ///
    /// Returns 0 if the obligation is not registered.
    #[must_use]
    pub fn estimate_difficulty(&self, obligation_id: &str) -> u32 {
        self.obligations
            .get(obligation_id)
            .map_or(0, |f| f.estimated_difficulty)
    }

    /// Produce a topological order respecting dependencies.
    ///
    /// `deps` is a list of `(prerequisite, dependent)` pairs: the
    /// prerequisite must be verified before the dependent. Unknown IDs
    /// in `deps` are silently ignored.
    ///
    /// Returns obligations in dependency order. If `respect_dependencies`
    /// is false in the config, returns the priority-sorted order instead.
    #[must_use]
    pub fn dependency_order(&self, deps: &[(String, String)]) -> Vec<String> {
        if !self.config.respect_dependencies || deps.is_empty() {
            return self.prioritize().into_iter().map(|p| p.obligation_id).collect();
        }

        let known: FxHashSet<&str> = self.obligations.keys().map(String::as_str).collect();

        // Build adjacency list and in-degree map.
        let mut adjacency: FxHashMap<&str, Vec<&str>> = FxHashMap::default();
        let mut in_degree: FxHashMap<&str, usize> = FxHashMap::default();
        for id in &known {
            adjacency.entry(id).or_default();
            in_degree.entry(id).or_insert(0);
        }
        for (prereq, dep) in deps {
            if known.contains(prereq.as_str()) && known.contains(dep.as_str()) {
                adjacency.entry(prereq.as_str()).or_default().push(dep.as_str());
                *in_degree.entry(dep.as_str()).or_insert(0) += 1;
            }
        }

        // Kahn's algorithm with priority tie-breaking.
        let priority_map: FxHashMap<&str, u64> = self
            .prioritize()
            .into_iter()
            .filter_map(|p| {
                // We need the str reference from known, but we can use the id
                let id_str = known.iter().find(|k| **k == p.obligation_id)?;
                Some((*id_str, p.score))
            })
            .collect();

        let mut queue: VecDeque<&str> = VecDeque::new();
        let mut ready: Vec<&str> = in_degree
            .iter()
            .filter(|(_, deg)| **deg == 0)
            .map(|(&id, _)| id)
            .collect();
        ready.sort_by_key(|id| priority_map.get(id).copied().unwrap_or(u64::MAX));
        for r in ready {
            queue.push_back(r);
        }

        let mut result = Vec::with_capacity(known.len());
        while let Some(node) = queue.pop_front() {
            result.push(node.to_string());
            if let Some(neighbors) = adjacency.get(node) {
                let mut newly_ready = Vec::new();
                for &nbr in neighbors {
                    if let Some(deg) = in_degree.get_mut(nbr) {
                        *deg = deg.saturating_sub(1);
                        if *deg == 0 {
                            newly_ready.push(nbr);
                        }
                    }
                }
                newly_ready.sort_by_key(|id| priority_map.get(id).copied().unwrap_or(u64::MAX));
                for r in newly_ready {
                    queue.push_back(r);
                }
            }
        }

        // Append any obligations not reachable (cycles are broken by omission).
        for id in &known {
            if !result.iter().any(|r| r == *id) {
                result.push(id.to_string());
            }
        }
        result
    }

    /// Produce a parallel batch schedule.
    ///
    /// Groups obligations into batches of up to `max_parallel` size,
    /// ordered by priority. Each batch can be verified concurrently.
    #[must_use]
    pub fn schedule_batch(&self) -> ScheduleResult {
        let ordered = self.prioritize();
        let max = self.config.max_parallel.max(1);

        let ordered_ids: Vec<String> = ordered.iter().map(|p| p.obligation_id.clone()).collect();

        let parallel_batches: Vec<Vec<String>> = ordered_ids
            .chunks(max)
            .map(|chunk| chunk.to_vec())
            .collect();

        // Estimate: sum of difficulty * 10ms per obligation (rough heuristic).
        let estimated_total_time_ms: u64 = ordered
            .iter()
            .map(|p| u64::from(p.factors.estimated_difficulty) * 10 + 5)
            .sum();

        ScheduleResult {
            ordered_ids,
            estimated_total_time_ms,
            parallel_batches,
        }
    }

    /// Reorder obligations after a failure: boost similar obligations' priority.
    ///
    /// When an obligation fails, obligations with similar characteristics
    /// (high failure_history) should be checked sooner. This bumps the
    /// failure_history of all obligations sharing the same difficulty tier.
    pub fn reorder_on_failure(&mut self, failed_id: &str) {
        let failed_difficulty = match self.obligations.get(failed_id) {
            Some(f) => f.estimated_difficulty,
            None => return,
        };

        // Bump failure history for obligations in the same difficulty tier
        // (within +/- 10 of the failed obligation's difficulty).
        let tier_lo = failed_difficulty.saturating_sub(10);
        let tier_hi = failed_difficulty.saturating_add(10);

        for (id, factors) in &mut self.obligations {
            if id == failed_id {
                factors.failure_history = factors.failure_history.saturating_add(5);
            } else if factors.estimated_difficulty >= tier_lo
                && factors.estimated_difficulty <= tier_hi
            {
                factors.failure_history = factors.failure_history.saturating_add(2);
            }
        }
    }

    /// Return the number of registered obligations.
    #[must_use]
    pub fn obligation_count(&self) -> usize {
        self.obligations.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_factors(difficulty: u32, depth: u32, cache: u32, failures: u32, size: u32) -> PriorityFactors {
        PriorityFactors {
            estimated_difficulty: difficulty,
            dependency_depth: depth,
            cache_likelihood: cache,
            failure_history: failures,
            size_score: size,
        }
    }

    #[test]
    fn test_priority_factors_composite_score_basic() {
        let f = make_factors(10, 0, 0, 0, 0);
        assert_eq!(f.composite_score(), 30); // 10*3
    }

    #[test]
    fn test_priority_factors_composite_score_with_all_fields() {
        let f = make_factors(10, 2, 5, 3, 4);
        // base = 10*3 + 2*5 + 4*2 = 30 + 10 + 8 = 48
        // reduction = 3*4 + 5*2 = 12 + 10 = 22
        // score = 48 - 22 = 26
        assert_eq!(f.composite_score(), 26);
    }

    #[test]
    fn test_priority_factors_saturating_sub() {
        // High failure + cache can reduce score to zero, not underflow.
        let f = make_factors(0, 0, 100, 100, 0);
        assert_eq!(f.composite_score(), 0);
    }

    #[test]
    fn test_scheduler_new_empty() {
        let s = ObligationScheduler::new(SchedulingConfig::default());
        assert_eq!(s.obligation_count(), 0);
    }

    #[test]
    fn test_scheduler_add_and_count() {
        let mut s = ObligationScheduler::new(SchedulingConfig::default());
        s.add_obligation("a", make_factors(10, 0, 0, 0, 0));
        s.add_obligation("b", make_factors(20, 0, 0, 0, 0));
        assert_eq!(s.obligation_count(), 2);
    }

    #[test]
    fn test_scheduler_add_overwrites() {
        let mut s = ObligationScheduler::new(SchedulingConfig::default());
        s.add_obligation("a", make_factors(10, 0, 0, 0, 0));
        s.add_obligation("a", make_factors(50, 0, 0, 0, 0));
        assert_eq!(s.obligation_count(), 1);
        assert_eq!(s.estimate_difficulty("a"), 50);
    }

    #[test]
    fn test_prioritize_orders_by_score() {
        let mut s = ObligationScheduler::new(SchedulingConfig::default());
        s.add_obligation("hard", make_factors(90, 0, 0, 0, 0));
        s.add_obligation("easy", make_factors(5, 0, 0, 0, 0));
        s.add_obligation("medium", make_factors(40, 0, 0, 0, 0));

        let priorities = s.prioritize();
        assert_eq!(priorities[0].obligation_id, "easy");
        assert_eq!(priorities[1].obligation_id, "medium");
        assert_eq!(priorities[2].obligation_id, "hard");
    }

    #[test]
    fn test_prioritize_prefer_hard_first() {
        let config = SchedulingConfig {
            prefer_easy_first: false,
            ..SchedulingConfig::default()
        };
        let mut s = ObligationScheduler::new(config);
        s.add_obligation("hard", make_factors(90, 0, 0, 0, 0));
        s.add_obligation("easy", make_factors(5, 0, 0, 0, 0));

        let priorities = s.prioritize();
        // With prefer_easy_first=false, hard should come before easy.
        assert_eq!(priorities[0].obligation_id, "hard");
        assert_eq!(priorities[1].obligation_id, "easy");
    }

    #[test]
    fn test_estimate_difficulty_known() {
        let mut s = ObligationScheduler::new(SchedulingConfig::default());
        s.add_obligation("x", make_factors(42, 0, 0, 0, 0));
        assert_eq!(s.estimate_difficulty("x"), 42);
    }

    #[test]
    fn test_estimate_difficulty_unknown() {
        let s = ObligationScheduler::new(SchedulingConfig::default());
        assert_eq!(s.estimate_difficulty("nonexistent"), 0);
    }

    #[test]
    fn test_dependency_order_no_deps() {
        let mut s = ObligationScheduler::new(SchedulingConfig::default());
        s.add_obligation("a", make_factors(50, 0, 0, 0, 0));
        s.add_obligation("b", make_factors(10, 0, 0, 0, 0));

        let order = s.dependency_order(&[]);
        // Should be priority order: b (score 30) before a (score 150).
        assert_eq!(order[0], "b");
        assert_eq!(order[1], "a");
    }

    #[test]
    fn test_dependency_order_with_deps() {
        let mut s = ObligationScheduler::new(SchedulingConfig::default());
        // b is easy but depends on a.
        s.add_obligation("a", make_factors(50, 0, 0, 0, 0));
        s.add_obligation("b", make_factors(10, 0, 0, 0, 0));

        let deps = vec![("a".to_string(), "b".to_string())];
        let order = s.dependency_order(&deps);
        // a must come before b even though b has lower score.
        let a_pos = order.iter().position(|x| x == "a").unwrap();
        let b_pos = order.iter().position(|x| x == "b").unwrap();
        assert!(a_pos < b_pos, "prerequisite a must come before dependent b");
    }

    #[test]
    fn test_dependency_order_respect_dependencies_false() {
        let config = SchedulingConfig {
            respect_dependencies: false,
            ..SchedulingConfig::default()
        };
        let mut s = ObligationScheduler::new(config);
        s.add_obligation("a", make_factors(50, 0, 0, 0, 0));
        s.add_obligation("b", make_factors(10, 0, 0, 0, 0));

        let deps = vec![("a".to_string(), "b".to_string())];
        let order = s.dependency_order(&deps);
        // Should ignore deps and use priority order.
        assert_eq!(order[0], "b");
    }

    #[test]
    fn test_schedule_batch_creates_batches() {
        let config = SchedulingConfig {
            max_parallel: 2,
            ..SchedulingConfig::default()
        };
        let mut s = ObligationScheduler::new(config);
        s.add_obligation("a", make_factors(10, 0, 0, 0, 0));
        s.add_obligation("b", make_factors(20, 0, 0, 0, 0));
        s.add_obligation("c", make_factors(30, 0, 0, 0, 0));

        let result = s.schedule_batch();
        assert_eq!(result.ordered_ids.len(), 3);
        assert_eq!(result.parallel_batches.len(), 2); // ceil(3/2)
        assert_eq!(result.parallel_batches[0].len(), 2);
        assert_eq!(result.parallel_batches[1].len(), 1);
        assert!(result.estimated_total_time_ms > 0);
    }

    #[test]
    fn test_schedule_batch_empty() {
        let s = ObligationScheduler::new(SchedulingConfig::default());
        let result = s.schedule_batch();
        assert!(result.ordered_ids.is_empty());
        assert!(result.parallel_batches.is_empty());
        assert_eq!(result.estimated_total_time_ms, 0);
    }

    #[test]
    fn test_reorder_on_failure_bumps_similar() {
        let mut s = ObligationScheduler::new(SchedulingConfig::default());
        s.add_obligation("a", make_factors(50, 0, 0, 0, 0));
        s.add_obligation("b", make_factors(55, 0, 0, 0, 0)); // same tier
        s.add_obligation("c", make_factors(90, 0, 0, 0, 0)); // different tier

        s.reorder_on_failure("a");

        // a gets +5 failure_history, b gets +2 (same tier), c unchanged.
        let priorities = s.prioritize();
        let a = priorities.iter().find(|p| p.obligation_id == "a").unwrap();
        let b = priorities.iter().find(|p| p.obligation_id == "b").unwrap();
        let c = priorities.iter().find(|p| p.obligation_id == "c").unwrap();

        assert_eq!(a.factors.failure_history, 5);
        assert_eq!(b.factors.failure_history, 2);
        assert_eq!(c.factors.failure_history, 0);
    }

    #[test]
    fn test_reorder_on_failure_unknown_id_noop() {
        let mut s = ObligationScheduler::new(SchedulingConfig::default());
        s.add_obligation("a", make_factors(50, 0, 0, 0, 0));
        s.reorder_on_failure("nonexistent");
        // Should not panic or change anything.
        assert_eq!(s.estimate_difficulty("a"), 50);
    }

    #[test]
    fn test_scheduling_config_default() {
        let config = SchedulingConfig::default();
        assert_eq!(config.max_parallel, 4);
        assert!(config.prefer_easy_first);
        assert!(config.respect_dependencies);
    }

    #[test]
    fn test_failure_history_lowers_score() {
        let mut s = ObligationScheduler::new(SchedulingConfig::default());
        s.add_obligation("with_failures", make_factors(50, 0, 0, 10, 0));
        s.add_obligation("no_failures", make_factors(50, 0, 0, 0, 0));

        let priorities = s.prioritize();
        // with_failures should have lower score (checked sooner).
        let wf = priorities.iter().find(|p| p.obligation_id == "with_failures").unwrap();
        let nf = priorities.iter().find(|p| p.obligation_id == "no_failures").unwrap();
        assert!(wf.score < nf.score, "failure history should reduce score for earlier checking");
    }

    #[test]
    fn test_cache_likelihood_lowers_score() {
        let mut s = ObligationScheduler::new(SchedulingConfig::default());
        s.add_obligation("cached", make_factors(50, 0, 80, 0, 0));
        s.add_obligation("not_cached", make_factors(50, 0, 0, 0, 0));

        let priorities = s.prioritize();
        let cached = priorities.iter().find(|p| p.obligation_id == "cached").unwrap();
        let not_cached = priorities.iter().find(|p| p.obligation_id == "not_cached").unwrap();
        assert!(cached.score < not_cached.score, "cache likelihood should reduce score");
    }
}
