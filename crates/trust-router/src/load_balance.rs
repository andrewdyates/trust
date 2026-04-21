// trust-router/load_balance.rs: Solver load balancing for proof throughput
//
// tRust #284: Distributes proof obligations across solver backends based on
// current load, historical performance, and solver capabilities. Supports
// round-robin, least-loaded, capability-based, and adaptive strategies.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::fmt;
use std::time::Duration;

use trust_types::{ProofLevel, VerificationCondition};

use crate::BackendRole;

/// tRust: Per-solver load and performance tracking.
#[derive(Debug, Clone, PartialEq)]
pub struct SolverLoad {
    /// Solver backend name.
    pub name: String,
    /// Role advertised by this backend.
    pub role: BackendRole,
    /// Number of obligations currently in-flight.
    pub active_obligations: u64,
    /// Maximum concurrent obligations this solver should handle.
    pub capacity: u64,
    /// Total obligations completed (lifetime).
    pub completed: u64,
    /// Total obligations that failed or timed out (lifetime).
    pub failures: u64,
    /// Cumulative solve time in milliseconds (for computing averages).
    pub total_solve_time_ms: f64,
    /// Average solve time in milliseconds (exponential moving average).
    pub avg_solve_time_ms: f64,
    /// Success rate as a fraction [0.0, 1.0].
    pub success_rate: f64,
}

impl SolverLoad {
    /// Create a new solver load tracker.
    #[must_use]
    pub fn new(name: impl Into<String>, role: BackendRole, capacity: u64) -> Self {
        Self {
            name: name.into(),
            role,
            active_obligations: 0,
            capacity,
            completed: 0,
            failures: 0,
            total_solve_time_ms: 0.0,
            avg_solve_time_ms: 0.0,
            success_rate: 1.0,
        }
    }

    /// Utilization as a fraction [0.0, 1.0].
    #[must_use]
    pub fn utilization(&self) -> f64 {
        if self.capacity == 0 {
            return 1.0;
        }
        self.active_obligations as f64 / self.capacity as f64
    }

    /// Whether this solver has remaining capacity.
    #[must_use]
    pub fn has_capacity(&self) -> bool {
        self.active_obligations < self.capacity
    }

    /// Total obligations attempted (completed + failures).
    #[must_use]
    pub fn total_attempted(&self) -> u64 {
        self.completed + self.failures
    }
}

/// tRust: Strategy for distributing obligations across solvers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BalancingStrategy {
    /// Cycle through solvers in order, regardless of load.
    RoundRobin,
    /// Always pick the solver with the fewest active obligations.
    LeastLoaded,
    /// Pick the solver best suited to the VC's proof level and kind.
    CapabilityBased,
    /// Combine capability matching with load awareness and historical
    /// performance to pick the optimal solver.
    Adaptive,
}

impl BalancingStrategy {
    /// Human-readable name.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::RoundRobin => "round-robin",
            Self::LeastLoaded => "least-loaded",
            Self::CapabilityBased => "capability-based",
            Self::Adaptive => "adaptive",
        }
    }
}

/// tRust: Load balancer distributing proof obligations across solver backends.
pub struct LoadBalancer {
    /// Per-solver load state, keyed by solver name.
    solvers: FxHashMap<String, SolverLoad>,
    /// Ordered solver names for round-robin.
    solver_order: Vec<String>,
    /// Current round-robin index.
    rr_index: usize,
    /// Active balancing strategy.
    strategy: BalancingStrategy,
    /// Exponential moving average smoothing factor for solve time (0.0..=1.0).
    /// Higher values weight recent observations more heavily.
    ema_alpha: f64,
}

impl LoadBalancer {
    /// Create a load balancer with the given strategy.
    #[must_use]
    pub fn new(strategy: BalancingStrategy) -> Self {
        Self {
            solvers: FxHashMap::default(),
            solver_order: Vec::new(),
            rr_index: 0,
            strategy,
            ema_alpha: 0.3,
        }
    }

    /// Register a solver backend with its role and capacity.
    pub fn register_solver(
        &mut self,
        name: impl Into<String>,
        role: BackendRole,
        capacity: u64,
    ) {
        let name = name.into();
        if !self.solvers.contains_key(&name) {
            self.solver_order.push(name.clone());
        }
        self.solvers.insert(name.clone(), SolverLoad::new(name, role, capacity));
    }

    /// Get the current balancing strategy.
    #[must_use]
    pub fn strategy(&self) -> BalancingStrategy {
        self.strategy
    }

    /// Set a new balancing strategy.
    pub fn set_strategy(&mut self, strategy: BalancingStrategy) {
        self.strategy = strategy;
    }

    /// Number of registered solvers.
    #[must_use]
    pub fn solver_count(&self) -> usize {
        self.solvers.len()
    }

    /// Get load state for a specific solver.
    #[must_use]
    pub fn solver_load(&self, name: &str) -> Option<&SolverLoad> {
        self.solvers.get(name)
    }

    /// Assign a verification condition to the best available solver.
    ///
    /// Returns the solver name, or `None` if no solver is available.
    /// Increments the active obligation count for the chosen solver.
    pub fn assign_obligation(&mut self, vc: &VerificationCondition) -> Option<String> {
        if self.solvers.is_empty() {
            return None;
        }

        let chosen = match self.strategy {
            BalancingStrategy::RoundRobin => self.pick_round_robin(),
            BalancingStrategy::LeastLoaded => self.pick_least_loaded(),
            BalancingStrategy::CapabilityBased => self.pick_capability_based(vc),
            BalancingStrategy::Adaptive => self.pick_adaptive(vc),
        };

        if let Some(ref name) = chosen
            && let Some(load) = self.solvers.get_mut(name) {
                load.active_obligations += 1;
            }

        chosen
    }

    /// Update metrics after a solver completes an obligation.
    ///
    /// `success`: whether the solver produced a definitive result (proved or
    /// disproved). `solve_time`: wall-clock time the solver spent.
    pub fn update_metrics(
        &mut self,
        solver_name: &str,
        success: bool,
        solve_time: Duration,
    ) {
        if let Some(load) = self.solvers.get_mut(solver_name) {
            load.active_obligations = load.active_obligations.saturating_sub(1);

            let time_ms = solve_time.as_secs_f64() * 1000.0;
            load.total_solve_time_ms += time_ms;

            if success {
                load.completed += 1;
            } else {
                load.failures += 1;
            }

            // Update exponential moving average of solve time.
            if load.total_attempted() == 1 {
                load.avg_solve_time_ms = time_ms;
            } else {
                load.avg_solve_time_ms =
                    self.ema_alpha * time_ms + (1.0 - self.ema_alpha) * load.avg_solve_time_ms;
            }

            // Update success rate.
            let total = load.total_attempted();
            if total > 0 {
                load.success_rate = load.completed as f64 / total as f64;
            }
        }
    }

    /// Rebalance assignments based on observed performance.
    ///
    /// Adjusts capacity for underperforming solvers (low success rate or
    /// high latency) and increases capacity for well-performing ones.
    /// Returns the number of solvers whose capacity was adjusted.
    pub fn rebalance(&mut self) -> usize {
        let mut adjusted = 0;

        // Compute mean success rate and mean latency across all solvers with data.
        let solvers_with_data: Vec<(String, f64, f64)> = self
            .solvers
            .values()
            .filter(|s| s.total_attempted() > 0)
            .map(|s| (s.name.clone(), s.success_rate, s.avg_solve_time_ms))
            .collect();

        if solvers_with_data.is_empty() {
            return 0;
        }

        let mean_success: f64 =
            solvers_with_data.iter().map(|(_, sr, _)| sr).sum::<f64>()
                / solvers_with_data.len() as f64;
        let mean_latency: f64 =
            solvers_with_data.iter().map(|(_, _, lat)| lat).sum::<f64>()
                / solvers_with_data.len() as f64;

        for (name, success_rate, avg_latency) in &solvers_with_data {
            let load = match self.solvers.get_mut(name.as_str()) {
                Some(l) => l,
                None => continue,
            };

            let original_capacity = load.capacity;

            // Reduce capacity for underperformers.
            if *success_rate < mean_success * 0.8 || *avg_latency > mean_latency * 2.0 {
                load.capacity = (load.capacity * 3 / 4).max(1);
            }
            // Increase capacity for strong performers.
            else if *success_rate > mean_success * 1.1 && *avg_latency < mean_latency * 0.5 {
                load.capacity = load.capacity * 5 / 4 + 1;
            }

            if load.capacity != original_capacity {
                adjusted += 1;
            }
        }

        adjusted
    }

    /// Generate a load report summarizing solver utilization.
    #[must_use]
    pub fn load_report(&self) -> LoadReport {
        let solver_reports: Vec<SolverReport> = self
            .solver_order
            .iter()
            .filter_map(|name| self.solvers.get(name))
            .map(|load| SolverReport {
                name: load.name.clone(),
                role: load.role,
                active: load.active_obligations,
                capacity: load.capacity,
                utilization: load.utilization(),
                completed: load.completed,
                failures: load.failures,
                avg_solve_time_ms: load.avg_solve_time_ms,
                success_rate: load.success_rate,
            })
            .collect();

        let total_active: u64 = solver_reports.iter().map(|s| s.active).sum();
        let total_capacity: u64 = solver_reports.iter().map(|s| s.capacity).sum();
        let overall_utilization = if total_capacity == 0 {
            0.0
        } else {
            total_active as f64 / total_capacity as f64
        };

        LoadReport {
            strategy: self.strategy,
            solver_count: self.solvers.len(),
            total_active,
            total_capacity,
            overall_utilization,
            solvers: solver_reports,
        }
    }

    // --- Private strategy implementations ---

    fn pick_round_robin(&mut self) -> Option<String> {
        if self.solver_order.is_empty() {
            return None;
        }
        let start = self.rr_index;
        let len = self.solver_order.len();

        // Try each solver starting from current index, wrapping around.
        for offset in 0..len {
            let idx = (start + offset) % len;
            let name = &self.solver_order[idx];
            if let Some(load) = self.solvers.get(name)
                && load.has_capacity() {
                    self.rr_index = (idx + 1) % len;
                    return Some(name.clone());
                }
        }

        // All at capacity — fall back to the next in line anyway.
        let name = self.solver_order[start % len].clone();
        self.rr_index = (start + 1) % len;
        Some(name)
    }

    fn pick_least_loaded(&self) -> Option<String> {
        self.solvers
            .values()
            .min_by(|a, b| {
                a.utilization()
                    .partial_cmp(&b.utilization())
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
            .map(|load| load.name.clone())
    }

    fn pick_capability_based(&self, vc: &VerificationCondition) -> Option<String> {
        let level = vc.kind.proof_level();
        let preferred_roles = preferred_roles_for_level(level);

        // Try each preferred role in priority order.
        for role in &preferred_roles {
            let candidate = self
                .solvers
                .values()
                .filter(|s| s.role == *role && s.has_capacity())
                .min_by(|a, b| {
                    a.active_obligations
                        .cmp(&b.active_obligations)
                });
            if let Some(s) = candidate {
                return Some(s.name.clone());
            }
        }

        // Fall back to any solver with capacity.
        self.solvers
            .values()
            .filter(|s| s.has_capacity())
            .min_by_key(|s| s.active_obligations)
            .map(|s| s.name.clone())
            // Absolute fallback: least loaded even if over capacity.
            .or_else(|| self.pick_least_loaded())
    }

    fn pick_adaptive(&self, vc: &VerificationCondition) -> Option<String> {
        let level = vc.kind.proof_level();
        let preferred_roles = preferred_roles_for_level(level);

        // Score each solver: lower is better.
        let mut scored: Vec<(String, f64)> = self
            .solvers
            .values()
            .map(|s| {
                let mut score = 0.0_f64;

                // Role match bonus (lower score = better).
                let role_penalty = if let Some(pos) =
                    preferred_roles.iter().position(|r| *r == s.role)
                {
                    pos as f64 * 10.0
                } else {
                    100.0
                };
                score += role_penalty;

                // Load penalty: heavily penalize overloaded solvers.
                score += s.utilization() * 50.0;

                // Latency penalty.
                score += s.avg_solve_time_ms * 0.1;

                // Success rate bonus (invert: high success = low penalty).
                score += (1.0 - s.success_rate) * 30.0;

                // Capacity exhaustion penalty.
                if !s.has_capacity() {
                    score += 200.0;
                }

                (s.name.clone(), score)
            })
            .collect();

        scored.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));
        scored.first().map(|(name, _)| name.clone())
    }
}

/// tRust: Summary report of solver utilization across the load balancer.
#[derive(Debug, Clone, PartialEq)]
pub struct LoadReport {
    /// Active balancing strategy.
    pub strategy: BalancingStrategy,
    /// Number of registered solvers.
    pub solver_count: usize,
    /// Total in-flight obligations across all solvers.
    pub total_active: u64,
    /// Total capacity across all solvers.
    pub total_capacity: u64,
    /// Overall utilization [0.0, 1.0].
    pub overall_utilization: f64,
    /// Per-solver utilization details.
    pub solvers: Vec<SolverReport>,
}

impl fmt::Display for LoadReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Load Balancer Report ===")?;
        writeln!(f, "Strategy:     {}", self.strategy.name())?;
        writeln!(f, "Solvers:      {}", self.solver_count)?;
        writeln!(f, "Active/Cap:   {}/{}", self.total_active, self.total_capacity)?;
        writeln!(f, "Utilization:  {:.1}%", self.overall_utilization * 100.0)?;

        for solver in &self.solvers {
            writeln!(f)?;
            writeln!(f, "--- {} ({:?}) ---", solver.name, solver.role)?;
            writeln!(f, "  Active/Cap:    {}/{}", solver.active, solver.capacity)?;
            writeln!(f, "  Utilization:   {:.1}%", solver.utilization * 100.0)?;
            writeln!(f, "  Completed:     {}", solver.completed)?;
            writeln!(f, "  Failures:      {}", solver.failures)?;
            writeln!(f, "  Avg solve:     {:.1}ms", solver.avg_solve_time_ms)?;
            writeln!(f, "  Success rate:  {:.1}%", solver.success_rate * 100.0)?;
        }

        Ok(())
    }
}

/// tRust: Per-solver detail in a load report.
#[derive(Debug, Clone, PartialEq)]
pub struct SolverReport {
    pub name: String,
    pub role: BackendRole,
    pub active: u64,
    pub capacity: u64,
    pub utilization: f64,
    pub completed: u64,
    pub failures: u64,
    pub avg_solve_time_ms: f64,
    pub success_rate: f64,
}

/// Return the preferred `BackendRole` order for a given proof level.
fn preferred_roles_for_level(level: ProofLevel) -> Vec<BackendRole> {
    match level {
        ProofLevel::L0Safety => vec![
            BackendRole::SmtSolver,
            BackendRole::BoundedModelChecker,
            BackendRole::Cegar,
            BackendRole::Deductive,
        ],
        ProofLevel::L1Functional => vec![
            BackendRole::Deductive,
            BackendRole::Cegar,
            BackendRole::SmtSolver,
            BackendRole::BoundedModelChecker,
        ],
        ProofLevel::L2Domain => vec![
            BackendRole::Temporal,
            BackendRole::Deductive,
            BackendRole::Cegar,
        ],
        _ => vec![],
    }
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    fn safety_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        }
    }

    fn postcondition_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "post_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn temporal_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Temporal {
                property: "eventually done".to_string(),
            },
            function: "temporal_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn make_balancer() -> LoadBalancer {
        let mut lb = LoadBalancer::new(BalancingStrategy::RoundRobin);
        lb.register_solver("z4", BackendRole::SmtSolver, 10);
        lb.register_solver("zani", BackendRole::BoundedModelChecker, 8);
        lb.register_solver("sunder", BackendRole::Deductive, 6);
        lb
    }

    // -----------------------------------------------------------------------
    // Test 1: SolverLoad basics
    // -----------------------------------------------------------------------

    #[test]
    fn test_solver_load_new_and_utilization() {
        let load = SolverLoad::new("z4", BackendRole::SmtSolver, 10);
        assert_eq!(load.name, "z4");
        assert_eq!(load.role, BackendRole::SmtSolver);
        assert_eq!(load.capacity, 10);
        assert_eq!(load.active_obligations, 0);
        assert_eq!(load.utilization(), 0.0);
        assert!(load.has_capacity());
        assert_eq!(load.total_attempted(), 0);

        let full = SolverLoad {
            active_obligations: 10,
            ..SolverLoad::new("full", BackendRole::General, 10)
        };
        assert!((full.utilization() - 1.0).abs() < f64::EPSILON);
        assert!(!full.has_capacity());
    }

    // -----------------------------------------------------------------------
    // Test 2: Zero-capacity solver
    // -----------------------------------------------------------------------

    #[test]
    fn test_solver_load_zero_capacity() {
        let load = SolverLoad::new("empty", BackendRole::General, 0);
        assert_eq!(load.utilization(), 1.0);
        assert!(!load.has_capacity());
    }

    // -----------------------------------------------------------------------
    // Test 3: BalancingStrategy names
    // -----------------------------------------------------------------------

    #[test]
    fn test_balancing_strategy_names() {
        assert_eq!(BalancingStrategy::RoundRobin.name(), "round-robin");
        assert_eq!(BalancingStrategy::LeastLoaded.name(), "least-loaded");
        assert_eq!(BalancingStrategy::CapabilityBased.name(), "capability-based");
        assert_eq!(BalancingStrategy::Adaptive.name(), "adaptive");
    }

    // -----------------------------------------------------------------------
    // Test 4: Round-robin assignment cycles through solvers
    // -----------------------------------------------------------------------

    #[test]
    fn test_round_robin_cycles_through_solvers() {
        let mut lb = make_balancer();
        let vc = safety_vc();

        let first = lb.assign_obligation(&vc).unwrap();
        let second = lb.assign_obligation(&vc).unwrap();
        let third = lb.assign_obligation(&vc).unwrap();
        let fourth = lb.assign_obligation(&vc).unwrap();

        assert_eq!(first, "z4");
        assert_eq!(second, "zani");
        assert_eq!(third, "sunder");
        // Wraps back to z4.
        assert_eq!(fourth, "z4");
    }

    // -----------------------------------------------------------------------
    // Test 5: Least-loaded picks the solver with lowest utilization
    // -----------------------------------------------------------------------

    #[test]
    fn test_least_loaded_picks_lowest_utilization() {
        let mut lb = LoadBalancer::new(BalancingStrategy::LeastLoaded);
        lb.register_solver("z4", BackendRole::SmtSolver, 10);
        lb.register_solver("zani", BackendRole::BoundedModelChecker, 10);
        lb.register_solver("sunder", BackendRole::Deductive, 10);

        // Give z4 and sunder some load.
        lb.solvers.get_mut("z4").unwrap().active_obligations = 5;
        lb.solvers.get_mut("sunder").unwrap().active_obligations = 3;
        // zani has 0 active — should be picked.

        let chosen = lb.assign_obligation(&safety_vc()).unwrap();
        assert_eq!(chosen, "zani");
    }

    // -----------------------------------------------------------------------
    // Test 6: Capability-based picks SMT for safety VCs
    // -----------------------------------------------------------------------

    #[test]
    fn test_capability_based_prefers_smt_for_safety() {
        let mut lb = LoadBalancer::new(BalancingStrategy::CapabilityBased);
        lb.register_solver("sunder", BackendRole::Deductive, 10);
        lb.register_solver("z4", BackendRole::SmtSolver, 10);
        lb.register_solver("tla2", BackendRole::Temporal, 10);

        let chosen = lb.assign_obligation(&safety_vc()).unwrap();
        assert_eq!(chosen, "z4", "SMT solver should be preferred for L0Safety");
    }

    // -----------------------------------------------------------------------
    // Test 7: Capability-based picks deductive for postcondition VCs
    // -----------------------------------------------------------------------

    #[test]
    fn test_capability_based_prefers_deductive_for_postcondition() {
        let mut lb = LoadBalancer::new(BalancingStrategy::CapabilityBased);
        lb.register_solver("z4", BackendRole::SmtSolver, 10);
        lb.register_solver("sunder", BackendRole::Deductive, 10);
        lb.register_solver("tla2", BackendRole::Temporal, 10);

        let chosen = lb.assign_obligation(&postcondition_vc()).unwrap();
        assert_eq!(chosen, "sunder", "Deductive solver should be preferred for L1Functional");
    }

    // -----------------------------------------------------------------------
    // Test 8: Capability-based picks temporal for temporal VCs
    // -----------------------------------------------------------------------

    #[test]
    fn test_capability_based_prefers_temporal_for_temporal_vc() {
        let mut lb = LoadBalancer::new(BalancingStrategy::CapabilityBased);
        lb.register_solver("z4", BackendRole::SmtSolver, 10);
        lb.register_solver("sunder", BackendRole::Deductive, 10);
        lb.register_solver("tla2", BackendRole::Temporal, 10);

        let chosen = lb.assign_obligation(&temporal_vc()).unwrap();
        assert_eq!(chosen, "tla2", "Temporal solver should be preferred for L2Domain");
    }

    // -----------------------------------------------------------------------
    // Test 9: update_metrics adjusts solver state
    // -----------------------------------------------------------------------

    #[test]
    fn test_update_metrics_adjusts_solver_state() {
        let mut lb = make_balancer();
        let vc = safety_vc();

        // Assign and then complete.
        let solver = lb.assign_obligation(&vc).unwrap();
        assert_eq!(lb.solver_load(&solver).unwrap().active_obligations, 1);

        lb.update_metrics(&solver, true, Duration::from_millis(50));

        let load = lb.solver_load(&solver).unwrap();
        assert_eq!(load.active_obligations, 0);
        assert_eq!(load.completed, 1);
        assert_eq!(load.failures, 0);
        assert!((load.success_rate - 1.0).abs() < f64::EPSILON);
        assert!(load.avg_solve_time_ms > 0.0);
    }

    // -----------------------------------------------------------------------
    // Test 10: update_metrics tracks failures
    // -----------------------------------------------------------------------

    #[test]
    fn test_update_metrics_tracks_failures() {
        let mut lb = make_balancer();
        let vc = safety_vc();

        let solver = lb.assign_obligation(&vc).unwrap();
        lb.update_metrics(&solver, false, Duration::from_millis(100));

        let load = lb.solver_load(&solver).unwrap();
        assert_eq!(load.completed, 0);
        assert_eq!(load.failures, 1);
        assert_eq!(load.success_rate, 0.0);
    }

    // -----------------------------------------------------------------------
    // Test 11: rebalance adjusts capacity for underperformers
    // -----------------------------------------------------------------------

    #[test]
    fn test_rebalance_adjusts_capacity() {
        let mut lb = LoadBalancer::new(BalancingStrategy::Adaptive);
        lb.register_solver("fast", BackendRole::SmtSolver, 10);
        lb.register_solver("slow", BackendRole::SmtSolver, 10);

        // Simulate: "fast" completes quickly with high success.
        for _ in 0..10 {
            lb.update_metrics("fast", true, Duration::from_millis(10));
        }

        // Simulate: "slow" is slow and fails often.
        for _ in 0..5 {
            lb.update_metrics("slow", false, Duration::from_millis(500));
        }
        for _ in 0..5 {
            lb.update_metrics("slow", true, Duration::from_millis(500));
        }

        let adjusted = lb.rebalance();
        assert!(adjusted > 0, "rebalance should adjust at least one solver");

        let fast_cap = lb.solver_load("fast").unwrap().capacity;
        let slow_cap = lb.solver_load("slow").unwrap().capacity;
        assert!(
            fast_cap >= slow_cap,
            "fast solver should have >= capacity than slow: fast={fast_cap}, slow={slow_cap}"
        );
    }

    // -----------------------------------------------------------------------
    // Test 12: load_report produces accurate summary
    // -----------------------------------------------------------------------

    #[test]
    fn test_load_report_summary() {
        let mut lb = make_balancer();
        let vc = safety_vc();

        lb.assign_obligation(&vc);
        lb.assign_obligation(&vc);

        let report = lb.load_report();
        assert_eq!(report.strategy, BalancingStrategy::RoundRobin);
        assert_eq!(report.solver_count, 3);
        assert_eq!(report.total_active, 2);
        assert_eq!(report.total_capacity, 10 + 8 + 6);
        assert!(report.overall_utilization > 0.0);
        assert_eq!(report.solvers.len(), 3);

        // Report Display should not panic.
        let display = format!("{report}");
        assert!(display.contains("Load Balancer Report"));
        assert!(display.contains("round-robin"));
    }

    // -----------------------------------------------------------------------
    // Test 13: Adaptive strategy considers both capability and load
    // -----------------------------------------------------------------------

    #[test]
    fn test_adaptive_balances_capability_and_load() {
        let mut lb = LoadBalancer::new(BalancingStrategy::Adaptive);
        lb.register_solver("z4", BackendRole::SmtSolver, 10);
        lb.register_solver("zani", BackendRole::BoundedModelChecker, 10);

        // Give z4 good performance history.
        for _ in 0..5 {
            lb.update_metrics("z4", true, Duration::from_millis(10));
        }
        // Give zani poor performance.
        for _ in 0..5 {
            lb.update_metrics("zani", false, Duration::from_millis(500));
        }

        // For a safety VC, adaptive should prefer z4 (matching role + better perf).
        let chosen = lb.assign_obligation(&safety_vc()).unwrap();
        assert_eq!(chosen, "z4");
    }

    // -----------------------------------------------------------------------
    // Test 14: Empty balancer returns None
    // -----------------------------------------------------------------------

    #[test]
    fn test_empty_balancer_returns_none() {
        let mut lb = LoadBalancer::new(BalancingStrategy::RoundRobin);
        assert!(lb.assign_obligation(&safety_vc()).is_none());
        assert_eq!(lb.load_report().solver_count, 0);
    }

    // -----------------------------------------------------------------------
    // Test 15: set_strategy changes behavior
    // -----------------------------------------------------------------------

    #[test]
    fn test_set_strategy_changes_behavior() {
        let mut lb = make_balancer();
        assert_eq!(lb.strategy(), BalancingStrategy::RoundRobin);

        lb.set_strategy(BalancingStrategy::LeastLoaded);
        assert_eq!(lb.strategy(), BalancingStrategy::LeastLoaded);
    }

    // -----------------------------------------------------------------------
    // Test 16: rebalance with no data is a no-op
    // -----------------------------------------------------------------------

    #[test]
    fn test_rebalance_no_data_is_noop() {
        let mut lb = make_balancer();
        let adjusted = lb.rebalance();
        assert_eq!(adjusted, 0, "no adjustments without performance data");
    }
}
