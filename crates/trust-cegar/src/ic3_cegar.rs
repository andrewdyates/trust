// trust-cegar: IC3-CEGAR integration bridge
//
// Bridges the IC3/PDR engine with the CEGAR refinement loop by:
// 1. Running IC3 on the current abstraction
// 2. Checking whether counterexamples are spurious under learned clauses
// 3. Extracting predicate candidates from spurious traces
// 4. Strengthening future IC3 runs with those learned clauses
//
// The current IC3 engine exposes a closed `check()` interface, so this bridge
// persists refinement information across fresh IC3 rounds by rebuilding the
// checked property from learned frame clauses.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::Formula;

use crate::error::CegarError;
use crate::ic3::{Cube, Frame, Ic3Config, Ic3Engine, Ic3Result, TransitionSystem};

/// Priority used when consuming proof obligations from an IC3 counterexample.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[non_exhaustive]
#[allow(clippy::enum_variant_names)]
pub(crate) enum ObligationPriority {
    /// Prioritize the deepest obligations first (IC3's natural blocking order).
    #[default]
    DepthFirst,
    /// Prioritize shallower obligations first.
    BreadthFirst,
    /// Prioritize obligations with the fewest literals first.
    SmallestCubeFirst,
}

/// Configuration for the IC3-CEGAR bridge.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Ic3CegarConfig {
    /// Maximum IC3 frame depth for each round.
    pub(crate) max_ic3_depth: usize,
    /// Maximum number of CEGAR refinement rounds.
    pub(crate) max_cegar_rounds: usize,
    /// Whether to split conjunctions into interpolation-like predicate atoms.
    pub(crate) use_interpolation: bool,
    /// Heuristic for consuming counterexample obligations during refinement.
    pub(crate) obligation_priority: ObligationPriority,
}

impl Default for Ic3CegarConfig {
    fn default() -> Self {
        Self {
            max_ic3_depth: 100,
            max_cegar_rounds: 50,
            use_interpolation: true,
            obligation_priority: ObligationPriority::DepthFirst,
        }
    }
}

/// Execution statistics for the IC3-CEGAR bridge.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Ic3Stats {
    /// Total IC3 frames explored across all rounds.
    pub(crate) ic3_frames_explored: usize,
    /// Number of trace-derived cubes learned during refinement.
    pub(crate) cubes_blocked: usize,
    /// Number of learned clauses copied into frames.
    pub(crate) clauses_propagated: usize,
    /// Number of successful CEGAR refinements performed.
    pub(crate) cegar_refinements: usize,
    /// Approximate total solver-style queries issued by the bridge.
    pub(crate) total_solver_calls: usize,
}

/// Outcome of running the IC3-CEGAR bridge.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
#[non_exhaustive]
pub(crate) enum Ic3CegarResult {
    /// The property was proved and an invariant was found.
    Proved {
        /// Inductive invariant clauses returned by IC3 and strengthened by CEGAR.
        invariant: Vec<Cube>,
        /// Execution statistics.
        stats: Ic3Stats,
    },
    /// The property was refuted by a concrete counterexample.
    Refuted {
        /// Concrete counterexample trace.
        trace: Vec<Cube>,
        /// Execution statistics.
        stats: Ic3Stats,
    },
    /// The bridge exhausted its budget without a proof or real counterexample.
    Unknown {
        /// Execution statistics.
        stats: Ic3Stats,
    },
}

/// Bridge that alternates between IC3 checking and CEGAR refinement.
#[derive(Debug, Clone)]
pub(crate) struct Ic3CegarBridge {
    system: TransitionSystem,
    config: Ic3CegarConfig,
    stats: Ic3Stats,
    learned_frames: Vec<Frame>,
    learned_predicates: Vec<Formula>,
}

impl Ic3CegarBridge {
    /// Create a new IC3-CEGAR bridge.
    #[must_use]
    pub(crate) fn new(system: TransitionSystem, config: Ic3CegarConfig) -> Self {
        Self {
            system,
            config,
            stats: Ic3Stats::default(),
            learned_frames: vec![Frame::new(0)],
            learned_predicates: Vec::new(),
        }
    }

    /// Access the collected statistics.
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn stats(&self) -> &Ic3Stats {
        &self.stats
    }

    /// Access the learned frame clauses accumulated by CEGAR refinement.
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn learned_frames(&self) -> &[Frame] {
        &self.learned_frames
    }

    /// Access the learned predicates extracted from spurious traces.
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn learned_predicates(&self) -> &[Formula] {
        &self.learned_predicates
    }

    /// Run alternating IC3 and CEGAR rounds until proof, refutation, or budget exhaustion.
    ///
    /// # Errors
    /// Returns `CegarError` if IC3 fails or refinement stalls on a spurious trace.
    pub(crate) fn run(&mut self) -> Result<Ic3CegarResult, CegarError> {
        for _round in 0..self.config.max_cegar_rounds {
            let mut engine = Ic3Engine::new(self.refined_system(), self.ic3_config());
            self.stats.total_solver_calls += 1;

            let result = engine.check()?;
            self.stats.ic3_frames_explored += engine.frames().len().saturating_sub(1);

            match result {
                Ic3Result::Safe { invariant_clauses, .. } => {
                    return Ok(Ic3CegarResult::Proved {
                        invariant: self.merge_invariant(invariant_clauses),
                        stats: self.stats.clone(),
                    });
                }
                Ic3Result::Unsafe { trace } => {
                    self.stats.total_solver_calls += 1;
                    if !self.counterexample_is_spurious(&trace) {
                        return Ok(Ic3CegarResult::Refuted { trace, stats: self.stats.clone() });
                    }

                    let prioritized_trace = self.prioritize_trace(&trace);
                    let new_predicates = if self.config.use_interpolation {
                        dedup_formulas(extract_predicates_from_trace(&prioritized_trace))
                    } else {
                        dedup_formulas(extract_top_level_predicates_from_trace(&prioritized_trace))
                    };

                    if new_predicates.is_empty() {
                        return Err(CegarError::RefinementStalled);
                    }

                    self.ensure_frame_capacity(engine.frames().len());
                    let clause_count_before = total_clauses(&self.learned_frames);
                    strengthen_frames(&mut self.learned_frames[1..], &new_predicates);
                    let clause_delta =
                        total_clauses(&self.learned_frames).saturating_sub(clause_count_before);

                    if clause_delta == 0 {
                        return Err(CegarError::RefinementStalled);
                    }

                    self.record_predicates(&new_predicates);
                    self.stats.cubes_blocked += new_predicates.len();
                    self.stats.clauses_propagated += clause_delta;
                    self.stats.cegar_refinements += 1;
                }
                Ic3Result::Unknown { .. } => {
                    return Ok(Ic3CegarResult::Unknown { stats: self.stats.clone() });
                }
            }
        }

        Ok(Ic3CegarResult::Unknown { stats: self.stats.clone() })
    }

    fn ic3_config(&self) -> Ic3Config {
        Ic3Config { max_depth: self.config.max_ic3_depth, ..Ic3Config::default() }
    }

    fn refined_system(&self) -> TransitionSystem {
        let mut property_parts = vec![self.system.property.clone()];
        for frame in self.learned_frames.iter().skip(1) {
            if !frame.is_empty() {
                property_parts.push(frame.to_formula());
            }
        }

        TransitionSystem::new(
            self.system.init.clone(),
            self.system.transition.clone(),
            conjoin(property_parts),
        )
    }

    fn merge_invariant(&self, mut invariant: Vec<Cube>) -> Vec<Cube> {
        for frame in self.learned_frames.iter().skip(1) {
            for clause in &frame.clauses {
                if !invariant.contains(clause) {
                    invariant.push(clause.clone());
                }
            }
        }
        invariant
    }

    fn prioritize_trace(&self, trace: &[Cube]) -> Vec<Cube> {
        let mut ordered = trace.to_vec();
        match self.config.obligation_priority {
            ObligationPriority::DepthFirst => ordered,
            ObligationPriority::BreadthFirst => {
                ordered.reverse();
                ordered
            }
            ObligationPriority::SmallestCubeFirst => {
                ordered.sort_by_key(Cube::len);
                ordered
            }
        }
    }

    fn counterexample_is_spurious(&self, trace: &[Cube]) -> bool {
        if trace.is_empty() {
            return true;
        }

        if self.trace_conflicts_with_refinement(trace) {
            return true;
        }

        let candidate = match self.config.obligation_priority {
            ObligationPriority::DepthFirst => trace.last().unwrap_or(&trace[0]),
            ObligationPriority::BreadthFirst => &trace[0],
            ObligationPriority::SmallestCubeFirst => {
                trace.iter().min_by_key(|cube| cube.len()).unwrap_or(&trace[0])
            }
        };

        if cube_contradicts_formula(candidate, &self.system.init) {
            return true;
        }

        self.system.transition == Formula::Bool(false) && trace.len() > 1
    }

    fn trace_conflicts_with_refinement(&self, trace: &[Cube]) -> bool {
        self.learned_frames
            .iter()
            .skip(1)
            .flat_map(|frame| frame.clauses.iter())
            .any(|clause| trace.iter().any(|cube| clause_subsumes_cube(clause, cube)))
    }

    fn ensure_frame_capacity(&mut self, required_len: usize) {
        while self.learned_frames.len() < required_len {
            let next_index = self.learned_frames.len();
            self.learned_frames.push(Frame::new(next_index));
        }
    }

    fn record_predicates(&mut self, predicates: &[Formula]) {
        for predicate in predicates {
            if !self.learned_predicates.contains(predicate) {
                self.learned_predicates.push(predicate.clone());
            }
        }
    }
}

/// Extract predicate candidates from a counterexample trace.
///
/// Conjunctive literals are split into atomic predicate candidates so they can
/// be fed back into the IC3 frame sequence as single-literal cubes.
#[must_use]
pub(crate) fn extract_predicates_from_trace(trace: &[Cube]) -> Vec<Formula> {
    let mut predicates = Vec::new();

    for cube in trace {
        for literal in &cube.literals {
            collect_predicates_from_formula(literal, &mut predicates);
        }
    }

    predicates
}

/// Strengthen IC3 frames with predicate-derived clauses.
pub(crate) fn strengthen_frames(frames: &mut [Frame], predicates: &[Formula]) {
    for frame in frames {
        for predicate in predicates {
            for clause in predicate_to_cubes(predicate) {
                frame.add_clause(clause);
            }
        }
    }
}

fn extract_top_level_predicates_from_trace(trace: &[Cube]) -> Vec<Formula> {
    let mut predicates = Vec::new();

    for cube in trace {
        for literal in &cube.literals {
            if matches!(literal, Formula::Bool(_)) {
                continue;
            }
            if !predicates.contains(literal) {
                predicates.push(literal.clone());
            }
        }
    }

    predicates
}

fn collect_predicates_from_formula(formula: &Formula, out: &mut Vec<Formula>) {
    match formula {
        Formula::Bool(_) => {}
        Formula::And(conjuncts) => {
            for conjunct in conjuncts {
                collect_predicates_from_formula(conjunct, out);
            }
        }
        _ => {
            if !out.contains(formula) {
                out.push(formula.clone());
            }
        }
    }
}

fn predicate_to_cubes(predicate: &Formula) -> Vec<Cube> {
    match predicate {
        Formula::Bool(_) => Vec::new(),
        Formula::And(conjuncts) => conjuncts
            .iter()
            .filter(|conjunct| !matches!(conjunct, Formula::Bool(_)))
            .map(|conjunct| Cube::new(vec![conjunct.clone()]))
            .collect(),
        _ => vec![Cube::new(vec![predicate.clone()])],
    }
}

fn conjoin(mut formulas: Vec<Formula>) -> Formula {
    match formulas.len() {
        0 => Formula::Bool(true),
        1 => formulas.pop().expect("formula length checked"),
        _ => Formula::And(formulas),
    }
}

fn total_clauses(frames: &[Frame]) -> usize {
    frames.iter().map(Frame::clause_count).sum()
}

fn dedup_formulas(formulas: Vec<Formula>) -> Vec<Formula> {
    let mut unique = Vec::new();
    for formula in formulas {
        if !unique.contains(&formula) {
            unique.push(formula);
        }
    }
    unique
}

fn clause_subsumes_cube(clause: &Cube, cube: &Cube) -> bool {
    clause.literals.iter().all(|literal| cube.literals.contains(literal))
}

fn cube_contradicts_formula(cube: &Cube, formula: &Formula) -> bool {
    cube.literals.iter().any(|literal| match literal {
        Formula::Bool(false) => *formula == Formula::Bool(true),
        Formula::Not(inner) => inner.as_ref() == formula,
        _ => *literal == Formula::Not(Box::new(formula.clone())),
    })
}

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn lt(name: &str, value: i128) -> Formula {
        Formula::Lt(Box::new(int_var(name)), Box::new(Formula::Int(value)))
    }

    fn ge(name: &str, value: i128) -> Formula {
        Formula::Ge(Box::new(int_var(name)), Box::new(Formula::Int(value)))
    }

    #[test]
    fn test_ic3_cegar_config_defaults() {
        let config = Ic3CegarConfig::default();
        assert_eq!(config.max_ic3_depth, 100);
        assert_eq!(config.max_cegar_rounds, 50);
        assert!(config.use_interpolation);
        assert_eq!(config.obligation_priority, ObligationPriority::DepthFirst);
    }

    #[test]
    fn test_ic3_stats_initialization() {
        let stats = Ic3Stats::default();
        assert_eq!(stats.ic3_frames_explored, 0);
        assert_eq!(stats.cubes_blocked, 0);
        assert_eq!(stats.clauses_propagated, 0);
        assert_eq!(stats.cegar_refinements, 0);
        assert_eq!(stats.total_solver_calls, 0);
    }

    #[test]
    fn test_trivially_safe_system_goes_through_bridge() {
        let system =
            TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
        let mut bridge = Ic3CegarBridge::new(system, Ic3CegarConfig::default());

        let result = bridge.run().expect("bridge should succeed");
        match result {
            Ic3CegarResult::Proved { invariant, stats } => {
                let _ = invariant;
                assert!(stats.ic3_frames_explored >= 1);
                assert!(stats.total_solver_calls >= 1);
            }
            other => panic!("expected Proved, got: {other:?}"),
        }
    }

    #[test]
    fn test_trivially_unsafe_system_returns_refutation() {
        let system =
            TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(false));
        let mut bridge = Ic3CegarBridge::new(system, Ic3CegarConfig::default());

        let result = bridge.run().expect("bridge should succeed");
        match result {
            Ic3CegarResult::Refuted { trace, stats } => {
                assert!(!trace.is_empty());
                assert!(stats.total_solver_calls >= 2);
            }
            other => panic!("expected Refuted, got: {other:?}"),
        }
    }

    #[test]
    fn test_obligation_priority_variants() {
        assert!(matches!(ObligationPriority::DepthFirst, ObligationPriority::DepthFirst));
        assert!(matches!(ObligationPriority::BreadthFirst, ObligationPriority::BreadthFirst));
        assert!(matches!(
            ObligationPriority::SmallestCubeFirst,
            ObligationPriority::SmallestCubeFirst
        ));
    }

    #[test]
    fn test_extract_predicates_from_trace_empty_trace() {
        let predicates = extract_predicates_from_trace(&[]);
        assert!(predicates.is_empty());
    }

    #[test]
    fn test_extract_predicates_from_trace_real_cubes() {
        let trace = vec![
            Cube::new(vec![lt("x", 0)]),
            Cube::new(vec![Formula::And(vec![ge("y", 1), lt("z", 5)])]),
        ];

        let predicates = extract_predicates_from_trace(&trace);
        assert_eq!(predicates.len(), 3);
        assert!(predicates.contains(&lt("x", 0)));
        assert!(predicates.contains(&ge("y", 1)));
        assert!(predicates.contains(&lt("z", 5)));
    }

    #[test]
    fn test_strengthen_frames_adds_clauses() {
        let mut frames = [Frame::new(0), Frame::new(1), Frame::new(2)];
        let predicates = vec![lt("x", 0), ge("y", 1)];

        strengthen_frames(&mut frames[1..], &predicates);

        assert_eq!(frames[0].clause_count(), 0);
        assert_eq!(frames[1].clause_count(), 2);
        assert_eq!(frames[2].clause_count(), 2);
        assert!(frames[1].contains(&Cube::new(vec![lt("x", 0)])));
        assert!(frames[2].contains(&Cube::new(vec![ge("y", 1)])));
    }
}
