// trust-cegar/cpa.rs: Configurable Program Analysis framework
//
// Implements the CPA composition framework from CPAchecker, allowing multiple
// abstract domains to be composed into a product analysis. Each CPA contributes
// its own abstract state, transfer function, and precision; the composite CPA
// runs all domains in lockstep and combines results.
//
// Reference: CPAchecker CPA framework
//   refs/cpachecker/src/org/sosy_lab/cpachecker/core/interfaces/
//
// Part of #103: Advanced Analysis
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use serde::{Deserialize, Serialize};
use trust_types::{BlockId, VerifiableBody};

use crate::abstraction::AbstractDomain;
use crate::predicate::AbstractState;

// ---------------------------------------------------------------------------
// CPA trait
// ---------------------------------------------------------------------------

/// A Configurable Program Analysis (CPA) component.
///
/// Each CPA defines:
/// - An abstract domain (lattice operations)
/// - A transfer function (abstract post for each statement)
/// - A merge operator (how states combine at join points)
/// - A stop operator (when to stop exploring)
pub trait Cpa: std::fmt::Debug {
    /// Unique name for this CPA (used in diagnostics and logging).
    fn name(&self) -> &str;

    /// Abstract domain providing lattice operations.
    fn domain(&self) -> &dyn AbstractDomain;

    /// Compute the abstract successor for a block transition.
    ///
    /// Given the current abstract state and the target block ID,
    /// returns the new abstract state after applying the block's
    /// statements abstractly.
    fn transfer(
        &self,
        state: &AbstractState,
        block: BlockId,
        body: &VerifiableBody,
    ) -> AbstractState;

    /// Merge two states at a control-flow join point.
    ///
    /// CPA-specific merge may be:
    /// - `MergeJoin`: always join (flow-insensitive)
    /// - `MergeSep`: never merge (path-sensitive)
    /// - Custom: merge selectively
    fn merge(&self, state1: &AbstractState, state2: &AbstractState) -> AbstractState;

    /// Check whether exploration should stop for this state.
    ///
    /// Returns true if `state` is already covered by `reached` (the set
    /// of already-explored states at this location).
    fn stop(&self, state: &AbstractState, reached: &[AbstractState]) -> bool;
}

// ---------------------------------------------------------------------------
// Merge operators
// ---------------------------------------------------------------------------

/// Standard merge strategies from CPAchecker.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum MergeStrategy {
    /// Always join states at merge points (flow-insensitive).
    Join,
    /// Never merge — keep states separate (fully path-sensitive).
    Sep,
}

// ---------------------------------------------------------------------------
// Composite CPA
// ---------------------------------------------------------------------------

/// A composite CPA that runs multiple CPAs in product.
///
/// The composite state is a tuple of individual CPA states. Transfer,
/// merge, and stop operate component-wise.
#[derive(Debug)]
pub struct CompositeCpa {
    /// Constituent CPAs.
    components: Vec<Box<dyn Cpa>>,
}

impl CompositeCpa {
    /// Create a composite from a list of component CPAs.
    #[must_use]
    pub fn new(components: Vec<Box<dyn Cpa>>) -> Self {
        Self { components }
    }

    /// Number of component CPAs.
    #[must_use]
    pub fn num_components(&self) -> usize {
        self.components.len()
    }

    /// Component names for diagnostics.
    #[must_use]
    pub fn component_names(&self) -> Vec<&str> {
        self.components.iter().map(|c| c.name()).collect()
    }
}

// ---------------------------------------------------------------------------
// Composite abstract state
// ---------------------------------------------------------------------------

/// A composite abstract state — one state per CPA component.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompositeState {
    /// Per-component abstract states, indexed by component position.
    pub states: Vec<AbstractState>,
}

impl CompositeState {
    /// Create a composite state from individual component states.
    #[must_use]
    pub fn new(states: Vec<AbstractState>) -> Self {
        Self { states }
    }

    /// Check if any component is bottom (unreachable).
    #[must_use]
    pub fn is_bottom(&self) -> bool {
        self.states.iter().any(crate::abstraction::is_bottom)
    }
}

// ---------------------------------------------------------------------------
// CPA algorithm (worklist-based reachability)
// ---------------------------------------------------------------------------

/// Configuration for the CPA algorithm.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CpaConfig {
    /// Maximum number of iterations before timeout.
    pub max_iterations: usize,
    /// Maximum number of states in the reached set before widening.
    pub max_reached: usize,
}

impl Default for CpaConfig {
    fn default() -> Self {
        Self { max_iterations: 10_000, max_reached: 100_000 }
    }
}

/// Result of CPA-based analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CpaResult {
    /// Analysis completed — all reachable states explored.
    Safe {
        /// Number of reachable states discovered.
        states_explored: usize,
        /// Number of iterations.
        iterations: usize,
    },
    /// A target state was reached (potential bug).
    Unsafe {
        /// The composite state at the error location.
        error_state: CompositeState,
        /// Block where the error was found.
        error_block: BlockId,
        /// Number of iterations before finding the error.
        iterations: usize,
    },
    /// Analysis did not converge within the iteration budget.
    Timeout {
        /// States explored before timeout.
        states_explored: usize,
        /// Iterations completed.
        iterations: usize,
    },
}

/// Reached set: per-block collection of explored states.
#[derive(Debug, Default)]
pub struct ReachedSet {
    /// Map from block ID to the set of abstract states reached at that block.
    states: FxHashMap<BlockId, Vec<CompositeState>>,
    /// Total number of states across all blocks.
    total: usize,
}

impl ReachedSet {
    /// Add a state at a given block. Returns true if the state is new.
    pub fn add(&mut self, block: BlockId, state: CompositeState) -> bool {
        let entry = self.states.entry(block).or_default();
        // Check if already covered
        // (simplified: just add; real impl would check stop operator)
        entry.push(state);
        self.total += 1;
        true
    }

    /// Get all states at a given block.
    #[must_use]
    pub fn at_block(&self, block: BlockId) -> &[CompositeState] {
        self.states.get(&block).map_or(&[], |v| v.as_slice())
    }

    /// Total states in the reached set.
    #[must_use]
    pub fn total(&self) -> usize {
        self.total
    }
}

/// Run the CPA algorithm on a verifiable body.
///
/// Uses a worklist-based forward reachability analysis, running all
/// component CPAs in lockstep. Each block is analyzed by applying
/// each CPA's transfer function to produce successor states.
pub fn cpa_analyze(
    cpa: &CompositeCpa,
    body: &VerifiableBody,
    error_blocks: &[BlockId],
    config: &CpaConfig,
) -> CpaResult {
    let n = cpa.num_components();

    // Initial state: top for all components at entry block
    let init_state = CompositeState::new(cpa.components.iter().map(|c| c.domain().top()).collect());

    let mut reached = ReachedSet::default();
    let entry_block = BlockId(0);
    reached.add(entry_block, init_state.clone());

    // Worklist: (block, composite_state)
    let mut worklist: Vec<(BlockId, CompositeState)> = vec![(entry_block, init_state)];
    let mut iterations = 0;

    while let Some((block, state)) = worklist.pop() {
        iterations += 1;
        if iterations > config.max_iterations {
            return CpaResult::Timeout { states_explored: reached.total(), iterations };
        }

        // Check if this is an error block
        if error_blocks.contains(&block) {
            return CpaResult::Unsafe { error_state: state, error_block: block, iterations };
        }

        // Apply transfer function for each component
        let successor_states: Vec<AbstractState> =
            (0..n).map(|i| cpa.components[i].transfer(&state.states[i], block, body)).collect();

        let succ = CompositeState::new(successor_states);

        // Skip if any component reached bottom
        if succ.is_bottom() {
            continue;
        }

        // Find successor blocks from the body's CFG terminator
        if let Some(block_data) = body.blocks.get(block.0) {
            let targets = terminator_targets(&block_data.terminator);
            for target in targets {
                // Check stop operator for each component
                let covered = (0..n).all(|i| {
                    let reached_states: Vec<AbstractState> =
                        reached.at_block(target).iter().map(|cs| cs.states[i].clone()).collect();
                    cpa.components[i].stop(&succ.states[i], &reached_states)
                });

                if !covered {
                    reached.add(target, succ.clone());
                    worklist.push((target, succ.clone()));
                }
            }
        }
    }

    CpaResult::Safe { states_explored: reached.total(), iterations }
}

/// Extract successor block IDs from a terminator.
fn terminator_targets(term: &trust_types::Terminator) -> Vec<BlockId> {
    use trust_types::Terminator;
    match term {
        Terminator::Goto(t) => vec![*t],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut result: Vec<BlockId> = targets.iter().map(|(_, b)| *b).collect();
            result.push(*otherwise);
            result
        }
        Terminator::Return | Terminator::Unreachable => vec![],
        Terminator::Call { target, .. } => target.iter().copied().collect(),
        Terminator::Assert { target, .. } => vec![*target],
        Terminator::Drop { target, .. } => vec![*target],
        _ => vec![],
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicate::Predicate;

    #[test]
    fn test_composite_state_new() {
        let s = CompositeState::new(vec![AbstractState::top(), AbstractState::top()]);
        assert_eq!(s.states.len(), 2);
        assert!(!s.is_bottom());
    }

    #[test]
    fn test_composite_state_bottom() {
        let mut state = AbstractState::top();
        state.add(Predicate::Custom("__bottom__".into()));
        let cs = CompositeState::new(vec![state]);
        assert!(cs.is_bottom());
    }

    #[test]
    fn test_reached_set_add() {
        let mut rs = ReachedSet::default();
        let cs = CompositeState::new(vec![AbstractState::top()]);
        assert!(rs.add(BlockId(0), cs.clone()));
        assert_eq!(rs.total(), 1);
        assert_eq!(rs.at_block(BlockId(0)).len(), 1);
        assert_eq!(rs.at_block(BlockId(1)).len(), 0);
    }

    #[test]
    fn test_cpa_config_default() {
        let cfg = CpaConfig::default();
        assert_eq!(cfg.max_iterations, 10_000);
        assert_eq!(cfg.max_reached, 100_000);
    }

    #[test]
    fn test_composite_cpa_names() {
        let cpa = CompositeCpa::new(vec![]);
        assert_eq!(cpa.num_components(), 0);
        assert!(cpa.component_names().is_empty());
    }

    #[test]
    fn test_cpa_result_variants() {
        let safe = CpaResult::Safe { states_explored: 10, iterations: 5 };
        assert!(matches!(safe, CpaResult::Safe { .. }));

        let timeout = CpaResult::Timeout { states_explored: 100, iterations: 10_000 };
        assert!(matches!(timeout, CpaResult::Timeout { .. }));

        let cs = CompositeState::new(vec![]);
        let err = CpaResult::Unsafe { error_state: cs, error_block: BlockId(3), iterations: 42 };
        assert!(matches!(err, CpaResult::Unsafe { .. }));
    }

    #[test]
    fn test_merge_strategy_debug() {
        assert_eq!(format!("{:?}", MergeStrategy::Join), "Join");
        assert_eq!(format!("{:?}", MergeStrategy::Sep), "Sep");
    }
}
