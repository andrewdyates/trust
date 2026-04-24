// trust-types/formula/contracts: Contract and metadata types for verification
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use super::Formula;
use crate::fx::FxHashMap;

/// tRust: Serializable state machine metadata for temporal VC dispatch (#182).
///
/// Bridges trust-types `StateMachine` (MIR-level) to trust-temporal
/// `StateMachine` (model-checking level). The tla2 backend converts this
/// to a trust-temporal StateMachine for CTL/LTL/liveness/fairness checking.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StateMachineMetadata {
    /// State names, indexed by position (position = state ID).
    pub states: Vec<String>,
    /// Indices of initial states (into the `states` vec).
    pub init_states: Vec<usize>,
    /// Transitions: (from_state_idx, event_label, to_state_idx).
    pub transitions: Vec<(usize, String, usize)>,
    /// Labels for each state: state_idx -> list of atomic proposition labels.
    pub labels: FxHashMap<usize, Vec<String>>,
}

impl StateMachineMetadata {
    /// tRust: Convert a trust-types `StateMachine` to `StateMachineMetadata` (#182).
    #[must_use]
    pub fn from_trust_types_sm(sm: &crate::StateMachine) -> Self {
        let states: Vec<String> = sm.states.iter().map(|s| s.name.clone()).collect();
        let init_states = sm.initial_state.map_or_else(Vec::new, |init| {
            sm.states.iter().position(|s| s.discriminant == init).into_iter().collect()
        });
        let transitions = sm
            .transitions
            .iter()
            .filter_map(|t| {
                let from_idx = sm.states.iter().position(|s| s.discriminant == t.from)?;
                let to_idx = sm.states.iter().position(|s| s.discriminant == t.to)?;
                let from_name = &sm.states[from_idx].name;
                let to_name = &sm.states[to_idx].name;
                Some((from_idx, format!("{from_name}_to_{to_name}"), to_idx))
            })
            .collect();
        let labels = states.iter().enumerate().map(|(i, name)| (i, vec![name.clone()])).collect();
        Self { states, init_states, transitions, labels }
    }
}

// tRust: Contract metadata for deductive verification routing (#181).
//
// Tracks which contract annotations are present on a VC so the router
// can prioritize sunder (deductive engine) for contract-bearing VCs.

/// Metadata about contract annotations attached to a verification condition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ContractMetadata {
    /// Whether the function has a `#[requires(...)]` annotation.
    pub has_requires: bool,
    /// Whether the function has an `#[ensures(...)]` annotation.
    pub has_ensures: bool,
    /// Whether the function has a `#[invariant(...)]` annotation.
    pub has_invariant: bool,
    /// Whether the function has a `#[decreases(...)]` annotation.
    pub has_variant: bool,
    // tRust #588: Sunder-style contract metadata for Horn clause lowering.
    /// Whether the function has a `#[loop_invariant(...)]` annotation.
    #[serde(default)]
    pub has_loop_invariant: bool,
    /// Whether the function has a `#[refine(...)]` annotation.
    #[serde(default)]
    pub has_type_refinement: bool,
    /// Whether the function has a `#[modifies(...)]` annotation.
    #[serde(default)]
    pub has_modifies: bool,
}

impl ContractMetadata {
    /// Returns true if any contract annotation is present.
    #[must_use]
    pub fn has_any(&self) -> bool {
        self.has_requires
            || self.has_ensures
            || self.has_invariant
            || self.has_variant
            || self.has_loop_invariant
            || self.has_type_refinement
            || self.has_modifies
    }

    /// Returns true if any Sunder-specific contract is present.
    #[must_use]
    pub fn has_sunder_contracts(&self) -> bool {
        self.has_loop_invariant || self.has_type_refinement || self.has_modifies
    }
}

// tRust #588: Sunder contract IR for Horn clause lowering.
//
// Captures the full contract representation needed to lower function contracts
// to Constrained Horn Clauses (CHCs). The Sunder backend uses this as input
// for its strongest-postcondition reasoning engine.

/// A loop invariant with its associated loop header block.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LoopInvariantContract {
    /// The invariant formula (parsed from the annotation body).
    pub formula: Formula,
    /// Block ID of the loop header this invariant applies to.
    pub header_block: usize,
    /// The original expression string from the annotation.
    pub expr: String,
}

/// A type refinement predicate binding a variable to a constraint.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeRefinementContract {
    /// The variable being refined.
    pub variable: String,
    /// The refinement predicate formula (e.g., `v > 0`).
    pub predicate: Formula,
    /// The original expression string from the annotation.
    pub expr: String,
}

/// Intermediate representation of Sunder-style contracts for a function.
///
/// Aggregates all contract annotations into a form suitable for lowering
/// to Horn clauses. The trust-vcgen contracts module populates this from
/// parsed `Contract` entries, and the trust-router sunder backend consumes
/// it for CHC system construction.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct SunderContractIr {
    /// Preconditions (from `#[requires(...)]`).
    pub preconditions: Vec<Formula>,
    /// Postconditions (from `#[ensures(...)]`).
    pub postconditions: Vec<Formula>,
    /// Loop invariants with associated loop headers.
    pub loop_invariants: Vec<LoopInvariantContract>,
    /// Type refinement predicates binding variables to constraints.
    pub type_refinements: Vec<TypeRefinementContract>,
    /// Variables the function is allowed to modify (from `#[modifies(...)]`).
    /// Everything else is implicitly preserved (frame condition).
    pub modifies_set: Vec<String>,
}

impl SunderContractIr {
    /// Returns true if this IR contains any contract information.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.preconditions.is_empty()
            && self.postconditions.is_empty()
            && self.loop_invariants.is_empty()
            && self.type_refinements.is_empty()
            && self.modifies_set.is_empty()
    }

    /// Build a `ContractMetadata` summarizing which contract kinds are present.
    #[must_use]
    pub fn to_metadata(&self) -> ContractMetadata {
        ContractMetadata {
            has_requires: !self.preconditions.is_empty(),
            has_ensures: !self.postconditions.is_empty(),
            has_invariant: false,
            has_variant: false,
            has_loop_invariant: !self.loop_invariants.is_empty(),
            has_type_refinement: !self.type_refinements.is_empty(),
            has_modifies: !self.modifies_set.is_empty(),
        }
    }
}
