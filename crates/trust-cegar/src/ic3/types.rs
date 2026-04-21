// trust-cegar: IC3 core types (Cube, Frame, TransitionSystem, results)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

use serde::{Deserialize, Serialize};
use trust_types::Formula;

use crate::z4_bridge::formula_to_smtlib;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A cube: a conjunction of literals (formulas). Represents a set of states.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Cube {
    /// Literals in the cube (conjuncted).
    pub literals: Vec<Formula>,
}

impl Cube {
    /// Create a cube from literals.
    #[must_use]
    pub fn new(literals: Vec<Formula>) -> Self {
        Self { literals }
    }

    /// Empty cube (represents all states / true).
    #[must_use]
    pub fn empty() -> Self {
        Self { literals: Vec::new() }
    }

    /// Whether this cube has no literals.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    /// Number of literals in this cube.
    #[must_use]
    pub fn len(&self) -> usize {
        self.literals.len()
    }

    /// Convert this cube to a formula (conjunction of its literals).
    #[must_use]
    pub fn to_formula(&self) -> Formula {
        match self.literals.len() {
            0 => Formula::Bool(true),
            1 => self.literals[0].clone(),
            _ => Formula::And(self.literals.clone()),
        }
    }

    /// Negate this cube (produces a clause: disjunction of negated literals).
    #[must_use]
    pub fn negate(&self) -> Formula {
        match self.literals.len() {
            0 => Formula::Bool(false),
            1 => Formula::Not(Box::new(self.literals[0].clone())),
            _ => Formula::Or(
                self.literals.iter().map(|l| Formula::Not(Box::new(l.clone()))).collect(),
            ),
        }
    }
}

impl fmt::Display for Cube {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.literals.is_empty() {
            return write!(f, "true");
        }
        let parts: Vec<String> = self.literals.iter().map(formula_to_smtlib).collect();
        write!(f, "({})", parts.join(" /\\ "))
    }
}

/// A frame in the IC3 frame sequence.
///
/// Each frame F_i overapproximates the states reachable in at most i steps.
/// Frames are represented as a set of clauses (negated cubes) that are
/// inductive relative to the previous frame.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Frame {
    /// Clauses in this frame. Each clause blocks a set of bad states.
    /// The frame represents the conjunction of all its clauses.
    /// Maintained without duplicates via `add_clause`.
    pub clauses: Vec<Cube>,
    /// Frame index in the sequence.
    pub index: usize,
}

impl Frame {
    /// Create a new empty frame at the given index.
    #[must_use]
    pub fn new(index: usize) -> Self {
        Self { clauses: Vec::new(), index }
    }

    /// Add a clause (blocked cube) to this frame. Deduplicates.
    pub fn add_clause(&mut self, cube: Cube) {
        if !self.clauses.contains(&cube) {
            self.clauses.push(cube);
        }
    }

    /// Number of clauses in this frame.
    #[must_use]
    pub fn clause_count(&self) -> usize {
        self.clauses.len()
    }

    /// Whether this frame has no clauses (equivalent to true / all states).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Check if this frame contains a specific clause.
    #[must_use]
    pub fn contains(&self, cube: &Cube) -> bool {
        self.clauses.contains(cube)
    }

    /// Convert all clauses to a single formula (conjunction of negated cubes).
    #[must_use]
    pub fn to_formula(&self) -> Formula {
        if self.clauses.is_empty() {
            return Formula::Bool(true);
        }
        let negated: Vec<Formula> = self.clauses.iter().map(Cube::negate).collect();
        if negated.len() == 1 {
            return negated.into_iter().next().expect("checked len == 1");
        }
        Formula::And(negated)
    }
}

impl fmt::Display for Frame {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "F_{} [{}cl]", self.index, self.clauses.len())
    }
}

// ---------------------------------------------------------------------------
// Transition system
// ---------------------------------------------------------------------------

/// A transition relation for IC3: `(init, transition, property)`.
///
/// - `init`: formula characterizing initial states
/// - `transition`: formula relating current-state and next-state variables
/// - `property`: safety property to check (should hold in all reachable states)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransitionSystem {
    /// Initial state formula.
    pub init: Formula,
    /// Transition relation formula (references both current and primed variables).
    pub transition: Formula,
    /// Safety property (over current-state variables).
    pub property: Formula,
}

impl TransitionSystem {
    /// Create a new transition system.
    #[must_use]
    pub fn new(init: Formula, transition: Formula, property: Formula) -> Self {
        Self { init, transition, property }
    }
}

// ---------------------------------------------------------------------------
// IC3 result
// ---------------------------------------------------------------------------

/// Result of IC3 model checking.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Ic3Result {
    /// Property is safe. Contains the inductive invariant (as frame clauses).
    Safe {
        /// The inductive invariant: conjunction of clauses from converged frames.
        invariant_clauses: Vec<Cube>,
        /// Frame depth at which convergence was detected.
        convergence_depth: usize,
    },
    /// Property is unsafe. Contains a counterexample trace.
    Unsafe {
        /// Counterexample trace: sequence of cubes from initial state to bad state.
        trace: Vec<Cube>,
    },
    /// IC3 reached the depth bound without convergence.
    Unknown {
        /// Maximum frame depth reached.
        depth: usize,
    },
}

// ---------------------------------------------------------------------------
// Proof obligation
// ---------------------------------------------------------------------------

/// A proof obligation in the IC3 blocking queue.
///
/// Represents a cube that needs to be blocked at a given frame level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofObligation {
    /// Frame level at which the cube must be blocked.
    pub(crate) level: usize,
    /// The cube (bad state set) to block.
    pub(crate) cube: Cube,
}

// ---------------------------------------------------------------------------
// IC3 Configuration
// ---------------------------------------------------------------------------

/// Configuration for the IC3 engine.
#[derive(Debug, Clone)]
pub struct Ic3Config {
    /// Maximum frame depth before giving up.
    pub max_depth: usize,
    /// Maximum number of blocking iterations per cube.
    pub max_block_iterations: usize,
}

impl Default for Ic3Config {
    fn default() -> Self {
        Self { max_depth: 200, max_block_iterations: 10_000 }
    }
}
