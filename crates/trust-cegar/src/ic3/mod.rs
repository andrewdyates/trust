// trust-cegar: IC3/PDR (Property Directed Reachability) model checking
//
// **SAFETY PROPERTIES ONLY.** IC3/PDR proves that a "bad" state is never
// reachable (AG !bad). It CANNOT prove termination or liveness properties
// ("something good eventually happens"). For termination proofs, use:
//   - lean5 (inductive proofs with decreasing measures / well-founded orders)
//   - sunder (deductive verification with ranking functions)
//   - tla2 (liveness checking via Buchi automata)
//
// IC3 maintains a sequence of frames F_0, F_1, ..., F_k where each frame
// overapproximates the set of reachable states at depth i. The algorithm
// iteratively blocks bad cubes and propagates clauses forward until either:
//   - Two consecutive frames become equal (property proved: inductive invariant found)
//   - A counterexample trace is extracted (property violated)
//
// Key operations:
//   - block_cube: recursively block a bad state by finding predecessors
//   - propagate_clauses: push clauses to later frames for convergence
//   - generalize_cube: minimize a blocked cube for stronger lemmas
//
// Reference: Aaron Bradley, "SAT-Based Model Checking without Unrolling" (VMCAI 2011)
// Reference: refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod engine;
pub(crate) mod prime;
pub(crate) mod sat;
mod types;

#[cfg(test)]
mod tests;

// Re-export public API
#[allow(unused_imports)]
pub use engine::{Ic3Engine, ic3_check};
pub use types::{Cube, Frame, Ic3Config, Ic3Result, TransitionSystem};

// Re-export crate-internal items used by sibling modules
pub(crate) use sat::{SatResult, structural_sat_check};
