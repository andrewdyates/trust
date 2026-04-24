// trust-types/facts.rs: remembered facts for cross-function spec composition
//
// This module provides a small, reusable in-memory model for proof facts
// discovered by the verifier and reused at call sites. The first slice is
// intentionally conservative: call-site discharge is exact formula matching
// only, which keeps the data model sound and easy for later compiler passes
// to extend.

use serde::{Deserialize, Serialize};

use crate::{Formula, ProofStrength};

/// Stable identifier for a remembered fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FactId(pub usize);

/// A postcondition that has been proved and can be reused as a note.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProvedPostcondition {
    /// Function that proved the postcondition.
    pub function: String,
    /// Solver that proved the fact.
    pub solver: String,
    /// Strength of the proof.
    pub strength: ProofStrength,
}

/// Origin information for a remembered fact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum FactSource {
    /// A proved postcondition from another function.
    ProvedPostcondition(ProvedPostcondition),
    /// An explicitly recorded assumption.
    Assumption { label: String },
    /// A manually imported note.
    Note { note: String },
}

impl FactSource {
    fn is_proved_postcondition(&self) -> bool {
        matches!(self, FactSource::ProvedPostcondition(_))
    }
}

/// A remembered fact available for later call-site reasoning.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct KnownFact {
    pub id: FactId,
    pub predicate: Formula,
    pub source: FactSource,
}

/// In-memory store for remembered facts.
///
/// The store is append-only and uses exact formula equality for matching.
/// That is sufficient for a first slice of cross-function spec composition:
/// if a call-site requirement is identical to a previously proved postcondition,
/// the requirement is satisfied from notes with no solver call.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactMemory {
    facts: Vec<KnownFact>,
}

/// Result of checking a call-site requirement against remembered facts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CallSiteSatisfaction {
    /// A remembered fact discharged the requirement.
    SatisfiedFromNotes { fact_id: FactId, source: FactSource },
    /// No remembered fact was sufficient, so a solver is still needed.
    RequiresSolver { callee: String },
}

/// tRust: How a verification condition was resolved (#20).
///
/// Three costs from the design doc:
/// - Known from notes (free) — a proved postcondition satisfies this VC
/// - Solver proves it (costs time) — the standard solver path
/// - Solver can't (runtime check or error) — unproved
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VcDisposition {
    /// Satisfied from compiler notes — no solver call needed.
    /// The cheapest outcome: a previously proved postcondition discharges the requirement.
    SatisfiedFromNotes { fact_id: FactId, source: FactSource },
    /// Requires a solver call — the standard verification path.
    RequiresSolver,
    /// An assumption was injected from a callee's proved postcondition.
    /// The VC still goes to the solver, but with the callee's postcondition as a premise.
    SolverWithAssumption { fact_id: FactId, source: FactSource },
}

impl FactMemory {
    /// Create an empty fact memory.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the number of remembered facts.
    pub fn len(&self) -> usize {
        self.facts.len()
    }

    /// Returns true when no facts have been remembered.
    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }

    /// Returns all remembered facts in insertion order.
    pub fn facts(&self) -> &[KnownFact] {
        &self.facts
    }

    /// Returns a single fact by id.
    pub fn fact(&self, id: FactId) -> Option<&KnownFact> {
        self.facts.iter().find(|fact| fact.id == id)
    }

    /// Remember a proved postcondition so later call sites can reuse it.
    pub fn remember_proved_postcondition(
        &mut self,
        function: impl Into<String>,
        predicate: Formula,
        solver: impl Into<String>,
        strength: ProofStrength,
    ) -> FactId {
        self.insert(KnownFact {
            id: FactId(self.facts.len()),
            predicate,
            source: FactSource::ProvedPostcondition(ProvedPostcondition {
                function: function.into(),
                solver: solver.into(),
                strength,
            }),
        })
    }

    /// Remember an explicit assumption as a reusable fact.
    pub fn remember_assumption(&mut self, predicate: Formula, label: impl Into<String>) -> FactId {
        self.insert(KnownFact {
            id: FactId(self.facts.len()),
            predicate,
            source: FactSource::Assumption { label: label.into() },
        })
    }

    /// Remember a manual note as a reusable fact.
    pub fn remember_note(&mut self, predicate: Formula, note: impl Into<String>) -> FactId {
        self.insert(KnownFact {
            id: FactId(self.facts.len()),
            predicate,
            source: FactSource::Note { note: note.into() },
        })
    }

    /// Check whether a call-site requirement is already satisfied from notes.
    ///
    /// The first slice uses exact formula equality. If a remembered fact's
    /// predicate matches the required formula, the requirement is considered
    /// satisfied without a solver call.
    pub fn satisfy_call_site(
        &self,
        callee: impl Into<String>,
        requirement: &Formula,
    ) -> CallSiteSatisfaction {
        if let Some(fact) = self
            .facts
            .iter()
            .find(|fact| fact.predicate == *requirement && fact.source.is_proved_postcondition())
        {
            return CallSiteSatisfaction::SatisfiedFromNotes {
                fact_id: fact.id,
                source: fact.source.clone(),
            };
        }

        if let Some(fact) = self.facts.iter().find(|fact| fact.predicate == *requirement) {
            return CallSiteSatisfaction::SatisfiedFromNotes {
                fact_id: fact.id,
                source: fact.source.clone(),
            };
        }

        CallSiteSatisfaction::RequiresSolver { callee: callee.into() }
    }

    fn insert(&mut self, fact: KnownFact) -> FactId {
        let id = fact.id;
        self.facts.push(fact);
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ge(lhs: Formula, rhs: Formula) -> Formula {
        Formula::Ge(Box::new(lhs), Box::new(rhs))
    }

    #[test]
    fn test_remember_proved_postcondition_is_reusable() {
        let mut memory = FactMemory::new();
        let requirement = ge(Formula::Var("n".into(), crate::Sort::Int), Formula::Int(0));

        let fact_id = memory.remember_proved_postcondition(
            "parse",
            requirement.clone(),
            "z4",
            ProofStrength::smt_unsat(),
        );

        assert_eq!(memory.len(), 1);

        let satisfaction = memory.satisfy_call_site("sqrt", &requirement);
        match satisfaction {
            CallSiteSatisfaction::SatisfiedFromNotes { fact_id: matched, source } => {
                assert_eq!(matched, fact_id);
                match source {
                    FactSource::ProvedPostcondition(post) => {
                        assert_eq!(post.function, "parse");
                        assert_eq!(post.solver, "z4");
                        assert_eq!(post.strength, ProofStrength::smt_unsat());
                    }
                    other => panic!("expected proved postcondition, got {other:?}"),
                }
            }
            other => panic!("expected note-based satisfaction, got {other:?}"),
        }
    }

    #[test]
    fn test_satisfy_call_site_requires_solver_without_match() {
        let memory = FactMemory::new();
        let requirement = ge(Formula::Var("n".into(), crate::Sort::Int), Formula::Int(1));

        let satisfaction = memory.satisfy_call_site("sqrt", &requirement);
        assert_eq!(
            satisfaction,
            CallSiteSatisfaction::RequiresSolver { callee: "sqrt".to_string() }
        );
    }

    #[test]
    fn test_proved_postcondition_wins_over_generic_note() {
        let mut memory = FactMemory::new();
        let requirement = ge(Formula::Var("x".into(), crate::Sort::Int), Formula::Int(0));

        let note_id = memory.remember_note(requirement.clone(), "manual note");
        let fact_id = memory.remember_proved_postcondition(
            "parse",
            requirement.clone(),
            "z4",
            ProofStrength::smt_unsat(),
        );

        let satisfaction = memory.satisfy_call_site("sqrt", &requirement);
        match satisfaction {
            CallSiteSatisfaction::SatisfiedFromNotes { fact_id: matched, source } => {
                assert_eq!(matched, fact_id);
                assert!(matches!(source, FactSource::ProvedPostcondition(_)));
                assert_ne!(matched, note_id);
            }
            other => panic!("expected proved postcondition to win, got {other:?}"),
        }
    }

    #[test]
    fn test_serialization_roundtrip() {
        let mut memory = FactMemory::new();
        let requirement = ge(Formula::Var("len".into(), crate::Sort::Int), Formula::Int(0));

        memory.remember_assumption(requirement, "len is non-negative");

        let json = serde_json::to_string(&memory).expect("serialize");
        let round: FactMemory = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(round.len(), 1);
        assert_eq!(
            round.facts()[0].source,
            FactSource::Assumption { label: "len is non-negative".to_string() }
        );
    }
}
