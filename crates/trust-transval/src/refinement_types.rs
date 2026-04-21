// trust-transval/refinement_types.rs: Refinement type checking (#257)
//
// Extends translation validation with refinement types: types enriched with
// logical predicates that are verified at compile time. E.g., {x: i32 | x > 0}
// is a positive integer type.
//
// References:
//   Freeman, Pfenning. "Refinement Types for ML" (PLDI 1991).
//   Rondon, Kawaguchi, Jhala. "Liquid Types" (PLDI 2008).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::{Formula, SourceSpan, VcKind, VerificationCondition};

// ---------------------------------------------------------------------------
// Refinement types
// ---------------------------------------------------------------------------

/// A refinement type: a base type with a predicate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RefinementType {
    /// Base type name (e.g., "i32", "usize").
    pub base: String,
    /// Refinement variable (bound in the predicate).
    pub var: String,
    /// Predicate over the variable.
    pub predicate: Formula,
}

impl RefinementType {
    /// Create a new refinement type.
    pub(crate) fn new(base: impl Into<String>, var: impl Into<String>, predicate: Formula) -> Self {
        Self { base: base.into(), var: var.into(), predicate }
    }

    /// Create an unrestricted type (predicate = true).
    pub(crate) fn unrestricted(base: impl Into<String>) -> Self {
        Self { base: base.into(), var: "v".into(), predicate: Formula::Bool(true) }
    }

    /// Check if this is a subtype of another (this.predicate => other.predicate).
    #[must_use]
    pub(crate) fn is_subtype_of(&self, other: &Self) -> SubtypeCheck {
        if self.base != other.base {
            return SubtypeCheck::Incompatible;
        }
        if other.predicate == Formula::Bool(true) {
            return SubtypeCheck::Trivial;
        }
        if self.predicate == other.predicate {
            return SubtypeCheck::Trivial;
        }
        SubtypeCheck::NeedsProof {
            antecedent: self.predicate.clone(),
            consequent: other.predicate.clone(),
        }
    }
}

impl std::fmt::Display for RefinementType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{ {}: {} | {:?} }}", self.var, self.base, self.predicate)
    }
}

/// Result of subtype checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SubtypeCheck {
    /// Base types are different — can't be subtypes.
    Incompatible,
    /// Subtyping holds trivially (target is unrestricted or same predicate).
    Trivial,
    /// Subtyping requires proving antecedent => consequent.
    NeedsProof { antecedent: Formula, consequent: Formula },
}

// ---------------------------------------------------------------------------
// Refinement environment
// ---------------------------------------------------------------------------

/// Type environment mapping variables to their refinement types.
#[derive(Debug, Clone, Default)]
pub(crate) struct RefinementEnv {
    /// Variable -> refinement type.
    bindings: FxHashMap<String, RefinementType>,
}

impl RefinementEnv {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Bind a variable to a refinement type.
    pub(crate) fn bind(&mut self, name: impl Into<String>, ty: RefinementType) {
        self.bindings.insert(name.into(), ty);
    }

    /// Look up a variable's refinement type.
    #[must_use]
    pub(crate) fn lookup(&self, name: &str) -> Option<&RefinementType> {
        self.bindings.get(name)
    }

    /// Get all bindings.
    #[must_use]
    pub(crate) fn bindings(&self) -> &FxHashMap<String, RefinementType> {
        &self.bindings
    }

    /// Number of bindings.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Whether the environment is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Collect all assumptions from the environment as a conjunction.
    #[must_use]
    pub(crate) fn assumptions(&self) -> Formula {
        let preds: Vec<Formula> = self
            .bindings
            .values()
            .filter(|ty| ty.predicate != Formula::Bool(true))
            .map(|ty| ty.predicate.clone())
            .collect();

        if preds.is_empty() { Formula::Bool(true) } else { Formula::And(preds) }
    }
}

// ---------------------------------------------------------------------------
// Refinement type checker
// ---------------------------------------------------------------------------

/// Checker that generates VCs from refinement type annotations.
pub struct RefinementChecker {
    /// Current environment.
    env: RefinementEnv,
}

impl RefinementChecker {
    pub(crate) fn new() -> Self {
        Self { env: RefinementEnv::new() }
    }

    pub(crate) fn with_env(env: RefinementEnv) -> Self {
        Self { env }
    }

    /// Generate a VC for a subtype check at a given program point.
    pub(crate) fn check_subtype(
        &self,
        actual: &RefinementType,
        expected: &RefinementType,
        function: &str,
        span: &SourceSpan,
    ) -> Vec<VerificationCondition> {
        match actual.is_subtype_of(expected) {
            SubtypeCheck::Incompatible | SubtypeCheck::Trivial => Vec::new(),
            SubtypeCheck::NeedsProof { antecedent, consequent } => {
                let assumptions = self.env.assumptions();
                let formula = Formula::Implies(
                    Box::new(Formula::And(vec![assumptions, antecedent])),
                    Box::new(Formula::Not(Box::new(consequent))),
                );
                vec![VerificationCondition {
                    kind: VcKind::Postcondition,
                    function: function.to_string(),
                    location: span.clone(),
                    formula,
                    contract_metadata: None,
                }]
            }
        }
    }

    /// Check an assignment: verify the RHS type is a subtype of the LHS type.
    pub(crate) fn check_assignment(
        &self,
        var: &str,
        rhs_type: &RefinementType,
        function: &str,
        span: &SourceSpan,
    ) -> Vec<VerificationCondition> {
        match self.env.lookup(var) {
            Some(lhs_type) => self.check_subtype(rhs_type, lhs_type, function, span),
            None => Vec::new(),
        }
    }

    /// Bind a variable in the environment.
    pub(crate) fn bind(&mut self, name: impl Into<String>, ty: RefinementType) {
        self.env.bind(name, ty);
    }

    /// Get the current environment.
    #[must_use]
    pub(crate) fn env(&self) -> &RefinementEnv {
        &self.env
    }
}

impl Default for RefinementChecker {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Common refinement type constructors
// ---------------------------------------------------------------------------

/// Create a positive integer refinement type.
pub(crate) fn positive_int(base: &str) -> RefinementType {
    RefinementType::new(
        base,
        "v",
        Formula::Gt(
            Box::new(Formula::Var("v".into(), trust_types::Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
    )
}

/// Create a non-negative integer refinement type.
pub(crate) fn non_negative_int(base: &str) -> RefinementType {
    RefinementType::new(
        base,
        "v",
        Formula::Ge(
            Box::new(Formula::Var("v".into(), trust_types::Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
    )
}

/// Create a bounded integer refinement type: lo <= v <= hi.
pub(crate) fn bounded_int(base: &str, lo: i128, hi: i128) -> RefinementType {
    RefinementType::new(
        base,
        "v",
        Formula::And(vec![
            Formula::Ge(
                Box::new(Formula::Var("v".into(), trust_types::Sort::Int)),
                Box::new(Formula::Int(lo)),
            ),
            Formula::Le(
                Box::new(Formula::Var("v".into(), trust_types::Sort::Int)),
                Box::new(Formula::Int(hi)),
            ),
        ]),
    )
}

/// Create a non-zero refinement type.
pub(crate) fn non_zero(base: &str) -> RefinementType {
    RefinementType::new(
        base,
        "v",
        Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("v".into(), trust_types::Sort::Int)),
            Box::new(Formula::Int(0)),
        ))),
    )
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_refinement_type_creation() {
        let ty = positive_int("i32");
        assert_eq!(ty.base, "i32");
        assert_eq!(ty.var, "v");
    }

    #[test]
    fn test_unrestricted_type() {
        let ty = RefinementType::unrestricted("u64");
        assert_eq!(ty.predicate, Formula::Bool(true));
    }

    #[test]
    fn test_subtype_same_predicate() {
        let a = positive_int("i32");
        let b = positive_int("i32");
        assert_eq!(a.is_subtype_of(&b), SubtypeCheck::Trivial);
    }

    #[test]
    fn test_subtype_unrestricted_target() {
        let a = positive_int("i32");
        let b = RefinementType::unrestricted("i32");
        assert_eq!(a.is_subtype_of(&b), SubtypeCheck::Trivial);
    }

    #[test]
    fn test_subtype_incompatible_bases() {
        let a = positive_int("i32");
        let b = positive_int("u64");
        assert_eq!(a.is_subtype_of(&b), SubtypeCheck::Incompatible);
    }

    #[test]
    fn test_subtype_needs_proof() {
        let a = positive_int("i32");
        let b = non_negative_int("i32");
        match a.is_subtype_of(&b) {
            SubtypeCheck::NeedsProof { .. } => {}
            other => panic!("expected NeedsProof, got {other:?}"),
        }
    }

    #[test]
    fn test_env_bind_and_lookup() {
        let mut env = RefinementEnv::new();
        env.bind("x", positive_int("i32"));
        assert!(env.lookup("x").is_some());
        assert!(env.lookup("y").is_none());
        assert_eq!(env.len(), 1);
    }

    #[test]
    fn test_env_assumptions() {
        let mut env = RefinementEnv::new();
        env.bind("x", positive_int("i32"));
        env.bind("y", RefinementType::unrestricted("u64"));
        let assumptions = env.assumptions();
        // Only x has a non-trivial predicate
        assert_ne!(assumptions, Formula::Bool(true));
    }

    #[test]
    fn test_empty_env_assumptions() {
        let env = RefinementEnv::new();
        assert_eq!(env.assumptions(), Formula::Bool(true));
    }

    #[test]
    fn test_checker_subtype_trivial() {
        let checker = RefinementChecker::new();
        let a = positive_int("i32");
        let b = RefinementType::unrestricted("i32");
        let vcs = checker.check_subtype(&a, &b, "f", &SourceSpan::default());
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_checker_subtype_generates_vc() {
        let checker = RefinementChecker::new();
        let a = non_negative_int("i32");
        let b = positive_int("i32");
        let vcs = checker.check_subtype(&a, &b, "f", &SourceSpan::default());
        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::Postcondition));
    }

    #[test]
    fn test_checker_assignment() {
        let mut checker = RefinementChecker::new();
        checker.bind("x", positive_int("i32"));
        let rhs = non_negative_int("i32");
        let vcs = checker.check_assignment("x", &rhs, "f", &SourceSpan::default());
        assert_eq!(vcs.len(), 1);
    }

    #[test]
    fn test_checker_assignment_unknown_var() {
        let checker = RefinementChecker::new();
        let rhs = positive_int("i32");
        let vcs = checker.check_assignment("unknown", &rhs, "f", &SourceSpan::default());
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_bounded_int() {
        let ty = bounded_int("u8", 0, 255);
        assert_eq!(ty.base, "u8");
        assert_ne!(ty.predicate, Formula::Bool(true));
    }

    #[test]
    fn test_non_zero() {
        let ty = non_zero("i32");
        assert_eq!(ty.base, "i32");
    }

    #[test]
    fn test_refinement_type_display() {
        let ty = positive_int("i32");
        let s = ty.to_string();
        assert!(s.contains("i32"));
        assert!(s.contains("v"));
    }
}
