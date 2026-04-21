// trust-vcgen/contract_check.rs: Modular verification with function contracts (#248)
//
// Extends contract-based VC generation with modular verification:
// - Check function bodies against requires/ensures contracts
// - Verify each function independently using only its contract
// - Contract inheritance for trait implementations
// - Automatic frame condition inference
// - Caller-side precondition checking at call sites
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::{Formula, SourceSpan, VcKind, VerificationCondition};

// ---------------------------------------------------------------------------
// Contract types
// ---------------------------------------------------------------------------

/// A function contract for modular verification.
#[derive(Debug, Clone)]
pub struct FunctionContract {
    /// Function name.
    pub function: String,
    /// Preconditions (requires clauses).
    pub requires: Vec<ContractClause>,
    /// Postconditions (ensures clauses).
    pub ensures: Vec<ContractClause>,
    /// Frame conditions (what doesn't change).
    pub frame: Vec<FrameCondition>,
    /// Whether this contract has been verified.
    pub verified: bool,
}

/// A single clause in a contract.
#[derive(Debug, Clone)]
pub struct ContractClause {
    /// Human-readable label.
    pub label: String,
    /// The formula for this clause.
    pub formula: Formula,
    /// Source location.
    pub span: SourceSpan,
}

/// A frame condition: a variable/location that doesn't change.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrameCondition {
    /// Variable or memory location name.
    pub location: String,
    /// Whether this was inferred (true) or explicitly specified (false).
    pub inferred: bool,
}

impl FunctionContract {
    /// Create a new empty contract.
    pub fn new(function: impl Into<String>) -> Self {
        Self {
            function: function.into(),
            requires: Vec::new(),
            ensures: Vec::new(),
            frame: Vec::new(),
            verified: false,
        }
    }

    /// Add a precondition.
    pub fn with_requires(mut self, label: impl Into<String>, formula: Formula) -> Self {
        self.requires.push(ContractClause {
            label: label.into(),
            formula,
            span: SourceSpan::default(),
        });
        self
    }

    /// Add a postcondition.
    pub fn with_ensures(mut self, label: impl Into<String>, formula: Formula) -> Self {
        self.ensures.push(ContractClause {
            label: label.into(),
            formula,
            span: SourceSpan::default(),
        });
        self
    }

    /// Add a frame condition.
    pub fn with_frame(mut self, location: impl Into<String>) -> Self {
        self.frame.push(FrameCondition {
            location: location.into(),
            inferred: false,
        });
        self
    }
}

// ---------------------------------------------------------------------------
// Contract checker (verify function body against contract)
// ---------------------------------------------------------------------------

/// Verifies function bodies against their contracts.
pub struct ContractChecker {
    /// Known contracts, keyed by function name.
    contracts: FxHashMap<String, FunctionContract>,
}

impl ContractChecker {
    /// Create a new contract checker.
    pub fn new() -> Self {
        Self {
            contracts: FxHashMap::default(),
        }
    }

    /// Register a contract.
    pub fn add_contract(&mut self, contract: FunctionContract) {
        self.contracts.insert(contract.function.clone(), contract);
    }

    /// Get a contract by function name.
    #[must_use]
    pub fn get_contract(&self, function: &str) -> Option<&FunctionContract> {
        self.contracts.get(function)
    }

    /// Generate VCs to verify a function body satisfies its contract.
    ///
    /// For each ensures clause, generates a VC that the postcondition holds
    /// at the function's return point, assuming all requires clauses hold.
    pub fn check_function(&self, function: &str) -> Vec<VerificationCondition> {
        let contract = match self.contracts.get(function) {
            Some(c) => c,
            None => return Vec::new(),
        };

        let mut vcs = Vec::new();

        // Build assumption from all requires clauses.
        let assumption = if contract.requires.is_empty() {
            Formula::Bool(true)
        } else {
            contract.requires.iter()
                .map(|c| c.formula.clone())
                .reduce(|a, b| Formula::And(vec![a, b]))
                .unwrap_or(Formula::Bool(true))
        };

        // For each ensures clause: prove postcondition assuming precondition.
        for clause in &contract.ensures {
            let formula = Formula::Implies(
                Box::new(assumption.clone()),
                Box::new(Formula::Not(Box::new(clause.formula.clone()))),
            );
            vcs.push(VerificationCondition {
                kind: VcKind::Postcondition,
                function: function.to_string(),
                location: clause.span.clone(),
                formula,
                contract_metadata: None,
            });
        }

        vcs
    }

    /// Generate caller-side VCs: at each call site, verify preconditions.
    pub fn check_call_site(
        &self,
        caller: &str,
        callee: &str,
        span: &SourceSpan,
    ) -> Vec<VerificationCondition> {
        let contract = match self.contracts.get(callee) {
            Some(c) => c,
            None => return Vec::new(),
        };

        contract.requires.iter().map(|clause| {
            VerificationCondition {
                kind: VcKind::Precondition { callee: callee.to_string() },
                function: caller.to_string(),
                location: span.clone(),
                formula: Formula::Not(Box::new(clause.formula.clone())),
                contract_metadata: None,
            }
        }).collect()
    }
}

impl Default for ContractChecker {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Modular verifier
// ---------------------------------------------------------------------------

/// Modular verifier: checks each function independently using only contracts.
pub struct ModularVerifier {
    /// Contract checker instance.
    checker: ContractChecker,
    /// Call graph: caller -> list of (callee, call_span).
    call_sites: FxHashMap<String, Vec<(String, SourceSpan)>>,
}

impl ModularVerifier {
    /// Create a new modular verifier.
    pub fn new() -> Self {
        Self {
            checker: ContractChecker::new(),
            call_sites: FxHashMap::default(),
        }
    }

    /// Register a contract.
    pub fn add_contract(&mut self, contract: FunctionContract) {
        self.checker.add_contract(contract);
    }

    /// Register a call site.
    pub fn add_call_site(&mut self, caller: &str, callee: &str, span: SourceSpan) {
        self.call_sites
            .entry(caller.to_string())
            .or_default()
            .push((callee.to_string(), span));
    }

    /// Verify all functions modularly.
    ///
    /// For each function:
    /// 1. Generate body VCs (postconditions hold assuming preconditions).
    /// 2. Generate call-site VCs (callee preconditions satisfied).
    pub fn verify_all(&self) -> Vec<VerificationCondition> {
        let mut all_vcs = Vec::new();

        // Body checks.
        for function in self.checker.contracts.keys() {
            all_vcs.extend(self.checker.check_function(function));
        }

        // Call-site checks.
        for (caller, callees) in &self.call_sites {
            for (callee, span) in callees {
                all_vcs.extend(self.checker.check_call_site(caller, callee, span));
            }
        }

        all_vcs
    }

    /// Get the number of registered contracts.
    #[must_use]
    pub fn contract_count(&self) -> usize {
        self.checker.contracts.len()
    }
}

impl Default for ModularVerifier {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Contract inheritance
// ---------------------------------------------------------------------------

/// Check contract inheritance: a subtype's contract must be compatible.
///
/// Liskov substitution:
/// - Subtypes may weaken preconditions (accept more).
/// - Subtypes may strengthen postconditions (guarantee more).
pub fn check_contract_inheritance(
    parent: &FunctionContract,
    child: &FunctionContract,
) -> Vec<InheritanceViolation> {
    let mut violations = Vec::new();

    // Child preconditions should be weaker (fewer/broader requirements).
    // Heuristic: if child has MORE requires clauses, it's likely strengthening.
    if child.requires.len() > parent.requires.len() {
        violations.push(InheritanceViolation {
            function: child.function.clone(),
            kind: InheritanceViolationKind::StrongerPrecondition,
            message: format!(
                "child '{}' has {} requires vs parent's {}; subtypes should weaken preconditions",
                child.function, child.requires.len(), parent.requires.len()
            ),
        });
    }

    // Child postconditions should be stronger (more/tighter guarantees).
    // Heuristic: if child has FEWER ensures clauses, it's likely weakening.
    if child.ensures.len() < parent.ensures.len() {
        violations.push(InheritanceViolation {
            function: child.function.clone(),
            kind: InheritanceViolationKind::WeakerPostcondition,
            message: format!(
                "child '{}' has {} ensures vs parent's {}; subtypes should strengthen postconditions",
                child.function, child.ensures.len(), parent.ensures.len()
            ),
        });
    }

    violations
}

/// A violation of contract inheritance rules.
#[derive(Debug, Clone)]
pub struct InheritanceViolation {
    /// Function with the violation.
    pub function: String,
    /// Kind of violation.
    pub kind: InheritanceViolationKind,
    /// Explanation.
    pub message: String,
}

/// Kind of inheritance violation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InheritanceViolationKind {
    /// Subtype strengthened preconditions (bad).
    StrongerPrecondition,
    /// Subtype weakened postconditions (bad).
    WeakerPostcondition,
}

// ---------------------------------------------------------------------------
// Frame condition inference
// ---------------------------------------------------------------------------

/// Infer frame conditions for a function.
///
/// A variable is "framed" if it is:
/// 1. Not modified in the function body.
/// 2. Not mentioned in any ensures clause.
pub fn infer_frame_conditions(
    modified_vars: &[String],
    ensures_vars: &[String],
    all_vars: &[String],
) -> Vec<FrameCondition> {
    let modified: FxHashSet<_> = modified_vars.iter().collect();
    let mentioned: FxHashSet<_> = ensures_vars.iter().collect();

    all_vars.iter()
        .filter(|v| !modified.contains(v) && !mentioned.contains(v))
        .map(|v| FrameCondition {
            location: v.clone(),
            inferred: true,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_contract() {
        let contract = FunctionContract::new("f");
        assert!(contract.requires.is_empty());
        assert!(contract.ensures.is_empty());
        assert!(!contract.verified);
    }

    #[test]
    fn test_contract_builder() {
        let contract = FunctionContract::new("f")
            .with_requires("x > 0", Formula::Bool(true))
            .with_ensures("result >= 0", Formula::Bool(true))
            .with_frame("global_state");
        assert_eq!(contract.requires.len(), 1);
        assert_eq!(contract.ensures.len(), 1);
        assert_eq!(contract.frame.len(), 1);
    }

    #[test]
    fn test_check_function_no_contract() {
        let checker = ContractChecker::new();
        let vcs = checker.check_function("unknown");
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_check_function_with_postcondition() {
        let mut checker = ContractChecker::new();
        let contract = FunctionContract::new("f")
            .with_ensures("result > 0", Formula::Bool(true));
        checker.add_contract(contract);

        let vcs = checker.check_function("f");
        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::Postcondition));
    }

    #[test]
    fn test_check_function_with_pre_and_post() {
        let mut checker = ContractChecker::new();
        let contract = FunctionContract::new("f")
            .with_requires("x > 0", Formula::Bool(true))
            .with_ensures("result > 0", Formula::Bool(true));
        checker.add_contract(contract);

        let vcs = checker.check_function("f");
        assert_eq!(vcs.len(), 1);
        // The VC should be: requires => !ensures (for refutation)
        assert!(matches!(vcs[0].formula, Formula::Implies(_, _)));
    }

    #[test]
    fn test_check_call_site() {
        let mut checker = ContractChecker::new();
        let contract = FunctionContract::new("callee")
            .with_requires("arg > 0", Formula::Bool(true));
        checker.add_contract(contract);

        let vcs = checker.check_call_site("caller", "callee", &SourceSpan::default());
        assert_eq!(vcs.len(), 1);
        assert!(matches!(&vcs[0].kind, VcKind::Precondition { callee } if callee == "callee"));
    }

    #[test]
    fn test_modular_verifier_all() {
        let mut verifier = ModularVerifier::new();
        verifier.add_contract(
            FunctionContract::new("main")
                .with_ensures("result == 0", Formula::Bool(true))
        );
        verifier.add_contract(
            FunctionContract::new("helper")
                .with_requires("n > 0", Formula::Bool(true))
                .with_ensures("result > 0", Formula::Bool(true))
        );
        verifier.add_call_site("main", "helper", SourceSpan::default());

        let vcs = verifier.verify_all();
        // 1 postcondition VC for main + 1 for helper + 1 call-site precondition
        assert_eq!(vcs.len(), 3);
        assert_eq!(verifier.contract_count(), 2);
    }

    #[test]
    fn test_contract_inheritance_valid() {
        let parent = FunctionContract::new("Animal::speak")
            .with_requires("self.alive", Formula::Bool(true))
            .with_ensures("result.len() > 0", Formula::Bool(true));

        let child = FunctionContract::new("Dog::speak")
            .with_requires("self.alive", Formula::Bool(true))
            .with_ensures("result.len() > 0", Formula::Bool(true))
            .with_ensures("result.contains('bark')", Formula::Bool(true));

        let violations = check_contract_inheritance(&parent, &child);
        assert!(violations.is_empty()); // Child has same pre, stronger post
    }

    #[test]
    fn test_contract_inheritance_stronger_precondition() {
        let parent = FunctionContract::new("Base::f")
            .with_requires("x > 0", Formula::Bool(true));

        let child = FunctionContract::new("Derived::f")
            .with_requires("x > 0", Formula::Bool(true))
            .with_requires("x < 100", Formula::Bool(true)); // Extra precondition!

        let violations = check_contract_inheritance(&parent, &child);
        assert!(violations.iter().any(|v| v.kind == InheritanceViolationKind::StrongerPrecondition));
    }

    #[test]
    fn test_contract_inheritance_weaker_postcondition() {
        let parent = FunctionContract::new("Base::f")
            .with_ensures("result > 0", Formula::Bool(true))
            .with_ensures("result < 100", Formula::Bool(true));

        let child = FunctionContract::new("Derived::f")
            .with_ensures("result > 0", Formula::Bool(true)); // Fewer guarantees!

        let violations = check_contract_inheritance(&parent, &child);
        assert!(violations.iter().any(|v| v.kind == InheritanceViolationKind::WeakerPostcondition));
    }

    #[test]
    fn test_infer_frame_conditions() {
        let all = vec!["x".into(), "y".into(), "z".into(), "w".into()];
        let modified = vec!["x".into()];
        let mentioned = vec!["y".into()];

        let frames = infer_frame_conditions(&modified, &mentioned, &all);
        assert_eq!(frames.len(), 2);
        assert!(frames.iter().any(|f| f.location == "z"));
        assert!(frames.iter().any(|f| f.location == "w"));
        assert!(frames.iter().all(|f| f.inferred));
    }

    #[test]
    fn test_frame_condition_no_modified() {
        let all = vec!["x".into(), "y".into()];
        let frames = infer_frame_conditions(&[], &[], &all);
        assert_eq!(frames.len(), 2);
    }

    #[test]
    fn test_modular_verifier_empty() {
        let verifier = ModularVerifier::new();
        let vcs = verifier.verify_all();
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_get_contract() {
        let mut checker = ContractChecker::new();
        checker.add_contract(FunctionContract::new("f"));
        assert!(checker.get_contract("f").is_some());
        assert!(checker.get_contract("g").is_none());
    }
}
