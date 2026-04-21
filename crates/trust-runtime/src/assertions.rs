// trust-runtime/assertions.rs: Runtime assertion injection (#255)
//
// Provides assertion injection for verified code: inserts runtime checks
// at key program points as a defense-in-depth measure alongside static proofs.
// Tracks assertion overhead and supports configurable assertion policies.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

// ---------------------------------------------------------------------------
// Assertion types
// ---------------------------------------------------------------------------

/// Kind of runtime assertion.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum AssertionKind {
    /// Precondition check at function entry.
    Precondition,
    /// Postcondition check at function exit.
    Postcondition,
    /// Loop invariant check at loop entry/exit.
    LoopInvariant,
    /// Type invariant check (e.g. non-null, in-range).
    TypeInvariant,
    /// Division-by-zero guard.
    DivisionGuard,
    /// Bounds check for array/slice access.
    BoundsCheck,
    /// Overflow check for arithmetic.
    OverflowCheck,
    /// Custom user assertion.
    Custom { tag: String },
}

impl std::fmt::Display for AssertionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Precondition => write!(f, "precondition"),
            Self::Postcondition => write!(f, "postcondition"),
            Self::LoopInvariant => write!(f, "loop_invariant"),
            Self::TypeInvariant => write!(f, "type_invariant"),
            Self::DivisionGuard => write!(f, "division_guard"),
            Self::BoundsCheck => write!(f, "bounds_check"),
            Self::OverflowCheck => write!(f, "overflow_check"),
            Self::Custom { tag } => write!(f, "custom({tag})"),
        }
    }
}

/// A runtime assertion to be injected into compiled code.
#[derive(Debug, Clone)]
pub(crate) struct RuntimeAssertion {
    /// Kind of assertion.
    pub kind: AssertionKind,
    /// Function where this assertion is injected.
    pub function: String,
    /// Human-readable condition expression.
    pub condition: String,
    /// Human-readable failure message.
    pub message: String,
    /// Estimated overhead in nanoseconds.
    pub overhead_ns: u64,
    /// Whether the assertion is enabled.
    pub enabled: bool,
}

impl RuntimeAssertion {
    /// Create a new assertion.
    pub(crate) fn new(
        kind: AssertionKind,
        function: impl Into<String>,
        condition: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        let kind_clone = kind.clone();
        Self {
            kind: kind_clone,
            function: function.into(),
            condition: condition.into(),
            message: message.into(),
            overhead_ns: estimate_overhead_ns(&kind),
            enabled: true,
        }
    }
}

/// Estimate the runtime overhead of an assertion kind in nanoseconds.
fn estimate_overhead_ns(kind: &AssertionKind) -> u64 {
    match kind {
        AssertionKind::Precondition => 5,
        AssertionKind::Postcondition => 5,
        AssertionKind::LoopInvariant => 10,
        AssertionKind::TypeInvariant => 3,
        AssertionKind::DivisionGuard => 2,
        AssertionKind::BoundsCheck => 2,
        AssertionKind::OverflowCheck => 3,
        AssertionKind::Custom { .. } => 10,
    }
}

// ---------------------------------------------------------------------------
// Assertion policy
// ---------------------------------------------------------------------------

/// Policy controlling which assertions to inject and overhead budget.
#[derive(Debug, Clone)]
pub(crate) struct AssertionPolicy {
    /// Maximum overhead budget per function in nanoseconds.
    pub max_overhead_ns: u64,
    /// Assertion kinds to include (empty = all).
    pub include_kinds: Vec<AssertionKind>,
    /// Assertion kinds to exclude.
    pub exclude_kinds: Vec<AssertionKind>,
    /// Whether to strip assertions for release builds.
    pub strip_in_release: bool,
}

impl Default for AssertionPolicy {
    fn default() -> Self {
        Self {
            max_overhead_ns: 100,
            include_kinds: Vec::new(),
            exclude_kinds: Vec::new(),
            strip_in_release: true,
        }
    }
}

impl AssertionPolicy {
    /// Check if an assertion kind is allowed by this policy.
    #[must_use]
    pub(crate) fn allows(&self, kind: &AssertionKind) -> bool {
        if self.exclude_kinds.contains(kind) {
            return false;
        }
        if self.include_kinds.is_empty() {
            return true;
        }
        self.include_kinds.contains(kind)
    }
}

// ---------------------------------------------------------------------------
// Assertion injector
// ---------------------------------------------------------------------------

/// Manages assertion injection for a program.
pub(crate) struct AssertionInjector {
    /// Assertions grouped by function.
    assertions: FxHashMap<String, Vec<RuntimeAssertion>>,
    /// Policy.
    policy: AssertionPolicy,
}

impl AssertionInjector {
    /// Create a new injector with the given policy.
    pub(crate) fn new(policy: AssertionPolicy) -> Self {
        Self {
            assertions: FxHashMap::default(),
            policy,
        }
    }

    /// Add an assertion if policy allows it and budget permits.
    pub(crate) fn add(&mut self, assertion: RuntimeAssertion) -> bool {
        if !self.policy.allows(&assertion.kind) {
            return false;
        }

        let func = assertion.function.clone();
        let current_overhead: u64 = self.assertions
            .get(&func)
            .map(|v| v.iter().map(|a| a.overhead_ns).sum())
            .unwrap_or(0);

        if current_overhead + assertion.overhead_ns > self.policy.max_overhead_ns {
            return false;
        }

        self.assertions.entry(func).or_default().push(assertion);
        true
    }

    /// Get all assertions for a function.
    #[must_use]
    pub(crate) fn get(&self, function: &str) -> &[RuntimeAssertion] {
        self.assertions.get(function).map_or(&[], |v| v.as_slice())
    }

    /// Get total assertion count.
    #[must_use]
    pub(crate) fn total_count(&self) -> usize {
        self.assertions.values().map(|v| v.len()).sum()
    }

    /// Get total overhead for a function.
    #[must_use]
    pub(crate) fn function_overhead_ns(&self, function: &str) -> u64 {
        self.assertions.get(function)
            .map(|v| v.iter().map(|a| a.overhead_ns).sum())
            .unwrap_or(0)
    }

    /// Generate a report of all injected assertions.
    #[must_use]
    pub(crate) fn report(&self) -> AssertionReport {
        let mut total_overhead = 0u64;
        let mut by_kind: FxHashMap<String, usize> = FxHashMap::default();
        let mut functions = Vec::new();

        for (func, asserts) in &self.assertions {
            let func_overhead: u64 = asserts.iter().map(|a| a.overhead_ns).sum();
            total_overhead += func_overhead;
            functions.push(func.clone());
            for a in asserts {
                *by_kind.entry(a.kind.to_string()).or_insert(0) += 1;
            }
        }

        functions.sort();

        AssertionReport {
            total_assertions: self.total_count(),
            total_overhead_ns: total_overhead,
            by_kind,
            functions,
        }
    }
}

impl Default for AssertionInjector {
    fn default() -> Self {
        Self::new(AssertionPolicy::default())
    }
}

/// Report summarizing injected assertions.
#[derive(Debug, Clone)]
pub(crate) struct AssertionReport {
    /// Total number of assertions.
    pub total_assertions: usize,
    /// Total estimated overhead in nanoseconds.
    pub total_overhead_ns: u64,
    /// Count by assertion kind.
    pub by_kind: FxHashMap<String, usize>,
    /// Functions with assertions.
    pub functions: Vec<String>,
}

/// Record of an assertion failure at runtime.
#[derive(Debug, Clone)]
pub(crate) struct AssertionFailure {
    /// Which assertion failed.
    pub kind: AssertionKind,
    /// Function where the failure occurred.
    pub function: String,
    /// The condition that was violated.
    pub condition: String,
    /// The failure message.
    pub message: String,
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_assertion_creation() {
        let a = RuntimeAssertion::new(
            AssertionKind::Precondition,
            "foo",
            "x > 0",
            "x must be positive",
        );
        assert_eq!(a.function, "foo");
        assert_eq!(a.condition, "x > 0");
        assert!(a.enabled);
        assert_eq!(a.overhead_ns, 5);
    }

    #[test]
    fn test_assertion_kind_display() {
        assert_eq!(AssertionKind::Precondition.to_string(), "precondition");
        assert_eq!(AssertionKind::BoundsCheck.to_string(), "bounds_check");
        let custom = AssertionKind::Custom { tag: "my_check".into() };
        assert_eq!(custom.to_string(), "custom(my_check)");
    }

    #[test]
    fn test_policy_allows_all_by_default() {
        let policy = AssertionPolicy::default();
        assert!(policy.allows(&AssertionKind::Precondition));
        assert!(policy.allows(&AssertionKind::BoundsCheck));
    }

    #[test]
    fn test_policy_exclude() {
        let policy = AssertionPolicy {
            exclude_kinds: vec![AssertionKind::OverflowCheck],
            ..Default::default()
        };
        assert!(!policy.allows(&AssertionKind::OverflowCheck));
        assert!(policy.allows(&AssertionKind::BoundsCheck));
    }

    #[test]
    fn test_policy_include_filter() {
        let policy = AssertionPolicy {
            include_kinds: vec![AssertionKind::Precondition, AssertionKind::Postcondition],
            ..Default::default()
        };
        assert!(policy.allows(&AssertionKind::Precondition));
        assert!(!policy.allows(&AssertionKind::BoundsCheck));
    }

    #[test]
    fn test_injector_add_and_get() {
        let mut injector = AssertionInjector::default();
        let a = RuntimeAssertion::new(AssertionKind::Precondition, "f", "x > 0", "positive");
        assert!(injector.add(a));
        assert_eq!(injector.get("f").len(), 1);
        assert_eq!(injector.total_count(), 1);
    }

    #[test]
    fn test_injector_respects_budget() {
        let policy = AssertionPolicy {
            max_overhead_ns: 5,
            ..Default::default()
        };
        let mut injector = AssertionInjector::new(policy);
        let a1 = RuntimeAssertion::new(AssertionKind::Precondition, "f", "x > 0", "pos");
        let a2 = RuntimeAssertion::new(AssertionKind::Postcondition, "f", "r > 0", "ret");
        assert!(injector.add(a1)); // 5ns, fits in 5ns budget
        assert!(!injector.add(a2)); // 5ns more would exceed
    }

    #[test]
    fn test_injector_respects_policy() {
        let policy = AssertionPolicy {
            exclude_kinds: vec![AssertionKind::OverflowCheck],
            ..Default::default()
        };
        let mut injector = AssertionInjector::new(policy);
        let a = RuntimeAssertion::new(AssertionKind::OverflowCheck, "f", "no overflow", "ov");
        assert!(!injector.add(a));
        assert_eq!(injector.total_count(), 0);
    }

    #[test]
    fn test_function_overhead() {
        let mut injector = AssertionInjector::default();
        injector.add(RuntimeAssertion::new(AssertionKind::DivisionGuard, "f", "y != 0", "div"));
        injector.add(RuntimeAssertion::new(AssertionKind::BoundsCheck, "f", "i < n", "oob"));
        assert_eq!(injector.function_overhead_ns("f"), 4); // 2 + 2
        assert_eq!(injector.function_overhead_ns("unknown"), 0);
    }

    #[test]
    fn test_report() {
        let mut injector = AssertionInjector::default();
        injector.add(RuntimeAssertion::new(AssertionKind::Precondition, "foo", "x > 0", "msg"));
        injector.add(RuntimeAssertion::new(AssertionKind::BoundsCheck, "bar", "i < n", "msg"));
        let report = injector.report();
        assert_eq!(report.total_assertions, 2);
        assert_eq!(report.functions.len(), 2);
        assert_eq!(*report.by_kind.get("precondition").unwrap(), 1);
        assert_eq!(*report.by_kind.get("bounds_check").unwrap(), 1);
    }

    #[test]
    fn test_estimate_overhead() {
        assert_eq!(estimate_overhead_ns(&AssertionKind::Precondition), 5);
        assert_eq!(estimate_overhead_ns(&AssertionKind::DivisionGuard), 2);
        assert_eq!(estimate_overhead_ns(&AssertionKind::LoopInvariant), 10);
    }

    #[test]
    fn test_empty_injector() {
        let injector = AssertionInjector::default();
        assert_eq!(injector.total_count(), 0);
        assert!(injector.get("any").is_empty());
        let report = injector.report();
        assert_eq!(report.total_assertions, 0);
        assert_eq!(report.total_overhead_ns, 0);
    }

    #[test]
    fn test_multiple_functions() {
        let mut injector = AssertionInjector::default();
        injector.add(RuntimeAssertion::new(AssertionKind::Precondition, "a", "x > 0", "m1"));
        injector.add(RuntimeAssertion::new(AssertionKind::Precondition, "b", "y > 0", "m2"));
        injector.add(RuntimeAssertion::new(AssertionKind::Postcondition, "a", "r >= 0", "m3"));
        assert_eq!(injector.get("a").len(), 2);
        assert_eq!(injector.get("b").len(), 1);
        assert_eq!(injector.total_count(), 3);
    }

    #[test]
    fn test_assertion_failure_struct() {
        let fail = AssertionFailure {
            kind: AssertionKind::DivisionGuard,
            function: "divide".into(),
            condition: "y != 0".into(),
            message: "division by zero".into(),
        };
        assert_eq!(fail.function, "divide");
        assert_eq!(fail.kind, AssertionKind::DivisionGuard);
    }
}
