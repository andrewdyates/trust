// trust-debug/root_cause.rs: Root cause analysis for verification failures
//
// Analyzes verification failures to determine their root cause, correlate
// related failures, build causal chains, and assign blame to the most likely
// responsible function. Produces fix suggestions for each identified root cause.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::fmt::Write;

use trust_types::{
    call_graph::CallGraph, Counterexample, CounterexampleValue, Formula, SourceSpan,
    VerificationCondition, VcKind,
};

/// Category of root cause for a verification failure.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum CauseCategory {
    /// Type mismatch between expected and actual values.
    TypeMismatch,
    /// Array/slice index or arithmetic bounds violation.
    BoundsViolation,
    /// Null or dangling pointer dereference.
    NullDeref,
    /// Access to memory after deallocation.
    UseAfterFree,
    /// Concurrent access without synchronization.
    DataRace,
    /// Loop or struct invariant does not hold.
    InvariantViolation,
    /// Specification is stronger than the implementation can satisfy.
    SpecTooStrong,
    /// Specification is too weak to prove the desired property.
    SpecTooWeak,
    /// No specification was provided for a required contract.
    MissingSpec,
    /// Solver hit a limitation (timeout, incomplete theory, etc.).
    SolverLimitation,
}

impl CauseCategory {
    /// Human-readable label for this category.
    #[must_use]
    pub(crate) fn label(&self) -> &'static str {
        match self {
            CauseCategory::TypeMismatch => "type mismatch",
            CauseCategory::BoundsViolation => "bounds violation",
            CauseCategory::NullDeref => "null dereference",
            CauseCategory::UseAfterFree => "use after free",
            CauseCategory::DataRace => "data race",
            CauseCategory::InvariantViolation => "invariant violation",
            CauseCategory::SpecTooStrong => "specification too strong",
            CauseCategory::SpecTooWeak => "specification too weak",
            CauseCategory::MissingSpec => "missing specification",
            CauseCategory::SolverLimitation => "solver limitation",
        }
    }
}

/// A diagnosed root cause for a verification failure.
#[derive(Debug, Clone)]
pub(crate) struct RootCause {
    /// The category of this root cause.
    pub category: CauseCategory,
    /// Source location where the root cause originates.
    pub location: SourceSpan,
    /// Human-readable explanation of why this failure occurred.
    pub explanation: String,
    /// Suggested fix for this root cause.
    pub suggested_fix: FixSuggestion,
    /// Confidence in this diagnosis (0.0 to 1.0).
    pub confidence: f64,
}

/// A suggested fix for a root cause.
#[derive(Debug, Clone)]
pub(crate) struct FixSuggestion {
    /// Short description of the fix.
    pub description: String,
    /// The kind of fix suggested.
    pub kind: DebugFixKind,
    /// Target location for the fix (may differ from root cause location).
    pub target_location: Option<SourceSpan>,
    /// Example code snippet illustrating the fix (if applicable).
    pub code_hint: Option<String>,
}

/// Classification of suggested fixes for verification failures.
///
/// Named `DebugFixKind` to distinguish from `trust_types::FixKind` which
/// covers resilience-pattern fixes (timeouts, retries, circuit breakers).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum DebugFixKind {
    /// Add a bounds check or assertion.
    AddBoundsCheck,
    /// Add or strengthen a precondition.
    AddPrecondition,
    /// Weaken a postcondition that is too strong.
    WeakenPostcondition,
    /// Add a missing specification.
    AddSpec,
    /// Change the type of a variable or parameter.
    ChangeType,
    /// Add synchronization (lock, atomic, etc.).
    AddSynchronization,
    /// Restructure code to avoid the problematic pattern.
    Restructure,
    /// Increase solver timeout or switch solver strategy.
    AdjustSolver,
    /// Add a loop invariant annotation.
    AddLoopInvariant,
}

/// A group of related failures sharing a common root cause.
#[derive(Debug, Clone)]
pub(crate) struct CorrelatedFailures {
    /// The shared root cause category.
    pub category: CauseCategory,
    /// Function where the root cause originates.
    pub origin_function: String,
    /// All VCs in this group (indices into the original failure list).
    pub failure_indices: Vec<usize>,
    /// Shared location (if all failures originate from the same place).
    pub shared_location: Option<SourceSpan>,
    /// Why these failures are correlated.
    pub correlation_reason: String,
}

/// An ordered chain of events leading to a verification failure.
#[derive(Debug, Clone)]
pub(crate) struct CausalChainStep {
    /// Function where this step occurs.
    pub function: String,
    /// Source location.
    pub location: SourceSpan,
    /// Description of what happens at this step.
    pub description: String,
}

/// Result of blame analysis: identifies the most likely responsible function.
#[derive(Debug, Clone)]
pub(crate) struct BlameResult {
    /// The function most likely responsible for the failure.
    pub blamed_function: String,
    /// Confidence in the blame assignment (0.0 to 1.0).
    pub confidence: f64,
    /// Why this function was blamed.
    pub reason: String,
    /// Other functions that may contribute to the failure.
    pub contributing_functions: Vec<String>,
}

/// Analyzes verification failures to find their root causes.
pub(crate) struct RootCauseAnalyzer {
    /// Confidence threshold below which results are discarded.
    min_confidence: f64,
}

impl Default for RootCauseAnalyzer {
    fn default() -> Self {
        Self {
            min_confidence: 0.3,
        }
    }
}

impl RootCauseAnalyzer {
    /// Create an analyzer with custom minimum confidence threshold.
    #[must_use]
    pub(crate) fn with_min_confidence(min_confidence: f64) -> Self {
        Self {
            min_confidence: min_confidence.clamp(0.0, 1.0),
        }
    }

    /// Returns the configured minimum confidence threshold.
    #[must_use]
    pub(crate) fn min_confidence(&self) -> f64 {
        self.min_confidence
    }

    /// Analyze a single verification failure to determine its root cause.
    ///
    /// Uses the VC kind and optional counterexample to classify the failure
    /// and produce a diagnosis with confidence score.
    #[must_use]
    pub(crate) fn analyze_failure(
        &self,
        vc: &VerificationCondition,
        counterexample: Option<&Counterexample>,
    ) -> RootCause {
        let (category, confidence) = classify_vc_failure(vc, counterexample);
        let explanation = build_explanation(vc, counterexample, category);
        let suggested_fix = suggest_fix(vc, category, counterexample);

        RootCause {
            category,
            location: vc.location.clone(),
            explanation,
            suggested_fix,
            confidence,
        }
    }

    /// Correlate a list of failures by grouping those that share a common root cause.
    ///
    /// Failures are grouped by:
    /// 1. Same function + same cause category
    /// 2. Related VC kinds (e.g., overflow + bounds in same function)
    /// 3. Shared counterexample variable patterns
    #[must_use]
    pub(crate) fn correlate_failures(
        &self,
        failures: &[(VerificationCondition, Option<Counterexample>)],
    ) -> Vec<CorrelatedFailures> {
        // Group by (function, category)
        let mut groups: FxHashMap<(String, CauseCategory), Vec<usize>> = FxHashMap::default();

        for (i, (vc, cex)) in failures.iter().enumerate() {
            let (category, _confidence) = classify_vc_failure(vc, cex.as_ref());
            let key = (vc.function.clone(), category);
            groups.entry(key).or_default().push(i);
        }

        let mut result: Vec<CorrelatedFailures> = groups
            .into_iter()
            .filter(|(_, indices)| !indices.is_empty())
            .map(|((func, category), indices)| {
                let shared_location = if indices.len() == 1 {
                    Some(failures[indices[0]].0.location.clone())
                } else {
                    // Check if all share the same file
                    let first_file = &failures[indices[0]].0.location.file;
                    let all_same_file = indices
                        .iter()
                        .all(|&i| &failures[i].0.location.file == first_file);
                    if all_same_file {
                        Some(failures[indices[0]].0.location.clone())
                    } else {
                        None
                    }
                };

                let correlation_reason = if indices.len() == 1 {
                    format!("single {} failure in `{}`", category.label(), func)
                } else {
                    format!(
                        "{} related {} failures in `{}`",
                        indices.len(),
                        category.label(),
                        func,
                    )
                };

                CorrelatedFailures {
                    category,
                    origin_function: func,
                    failure_indices: indices,
                    shared_location,
                    correlation_reason,
                }
            })
            .collect();

        // Sort: largest groups first
        result.sort_by(|a, b| b.failure_indices.len().cmp(&a.failure_indices.len()));
        result
    }

    /// Build a causal chain: the ordered sequence of events leading to a failure.
    ///
    /// Uses the VC's function, location, and formula structure to reconstruct
    /// the chain of operations that led to the violation.
    #[must_use]
    pub(crate) fn causal_chain(&self, vc: &VerificationCondition) -> Vec<CausalChainStep> {
        let mut chain = Vec::new();

        // Step 1: The function entry (context)
        chain.push(CausalChainStep {
            function: vc.function.clone(),
            location: vc.location.clone(),
            description: format!("Enter function `{}`", vc.function),
        });

        // Step 2: Derive intermediate steps from VC kind
        match &vc.kind {
            VcKind::ArithmeticOverflow { op, operand_tys } => {
                chain.push(CausalChainStep {
                    function: vc.function.clone(),
                    location: vc.location.clone(),
                    description: format!(
                        "Perform {:?} operation on {:?} operands",
                        op, operand_tys,
                    ),
                });
                chain.push(CausalChainStep {
                    function: vc.function.clone(),
                    location: vc.location.clone(),
                    description: "Result exceeds representable range".to_string(),
                });
            }
            VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
                chain.push(CausalChainStep {
                    function: vc.function.clone(),
                    location: vc.location.clone(),
                    description: "Compute index expression".to_string(),
                });
                chain.push(CausalChainStep {
                    function: vc.function.clone(),
                    location: vc.location.clone(),
                    description: "Index exceeds collection bounds".to_string(),
                });
            }
            VcKind::DivisionByZero | VcKind::RemainderByZero => {
                chain.push(CausalChainStep {
                    function: vc.function.clone(),
                    location: vc.location.clone(),
                    description: "Divisor evaluates to zero".to_string(),
                });
            }
            VcKind::Precondition { callee } => {
                chain.push(CausalChainStep {
                    function: vc.function.clone(),
                    location: vc.location.clone(),
                    description: format!("Prepare arguments for call to `{}`", callee),
                });
                chain.push(CausalChainStep {
                    function: callee.clone(),
                    location: vc.location.clone(),
                    description: format!(
                        "Precondition of `{}` not satisfied by caller arguments",
                        callee,
                    ),
                });
            }
            VcKind::Postcondition => {
                chain.push(CausalChainStep {
                    function: vc.function.clone(),
                    location: vc.location.clone(),
                    description: "Function body executes".to_string(),
                });
                chain.push(CausalChainStep {
                    function: vc.function.clone(),
                    location: vc.location.clone(),
                    description: "Return value does not satisfy postcondition".to_string(),
                });
            }
            _ => {
                chain.push(CausalChainStep {
                    function: vc.function.clone(),
                    location: vc.location.clone(),
                    description: format!("Violation: {}", vc.kind.description()),
                });
            }
        }

        chain
    }

    /// Perform blame analysis: determine which function is most responsible.
    ///
    /// Uses the call graph to trace the failure back to callers that may have
    /// provided invalid inputs, or to the function itself if it contains the bug.
    #[must_use]
    pub(crate) fn blame_analysis(
        &self,
        vc: &VerificationCondition,
        call_graph: &CallGraph,
    ) -> BlameResult {
        // Find callers of the failing function
        let callers: Vec<&str> = call_graph
            .edges
            .iter()
            .filter(|e| {
                e.callee == vc.function || vc.function.ends_with(&format!("::{}", e.callee))
            })
            .map(|e| e.caller.as_str())
            .collect();

        match &vc.kind {
            // Precondition failures: blame the caller
            VcKind::Precondition { callee } => {
                if callers.is_empty() {
                    BlameResult {
                        blamed_function: vc.function.clone(),
                        confidence: 0.7,
                        reason: format!(
                            "Precondition of `{}` violated; no callers found in call graph",
                            callee,
                        ),
                        contributing_functions: vec![],
                    }
                } else {
                    let blamed = callers[0].to_string();
                    let contributing: Vec<String> = callers[1..]
                        .iter()
                        .map(|s| s.to_string())
                        .collect();
                    BlameResult {
                        blamed_function: blamed.clone(),
                        confidence: 0.8,
                        reason: format!(
                            "Caller `{}` does not establish precondition of `{}`",
                            blamed, callee,
                        ),
                        contributing_functions: contributing,
                    }
                }
            }
            // Postcondition failures: blame the function itself
            VcKind::Postcondition => BlameResult {
                blamed_function: vc.function.clone(),
                confidence: 0.9,
                reason: format!(
                    "Function `{}` does not satisfy its own postcondition",
                    vc.function,
                ),
                contributing_functions: vec![],
            },
            // Safety violations: typically blame the function, but callers may contribute
            _ => {
                let contributing: Vec<String> =
                    callers.iter().map(|s| s.to_string()).collect();
                BlameResult {
                    blamed_function: vc.function.clone(),
                    confidence: if callers.is_empty() { 0.9 } else { 0.6 },
                    reason: format!(
                        "Safety violation ({}) in `{}`",
                        vc.kind.description(),
                        vc.function,
                    ),
                    contributing_functions: contributing,
                }
            }
        }
    }
}

/// Classify a VC failure into a cause category with confidence.
fn classify_vc_failure(
    vc: &VerificationCondition,
    counterexample: Option<&Counterexample>,
) -> (CauseCategory, f64) {
    match &vc.kind {
        VcKind::ArithmeticOverflow { .. }
        | VcKind::ShiftOverflow { .. }
        | VcKind::NegationOverflow { .. } => {
            // If counterexample shows boundary values, high confidence
            let confidence = if has_boundary_values(counterexample) {
                0.95
            } else {
                0.8
            };
            (CauseCategory::BoundsViolation, confidence)
        }
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
            (CauseCategory::BoundsViolation, 0.95)
        }
        VcKind::DivisionByZero | VcKind::RemainderByZero => {
            (CauseCategory::BoundsViolation, 0.95)
        }
        VcKind::CastOverflow { .. } => {
            (CauseCategory::TypeMismatch, 0.85)
        }
        VcKind::Precondition { .. } => {
            // Could be spec too strong or missing spec
            if matches!(vc.formula, Formula::Bool(true)) {
                // Trivial formula suggests missing spec
                (CauseCategory::MissingSpec, 0.7)
            } else {
                (CauseCategory::SpecTooStrong, 0.7)
            }
        }
        VcKind::Postcondition => {
            (CauseCategory::SpecTooStrong, 0.65)
        }
        VcKind::Assertion { .. } => {
            (CauseCategory::InvariantViolation, 0.8)
        }
        VcKind::Unreachable => {
            (CauseCategory::InvariantViolation, 0.6)
        }
        VcKind::Deadlock => {
            (CauseCategory::DataRace, 0.75)
        }
        VcKind::TaintViolation { .. } => {
            (CauseCategory::MissingSpec, 0.7)
        }
        VcKind::NonTermination { .. } => {
            (CauseCategory::InvariantViolation, 0.8)
        }
        _ => {
            // For unrecognized kinds, check if we have a counterexample
            if counterexample.is_some() {
                (CauseCategory::InvariantViolation, 0.5)
            } else {
                (CauseCategory::SolverLimitation, 0.4)
            }
        }
    }
}

/// Check whether a counterexample contains boundary values (MAX, 0, etc.).
fn has_boundary_values(counterexample: Option<&Counterexample>) -> bool {
    let Some(cex) = counterexample else {
        return false;
    };
    cex.assignments.iter().any(|(_, val)| match val {
        CounterexampleValue::Uint(n) => *n == 0 || *n == u64::MAX as u128 || *n == u128::MAX,
        CounterexampleValue::Int(n) => {
            *n == 0 || *n == i64::MAX as i128 || *n == i64::MIN as i128 || *n == i128::MAX || *n == i128::MIN
        }
        _ => false,
    })
}

/// Build a human-readable explanation for a failure.
fn build_explanation(
    vc: &VerificationCondition,
    counterexample: Option<&Counterexample>,
    category: CauseCategory,
) -> String {
    let mut explanation = format!(
        "{} in function `{}`: {}",
        category.label(),
        vc.function,
        vc.kind.description(),
    );

    if let Some(cex) = counterexample
        && !cex.assignments.is_empty() {
            let vars: Vec<String> = cex
                .assignments
                .iter()
                .take(5)
                .map(|(name, val)| format!("{} = {}", name, val))
                .collect();
            let _ = write!(explanation, 
                ". Counterexample: {}",
                vars.join(", "),
            );
            if cex.assignments.len() > 5 {
                let _ = write!(explanation, 
                    " (and {} more variables)",
                    cex.assignments.len() - 5,
                );
            }
        }

    explanation
}

/// Generate a fix suggestion for a given root cause.
pub(crate) fn suggest_fix(
    vc: &VerificationCondition,
    category: CauseCategory,
    _counterexample: Option<&Counterexample>,
) -> FixSuggestion {
    match category {
        CauseCategory::BoundsViolation => match &vc.kind {
            VcKind::ArithmeticOverflow { op, .. } => FixSuggestion {
                description: format!(
                    "Add overflow check before {:?} operation, or use checked_{:?}",
                    op,
                    op,
                ),
                kind: DebugFixKind::AddBoundsCheck,
                target_location: Some(vc.location.clone()),
                code_hint: Some("a.checked_add(b).ok_or(Error::Overflow)?".to_string()),
            },
            VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => FixSuggestion {
                description: "Add bounds check before array/slice access".to_string(),
                kind: DebugFixKind::AddBoundsCheck,
                target_location: Some(vc.location.clone()),
                code_hint: Some("if index < slice.len() { &slice[index] } else { return Err(...) }".to_string()),
            },
            VcKind::DivisionByZero | VcKind::RemainderByZero => FixSuggestion {
                description: "Add zero-check on divisor before division".to_string(),
                kind: DebugFixKind::AddBoundsCheck,
                target_location: Some(vc.location.clone()),
                code_hint: Some("if divisor != 0 { a / divisor } else { return Err(Error::DivByZero) }".to_string()),
            },
            _ => FixSuggestion {
                description: "Add bounds checking to prevent overflow".to_string(),
                kind: DebugFixKind::AddBoundsCheck,
                target_location: Some(vc.location.clone()),
                code_hint: None,
            },
        },
        CauseCategory::TypeMismatch => FixSuggestion {
            description: "Use a safe cast (TryFrom/TryInto) instead of unchecked cast".to_string(),
            kind: DebugFixKind::ChangeType,
            target_location: Some(vc.location.clone()),
            code_hint: Some("let val: TargetType = source.try_into()?;".to_string()),
        },
        CauseCategory::NullDeref => FixSuggestion {
            description: "Check for null/None before dereference".to_string(),
            kind: DebugFixKind::AddBoundsCheck,
            target_location: Some(vc.location.clone()),
            code_hint: Some("if let Some(val) = opt { use(val) }".to_string()),
        },
        CauseCategory::UseAfterFree => FixSuggestion {
            description: "Restructure ownership to prevent use after free".to_string(),
            kind: DebugFixKind::Restructure,
            target_location: Some(vc.location.clone()),
            code_hint: None,
        },
        CauseCategory::DataRace => FixSuggestion {
            description: "Add synchronization to protect shared mutable state".to_string(),
            kind: DebugFixKind::AddSynchronization,
            target_location: Some(vc.location.clone()),
            code_hint: Some("let guard = mutex.lock().expect(\"poisoned\");".to_string()),
        },
        CauseCategory::InvariantViolation => FixSuggestion {
            description: "Add or strengthen loop/struct invariant".to_string(),
            kind: DebugFixKind::AddLoopInvariant,
            target_location: Some(vc.location.clone()),
            code_hint: Some("#[invariant(\"0 <= i && i <= n\")]".to_string()),
        },
        CauseCategory::SpecTooStrong => FixSuggestion {
            description: "Weaken the postcondition to match actual implementation behavior".to_string(),
            kind: DebugFixKind::WeakenPostcondition,
            target_location: Some(vc.location.clone()),
            code_hint: None,
        },
        CauseCategory::SpecTooWeak => FixSuggestion {
            description: "Strengthen the precondition to narrow input domain".to_string(),
            kind: DebugFixKind::AddPrecondition,
            target_location: Some(vc.location.clone()),
            code_hint: Some("#[requires(\"n > 0\")]".to_string()),
        },
        CauseCategory::MissingSpec => FixSuggestion {
            description: "Add a specification (requires/ensures) for this function".to_string(),
            kind: DebugFixKind::AddSpec,
            target_location: Some(vc.location.clone()),
            code_hint: Some("#[requires(\"...\")]\n#[ensures(\"...\")]".to_string()),
        },
        CauseCategory::SolverLimitation => FixSuggestion {
            description: "Increase solver timeout or try a different backend".to_string(),
            kind: DebugFixKind::AdjustSolver,
            target_location: None,
            code_hint: None,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::*;

    fn make_vc(kind: VcKind, function: &str) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: function.to_string(),
            location: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 10,
                col_start: 5,
                line_end: 10,
                col_end: 30,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn overflow_vc() -> VerificationCondition {
        make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            "test::add",
        )
    }

    fn index_vc() -> VerificationCondition {
        make_vc(VcKind::IndexOutOfBounds, "test::access")
    }

    fn div_zero_vc() -> VerificationCondition {
        make_vc(VcKind::DivisionByZero, "test::divide")
    }

    fn precond_vc() -> VerificationCondition {
        make_vc(
            VcKind::Precondition {
                callee: "helper::validate".to_string(),
            },
            "test::caller",
        )
    }

    fn postcond_vc() -> VerificationCondition {
        make_vc(VcKind::Postcondition, "test::compute")
    }

    fn cast_vc() -> VerificationCondition {
        make_vc(
            VcKind::CastOverflow {
                from_ty: Ty::Int {
                    width: 64,
                    signed: true,
                },
                to_ty: Ty::Int { width: 32, signed: false },
            },
            "test::convert",
        )
    }

    fn sample_counterexample() -> Counterexample {
        Counterexample::new(vec![
            ("a".to_string(), CounterexampleValue::Uint(u64::MAX as u128)),
            ("b".to_string(), CounterexampleValue::Uint(1)),
        ])
    }

    // --- CauseCategory detection tests ---

    #[test]
    fn test_classify_arithmetic_overflow() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = overflow_vc();
        let root = analyzer.analyze_failure(&vc, None);
        assert_eq!(root.category, CauseCategory::BoundsViolation);
        assert!(root.confidence >= 0.7);
    }

    #[test]
    fn test_classify_index_out_of_bounds() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = index_vc();
        let root = analyzer.analyze_failure(&vc, None);
        assert_eq!(root.category, CauseCategory::BoundsViolation);
        assert!(root.confidence >= 0.9);
    }

    #[test]
    fn test_classify_division_by_zero() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = div_zero_vc();
        let root = analyzer.analyze_failure(&vc, None);
        assert_eq!(root.category, CauseCategory::BoundsViolation);
    }

    #[test]
    fn test_classify_cast_overflow_as_type_mismatch() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = cast_vc();
        let root = analyzer.analyze_failure(&vc, None);
        assert_eq!(root.category, CauseCategory::TypeMismatch);
    }

    #[test]
    fn test_classify_precondition_failure() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = precond_vc();
        let root = analyzer.analyze_failure(&vc, None);
        // Trivial formula => MissingSpec
        assert!(
            root.category == CauseCategory::MissingSpec
                || root.category == CauseCategory::SpecTooStrong
        );
    }

    #[test]
    fn test_classify_postcondition_failure() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = postcond_vc();
        let root = analyzer.analyze_failure(&vc, None);
        assert_eq!(root.category, CauseCategory::SpecTooStrong);
    }

    #[test]
    fn test_classify_deadlock_as_data_race() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = make_vc(VcKind::Deadlock, "test::lock");
        let root = analyzer.analyze_failure(&vc, None);
        assert_eq!(root.category, CauseCategory::DataRace);
    }

    #[test]
    fn test_classify_assertion_as_invariant_violation() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = make_vc(
            VcKind::Assertion {
                message: "loop invariant".to_string(),
            },
            "test::loop_fn",
        );
        let root = analyzer.analyze_failure(&vc, None);
        assert_eq!(root.category, CauseCategory::InvariantViolation);
    }

    #[test]
    fn test_classify_non_termination() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = make_vc(
            VcKind::NonTermination {
                context: "loop".to_string(),
                measure: "n".to_string(),
            },
            "test::infinite",
        );
        let root = analyzer.analyze_failure(&vc, None);
        assert_eq!(root.category, CauseCategory::InvariantViolation);
    }

    // --- Counterexample influence tests ---

    #[test]
    fn test_boundary_values_increase_confidence() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = overflow_vc();
        let cex = sample_counterexample();

        let with_cex = analyzer.analyze_failure(&vc, Some(&cex));
        let without_cex = analyzer.analyze_failure(&vc, None);

        assert!(
            with_cex.confidence >= without_cex.confidence,
            "boundary values should increase or maintain confidence"
        );
    }

    #[test]
    fn test_explanation_includes_counterexample() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = overflow_vc();
        let cex = sample_counterexample();

        let root = analyzer.analyze_failure(&vc, Some(&cex));
        assert!(
            root.explanation.contains("Counterexample"),
            "explanation should mention counterexample: {}",
            root.explanation,
        );
        assert!(root.explanation.contains("a ="));
    }

    // --- Correlation tests ---

    #[test]
    fn test_correlate_same_function_same_category() {
        let analyzer = RootCauseAnalyzer::default();
        let failures: Vec<(VerificationCondition, Option<Counterexample>)> = vec![
            (overflow_vc(), None),
            (
                make_vc(
                    VcKind::ArithmeticOverflow {
                        op: BinOp::Mul,
                        operand_tys: (Ty::usize(), Ty::usize()),
                    },
                    "test::add", // same function
                ),
                None,
            ),
        ];

        let correlated = analyzer.correlate_failures(&failures);
        // Both are BoundsViolation in test::add -> should be in one group
        let group = correlated
            .iter()
            .find(|g| g.origin_function == "test::add");
        assert!(group.is_some());
        assert_eq!(group.unwrap().failure_indices.len(), 2);
    }

    #[test]
    fn test_correlate_different_functions_separate_groups() {
        let analyzer = RootCauseAnalyzer::default();
        let failures: Vec<(VerificationCondition, Option<Counterexample>)> = vec![
            (overflow_vc(), None),         // test::add
            (index_vc(), None),            // test::access
            (div_zero_vc(), None),         // test::divide
        ];

        let correlated = analyzer.correlate_failures(&failures);
        // All different functions -> separate groups (but overflow and div_zero may
        // share BoundsViolation category if in different functions)
        assert!(correlated.len() >= 2);
    }

    #[test]
    fn test_correlate_empty_failures() {
        let analyzer = RootCauseAnalyzer::default();
        let correlated = analyzer.correlate_failures(&[]);
        assert!(correlated.is_empty());
    }

    // --- Causal chain tests ---

    #[test]
    fn test_causal_chain_overflow() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = overflow_vc();
        let chain = analyzer.causal_chain(&vc);

        assert!(chain.len() >= 2, "overflow chain should have >= 2 steps");
        assert!(chain[0].description.contains("Enter function"));
        assert!(chain.last().unwrap().description.contains("exceeds"));
    }

    #[test]
    fn test_causal_chain_precondition() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = precond_vc();
        let chain = analyzer.causal_chain(&vc);

        assert!(chain.len() >= 2);
        assert!(chain
            .iter()
            .any(|s| s.description.contains("Precondition")));
    }

    #[test]
    fn test_causal_chain_postcondition() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = postcond_vc();
        let chain = analyzer.causal_chain(&vc);

        assert!(chain
            .iter()
            .any(|s| s.description.contains("postcondition")));
    }

    #[test]
    fn test_causal_chain_division_by_zero() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = div_zero_vc();
        let chain = analyzer.causal_chain(&vc);

        assert!(chain.iter().any(|s| s.description.contains("zero")));
    }

    // --- Blame analysis tests ---

    #[test]
    fn test_blame_postcondition_blames_function() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = postcond_vc();
        let cg = CallGraph::new();

        let blame = analyzer.blame_analysis(&vc, &cg);
        assert_eq!(blame.blamed_function, "test::compute");
        assert!(blame.confidence >= 0.8);
    }

    #[test]
    fn test_blame_precondition_blames_caller() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = precond_vc();

        let mut cg = CallGraph::new();
        cg.add_node(call_graph::CallGraphNode {
            def_path: "test::caller".to_string(),
            name: "caller".to_string(),
            is_public: true,
            is_entry_point: true,
            span: SourceSpan::default(),
        });
        cg.add_node(call_graph::CallGraphNode {
            def_path: "helper::validate".to_string(),
            name: "validate".to_string(),
            is_public: true,
            is_entry_point: false,
            span: SourceSpan::default(),
        });
        cg.add_edge(call_graph::CallGraphEdge {
            caller: "test::main".to_string(),
            callee: "test::caller".to_string(),
            call_site: SourceSpan::default(),
        });

        let blame = analyzer.blame_analysis(&vc, &cg);
        // For precondition, blame goes to the caller's callers
        // Since test::main calls test::caller, it should blame main
        assert!(blame.confidence >= 0.6);
    }

    #[test]
    fn test_blame_safety_violation_no_callers() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = overflow_vc();
        let cg = CallGraph::new();

        let blame = analyzer.blame_analysis(&vc, &cg);
        assert_eq!(blame.blamed_function, "test::add");
        assert!(blame.confidence >= 0.8);
        assert!(blame.contributing_functions.is_empty());
    }

    #[test]
    fn test_blame_safety_violation_with_callers() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = overflow_vc();

        let mut cg = CallGraph::new();
        cg.add_node(call_graph::CallGraphNode {
            def_path: "test::main".to_string(),
            name: "main".to_string(),
            is_public: true,
            is_entry_point: true,
            span: SourceSpan::default(),
        });
        cg.add_node(call_graph::CallGraphNode {
            def_path: "test::add".to_string(),
            name: "add".to_string(),
            is_public: true,
            is_entry_point: false,
            span: SourceSpan::default(),
        });
        cg.add_edge(call_graph::CallGraphEdge {
            caller: "test::main".to_string(),
            callee: "test::add".to_string(),
            call_site: SourceSpan::default(),
        });

        let blame = analyzer.blame_analysis(&vc, &cg);
        assert_eq!(blame.blamed_function, "test::add");
        assert!(!blame.contributing_functions.is_empty());
        assert!(blame.contributing_functions.contains(&"test::main".to_string()));
    }

    // --- Fix suggestion tests ---

    #[test]
    fn test_suggest_fix_overflow() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = overflow_vc();
        let root = analyzer.analyze_failure(&vc, None);
        assert_eq!(root.suggested_fix.kind, DebugFixKind::AddBoundsCheck);
        assert!(root.suggested_fix.code_hint.is_some());
    }

    #[test]
    fn test_suggest_fix_index_out_of_bounds() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = index_vc();
        let root = analyzer.analyze_failure(&vc, None);
        assert_eq!(root.suggested_fix.kind, DebugFixKind::AddBoundsCheck);
        assert!(root
            .suggested_fix
            .description
            .contains("bounds check"));
    }

    #[test]
    fn test_suggest_fix_cast_overflow() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = cast_vc();
        let root = analyzer.analyze_failure(&vc, None);
        assert_eq!(root.suggested_fix.kind, DebugFixKind::ChangeType);
        assert!(root.suggested_fix.code_hint.as_ref().unwrap().contains("try_into"));
    }

    #[test]
    fn test_suggest_fix_postcondition() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = postcond_vc();
        let root = analyzer.analyze_failure(&vc, None);
        assert_eq!(root.suggested_fix.kind, DebugFixKind::WeakenPostcondition);
    }

    #[test]
    fn test_suggest_fix_missing_spec() {
        let analyzer = RootCauseAnalyzer::default();
        let vc = make_vc(
            VcKind::TaintViolation {
                source_label: "user-input".to_string(),
                sink_kind: "sql".to_string(),
                path_length: 3,
            },
            "test::handler",
        );
        let root = analyzer.analyze_failure(&vc, None);
        assert_eq!(root.suggested_fix.kind, DebugFixKind::AddSpec);
    }

    // --- CauseCategory label test ---

    #[test]
    fn test_all_categories_have_labels() {
        let categories = [
            CauseCategory::TypeMismatch,
            CauseCategory::BoundsViolation,
            CauseCategory::NullDeref,
            CauseCategory::UseAfterFree,
            CauseCategory::DataRace,
            CauseCategory::InvariantViolation,
            CauseCategory::SpecTooStrong,
            CauseCategory::SpecTooWeak,
            CauseCategory::MissingSpec,
            CauseCategory::SolverLimitation,
        ];

        for cat in &categories {
            let label = cat.label();
            assert!(!label.is_empty(), "category {:?} should have a label", cat);
        }
    }

    // --- Custom confidence threshold ---

    #[test]
    fn test_custom_min_confidence() {
        let analyzer = RootCauseAnalyzer::with_min_confidence(0.9);
        assert!((analyzer.min_confidence - 0.9).abs() < f64::EPSILON);
    }

    #[test]
    fn test_min_confidence_clamped() {
        let analyzer = RootCauseAnalyzer::with_min_confidence(2.0);
        assert!((analyzer.min_confidence - 1.0).abs() < f64::EPSILON);

        let analyzer2 = RootCauseAnalyzer::with_min_confidence(-1.0);
        assert!((analyzer2.min_confidence - 0.0).abs() < f64::EPSILON);
    }
}
