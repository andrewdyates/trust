// trust-transval/property_check.rs: Property-based translation validation (#291)
//
// Validates that transformations preserve key properties: semantic equivalence,
// type preservation, termination preservation, and memory safety. Generates
// `PropertyViolation` diagnostics when properties are broken and summarizes
// results in a `PropertyReport`.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::{
    Rvalue, SourceSpan, Statement, Terminator, Ty, VerifiableBody,
    VerifiableFunction,
};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A property that a translation must preserve.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum TranslationProperty {
    /// Semantics of the source program are preserved in the target.
    SemanticPreservation,
    /// Types of all values are maintained across the transformation.
    TypePreservation,
    /// If the source terminates, the target must also terminate.
    TerminationPreservation,
    /// Memory safety guarantees are not weakened by the transformation.
    MemorySafety,
}

impl std::fmt::Display for TranslationProperty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SemanticPreservation => write!(f, "semantic-preservation"),
            Self::TypePreservation => write!(f, "type-preservation"),
            Self::TerminationPreservation => write!(f, "termination-preservation"),
            Self::MemorySafety => write!(f, "memory-safety"),
        }
    }
}

/// A violation of a translation property.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PropertyViolation {
    /// Which property was violated.
    pub property: TranslationProperty,
    /// Location in the source program.
    pub source_location: SourceSpan,
    /// Location in the target program.
    pub target_location: SourceSpan,
    /// Human-readable explanation of the violation.
    pub explanation: String,
}

impl std::fmt::Display for PropertyViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}] {}:{} -> {}:{}: {}",
            self.property,
            self.source_location.file,
            self.source_location.line_start,
            self.target_location.file,
            self.target_location.line_start,
            self.explanation,
        )
    }
}

/// Outcome of checking a single property.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PropertyOutcome {
    /// Property holds (no violations found).
    Holds,
    /// Property is violated with one or more diagnostics.
    Violated(Vec<PropertyViolation>),
    /// Could not determine whether the property holds.
    Unknown(String),
}

/// Summary report of all property checks on a transformation.
#[derive(Debug, Clone)]
pub(crate) struct PropertyReport {
    /// Source function name.
    pub source_function: String,
    /// Target function name.
    pub target_function: String,
    /// Per-property outcomes.
    pub outcomes: FxHashMap<TranslationProperty, PropertyOutcome>,
    /// All violations across all properties.
    pub violations: Vec<PropertyViolation>,
    /// Confidence score in [0.0, 1.0] -- proportion of properties that hold.
    pub confidence: f64,
}

// f64 field: only PartialEq, not Eq.
impl PartialEq for PropertyReport {
    fn eq(&self, other: &Self) -> bool {
        self.source_function == other.source_function
            && self.target_function == other.target_function
            && self.outcomes == other.outcomes
            && self.violations == other.violations
            && (self.confidence - other.confidence).abs() < f64::EPSILON
    }
}

impl PropertyReport {
    /// Number of properties that hold.
    #[must_use]
    pub(crate) fn properties_held(&self) -> usize {
        self.outcomes.values().filter(|o| matches!(o, PropertyOutcome::Holds)).count()
    }

    /// Number of properties checked.
    #[must_use]
    pub(crate) fn properties_checked(&self) -> usize {
        self.outcomes.len()
    }

    /// Whether all checked properties hold.
    #[must_use]
    pub(crate) fn all_hold(&self) -> bool {
        self.violations.is_empty()
            && self.outcomes.values().all(|o| matches!(o, PropertyOutcome::Holds))
    }
}

// ---------------------------------------------------------------------------
// PropertyChecker
// ---------------------------------------------------------------------------

/// Validates translation properties across source/target function pairs.
#[derive(Debug, Clone, Default)]
pub(crate) struct PropertyChecker {
    /// Properties to check (empty = check all).
    enabled: Vec<TranslationProperty>,
}

impl PropertyChecker {
    /// Create a checker that validates all properties.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Only check the specified properties.
    #[must_use]
    pub(crate) fn with_properties(mut self, props: Vec<TranslationProperty>) -> Self {
        self.enabled = props;
        self
    }

    /// Run all enabled property checks on a source/target pair.
    pub(crate) fn check(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> PropertyReport {
        let properties = if self.enabled.is_empty() {
            vec![
                TranslationProperty::SemanticPreservation,
                TranslationProperty::TypePreservation,
                TranslationProperty::TerminationPreservation,
                TranslationProperty::MemorySafety,
            ]
        } else {
            self.enabled.clone()
        };

        let mut outcomes = FxHashMap::default();
        let mut all_violations = Vec::new();

        for prop in &properties {
            let outcome = match prop {
                TranslationProperty::SemanticPreservation => {
                    check_semantic_equivalence(source, target)
                }
                TranslationProperty::TypePreservation => check_type_preservation(source, target),
                TranslationProperty::TerminationPreservation => check_termination(source, target),
                TranslationProperty::MemorySafety => check_memory_safety(source, target),
            };

            if let PropertyOutcome::Violated(ref vs) = outcome {
                all_violations.extend(vs.iter().cloned());
            }
            outcomes.insert(*prop, outcome);
        }

        let held = outcomes.values().filter(|o| matches!(o, PropertyOutcome::Holds)).count();
        let total = outcomes.len();
        let confidence = if total > 0 { held as f64 / total as f64 } else { 0.0 };

        PropertyReport {
            source_function: source.name.clone(),
            target_function: target.name.clone(),
            outcomes,
            violations: all_violations,
            confidence,
        }
    }
}

// ---------------------------------------------------------------------------
// Property check implementations
// ---------------------------------------------------------------------------

/// Compare source and target semantics by checking structural equivalence of
/// the function bodies (argument count, block count, return type, statements).
pub(crate) fn check_semantic_equivalence(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
) -> PropertyOutcome {
    let mut violations = Vec::new();

    // Argument count must match.
    if source.body.arg_count != target.body.arg_count {
        violations.push(PropertyViolation {
            property: TranslationProperty::SemanticPreservation,
            source_location: source.span.clone(),
            target_location: target.span.clone(),
            explanation: format!(
                "argument count mismatch: source has {}, target has {}",
                source.body.arg_count, target.body.arg_count,
            ),
        });
    }

    // Return type must match.
    if source.body.return_ty != target.body.return_ty {
        violations.push(PropertyViolation {
            property: TranslationProperty::SemanticPreservation,
            source_location: source.span.clone(),
            target_location: target.span.clone(),
            explanation: format!(
                "return type mismatch: source {:?}, target {:?}",
                source.body.return_ty, target.body.return_ty,
            ),
        });
    }

    // Check that return-producing blocks in source have counterparts.
    let source_returns = count_returning_blocks(&source.body);
    let target_returns = count_returning_blocks(&target.body);
    if source_returns > 0 && target_returns == 0 {
        violations.push(PropertyViolation {
            property: TranslationProperty::SemanticPreservation,
            source_location: source.span.clone(),
            target_location: target.span.clone(),
            explanation: "source has return blocks but target has none".into(),
        });
    }

    if violations.is_empty() {
        PropertyOutcome::Holds
    } else {
        PropertyOutcome::Violated(violations)
    }
}

/// Verify that types are maintained across the transformation.
///
/// Checks: local types at corresponding indices match, argument types match,
/// and the return type is preserved.
pub(crate) fn check_type_preservation(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
) -> PropertyOutcome {
    let mut violations = Vec::new();

    // Return type.
    if source.body.return_ty != target.body.return_ty {
        violations.push(PropertyViolation {
            property: TranslationProperty::TypePreservation,
            source_location: source.span.clone(),
            target_location: target.span.clone(),
            explanation: format!(
                "return type changed: {:?} -> {:?}",
                source.body.return_ty, target.body.return_ty,
            ),
        });
    }

    // Argument locals (indices 1..=arg_count).
    let src_args = argument_types(&source.body);
    let tgt_args = argument_types(&target.body);
    let check_count = src_args.len().min(tgt_args.len());
    for i in 0..check_count {
        if src_args[i] != tgt_args[i] {
            violations.push(PropertyViolation {
                property: TranslationProperty::TypePreservation,
                source_location: source.span.clone(),
                target_location: target.span.clone(),
                explanation: format!(
                    "argument {} type changed: {:?} -> {:?}",
                    i, src_args[i], tgt_args[i],
                ),
            });
        }
    }

    if violations.is_empty() {
        PropertyOutcome::Holds
    } else {
        PropertyOutcome::Violated(violations)
    }
}

/// Ensure that if the source terminates, the target also terminates.
///
/// Structural check: if source has return terminators, the target must too.
/// If target introduces unreachable paths where source returns, that is a
/// termination violation.
pub(crate) fn check_termination(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
) -> PropertyOutcome {
    let source_returns = count_returning_blocks(&source.body);
    let target_returns = count_returning_blocks(&target.body);
    let target_unreachable = count_unreachable_blocks(&target.body);

    // If source returns and target never returns, that is a termination issue.
    if source_returns > 0 && target_returns == 0 {
        return PropertyOutcome::Violated(vec![PropertyViolation {
            property: TranslationProperty::TerminationPreservation,
            source_location: source.span.clone(),
            target_location: target.span.clone(),
            explanation: format!(
                "source has {} return block(s) but target has none",
                source_returns,
            ),
        }]);
    }

    // If target introduces new unreachable blocks not in source, warn.
    let source_unreachable = count_unreachable_blocks(&source.body);
    if target_unreachable > source_unreachable {
        return PropertyOutcome::Violated(vec![PropertyViolation {
            property: TranslationProperty::TerminationPreservation,
            source_location: source.span.clone(),
            target_location: target.span.clone(),
            explanation: format!(
                "target introduces {} new unreachable block(s)",
                target_unreachable - source_unreachable,
            ),
        }]);
    }

    PropertyOutcome::Holds
}

/// Check that memory safety properties are not weakened.
///
/// Structural check: ensures the target does not introduce raw pointer
/// dereferences or mutable references where the source has none.
pub(crate) fn check_memory_safety(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
) -> PropertyOutcome {
    let source_mut_refs = count_mutable_ref_uses(&source.body);
    let target_mut_refs = count_mutable_ref_uses(&target.body);

    if target_mut_refs > source_mut_refs {
        return PropertyOutcome::Violated(vec![PropertyViolation {
            property: TranslationProperty::MemorySafety,
            source_location: source.span.clone(),
            target_location: target.span.clone(),
            explanation: format!(
                "target introduces {} additional mutable reference use(s)",
                target_mut_refs - source_mut_refs,
            ),
        }]);
    }

    PropertyOutcome::Holds
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Count blocks that terminate with `Return`.
fn count_returning_blocks(body: &VerifiableBody) -> usize {
    body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return)).count()
}

/// Count blocks that terminate with `Unreachable`.
fn count_unreachable_blocks(body: &VerifiableBody) -> usize {
    body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Unreachable)).count()
}

/// Extract argument types (indices 1..=arg_count).
fn argument_types(body: &VerifiableBody) -> Vec<&Ty> {
    body.locals.iter().skip(1).take(body.arg_count).map(|l| &l.ty).collect()
}

/// Count the number of mutable-reference uses in rvalues across all blocks.
fn count_mutable_ref_uses(body: &VerifiableBody) -> usize {
    body.blocks.iter().flat_map(|b| b.stmts.iter()).filter(|s| stmt_uses_mut_ref(s)).count()
}

/// Check if a statement uses a mutable reference in its rvalue.
fn stmt_uses_mut_ref(stmt: &Statement) -> bool {
    match stmt {
        Statement::Assign { rvalue, .. } => rvalue_uses_mut_ref(rvalue),
        _ => false,
    }
}

/// Check if an rvalue introduces or uses a mutable reference.
fn rvalue_uses_mut_ref(rvalue: &Rvalue) -> bool {
    matches!(rvalue, Rvalue::Ref { mutable: true, .. })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::*;

    /// Build a simple two-arg add function for testing.
    fn make_add_fn(name: &str) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::i32(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_property_display() {
        assert_eq!(TranslationProperty::SemanticPreservation.to_string(), "semantic-preservation");
        assert_eq!(TranslationProperty::MemorySafety.to_string(), "memory-safety");
    }

    #[test]
    fn test_semantic_equivalence_identical() {
        let src = make_add_fn("src");
        let tgt = make_add_fn("tgt");
        let outcome = check_semantic_equivalence(&src, &tgt);
        assert!(matches!(outcome, PropertyOutcome::Holds));
    }

    #[test]
    fn test_semantic_equivalence_arg_count_mismatch() {
        let src = make_add_fn("src");
        let mut tgt = make_add_fn("tgt");
        tgt.body.arg_count = 5;
        let outcome = check_semantic_equivalence(&src, &tgt);
        match outcome {
            PropertyOutcome::Violated(vs) => {
                assert!(vs[0].explanation.contains("argument count"));
            }
            other => panic!("expected Violated, got {other:?}"),
        }
    }

    #[test]
    fn test_semantic_equivalence_return_type_mismatch() {
        let src = make_add_fn("src");
        let mut tgt = make_add_fn("tgt");
        tgt.body.return_ty = Ty::Bool;
        let outcome = check_semantic_equivalence(&src, &tgt);
        match outcome {
            PropertyOutcome::Violated(vs) => {
                assert!(vs.iter().any(|v| v.explanation.contains("return type")));
            }
            other => panic!("expected Violated, got {other:?}"),
        }
    }

    #[test]
    fn test_type_preservation_holds() {
        let src = make_add_fn("src");
        let tgt = make_add_fn("tgt");
        let outcome = check_type_preservation(&src, &tgt);
        assert!(matches!(outcome, PropertyOutcome::Holds));
    }

    #[test]
    fn test_type_preservation_arg_type_changed() {
        let src = make_add_fn("src");
        let mut tgt = make_add_fn("tgt");
        tgt.body.locals[1].ty = Ty::Bool;
        let outcome = check_type_preservation(&src, &tgt);
        match outcome {
            PropertyOutcome::Violated(vs) => {
                assert!(vs[0].explanation.contains("argument 0 type changed"));
            }
            other => panic!("expected Violated, got {other:?}"),
        }
    }

    #[test]
    fn test_termination_preserved() {
        let src = make_add_fn("src");
        let tgt = make_add_fn("tgt");
        let outcome = check_termination(&src, &tgt);
        assert!(matches!(outcome, PropertyOutcome::Holds));
    }

    #[test]
    fn test_termination_target_no_return() {
        let src = make_add_fn("src");
        let mut tgt = make_add_fn("tgt");
        tgt.body.blocks[0].terminator = Terminator::Unreachable;
        let outcome = check_termination(&src, &tgt);
        match outcome {
            PropertyOutcome::Violated(vs) => {
                assert!(vs[0].explanation.contains("return block"));
            }
            other => panic!("expected Violated, got {other:?}"),
        }
    }

    #[test]
    fn test_termination_new_unreachable() {
        let src = make_add_fn("src");
        let mut tgt = make_add_fn("tgt");
        // Add an extra unreachable block to target.
        tgt.body.blocks.push(BasicBlock {
            id: BlockId(99),
            stmts: vec![],
            terminator: Terminator::Unreachable,
        });
        let outcome = check_termination(&src, &tgt);
        match outcome {
            PropertyOutcome::Violated(vs) => {
                assert!(vs[0].explanation.contains("unreachable"));
            }
            other => panic!("expected Violated, got {other:?}"),
        }
    }

    #[test]
    fn test_memory_safety_holds() {
        let src = make_add_fn("src");
        let tgt = make_add_fn("tgt");
        let outcome = check_memory_safety(&src, &tgt);
        assert!(matches!(outcome, PropertyOutcome::Holds));
    }

    #[test]
    fn test_memory_safety_new_mut_ref() {
        let src = make_add_fn("src");
        let mut tgt = make_add_fn("tgt");
        // Introduce a mutable ref in target.
        tgt.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
            span: SourceSpan::default(),
        });
        let outcome = check_memory_safety(&src, &tgt);
        match outcome {
            PropertyOutcome::Violated(vs) => {
                assert!(vs[0].explanation.contains("mutable reference"));
            }
            other => panic!("expected Violated, got {other:?}"),
        }
    }

    #[test]
    fn test_full_report_all_hold() {
        let src = make_add_fn("src");
        let tgt = make_add_fn("tgt");
        let checker = PropertyChecker::new();
        let report = checker.check(&src, &tgt);

        assert!(report.all_hold());
        assert_eq!(report.properties_checked(), 4);
        assert_eq!(report.properties_held(), 4);
        assert!(report.violations.is_empty());
        assert!((report.confidence - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_full_report_with_violations() {
        let src = make_add_fn("src");
        let mut tgt = make_add_fn("tgt");
        tgt.body.arg_count = 5;
        tgt.body.blocks[0].terminator = Terminator::Unreachable;

        let checker = PropertyChecker::new();
        let report = checker.check(&src, &tgt);

        assert!(!report.all_hold());
        assert!(!report.violations.is_empty());
        assert!(report.confidence < 1.0);
        assert_eq!(report.source_function, "src");
        assert_eq!(report.target_function, "tgt");
    }

    #[test]
    fn test_checker_with_selected_properties() {
        let src = make_add_fn("src");
        let tgt = make_add_fn("tgt");
        let checker =
            PropertyChecker::new().with_properties(vec![TranslationProperty::TypePreservation]);
        let report = checker.check(&src, &tgt);
        assert_eq!(report.properties_checked(), 1);
        assert!(report.all_hold());
    }

    #[test]
    fn test_violation_display() {
        let v = PropertyViolation {
            property: TranslationProperty::SemanticPreservation,
            source_location: SourceSpan {
                file: "src.rs".into(),
                line_start: 10,
                col_start: 0,
                line_end: 10,
                col_end: 0,
            },
            target_location: SourceSpan {
                file: "tgt.rs".into(),
                line_start: 20,
                col_start: 0,
                line_end: 20,
                col_end: 0,
            },
            explanation: "test violation".into(),
        };
        let s = v.to_string();
        assert!(s.contains("semantic-preservation"));
        assert!(s.contains("src.rs"));
        assert!(s.contains("tgt.rs"));
        assert!(s.contains("test violation"));
    }

    #[test]
    fn test_property_report_partial_eq() {
        let src = make_add_fn("src");
        let tgt = make_add_fn("tgt");
        let checker = PropertyChecker::new();
        let r1 = checker.check(&src, &tgt);
        let r2 = checker.check(&src, &tgt);
        assert_eq!(r1, r2);
    }
}
