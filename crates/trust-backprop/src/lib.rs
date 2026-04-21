#![allow(dead_code)]
//! trust-backprop: Source rewriting engine for the prove-strengthen-backprop loop.
//!
//! Takes proposals from trust-strengthen and applies them to source code:
//! inserting spec attributes (`#[requires]`, `#[ensures]`), replacing unsafe
//! arithmetic with checked variants, and adding runtime assertions.
//! Part of Idea 3 from VISION.md.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod approval;
pub(crate) mod ast_rewriter;
pub(crate) mod ast_validation;
pub(crate) mod audit_trail;
pub(crate) mod caller_propagation;
pub(crate) mod cross_module;
pub(crate) mod dependency;
pub(crate) mod diff_gen;
pub mod file_io;
mod governance;
pub(crate) mod locator;
pub(crate) mod proposal_converter;
mod rewriter;
pub(crate) mod rollback;
pub(crate) mod substitution;
pub(crate) mod type_guided;
pub(crate) mod validation;

pub use caller_propagation::{
    build_types_call_graph, CallerPropagator, FunctionVisibility, PropagationAction,
    PropagationConfig, PropagationError, PropagationResult, PropagationSuggestion, Provenance,
};
pub use cross_module::{plan_cross_module_rewrites, CrossModulePlan};
pub use dependency::{build_call_graph, topological_order, CallGraph};
pub use substitution::{
    free_variables, simplify, substitute, substitute_with_depth, rename_variable,
    SubstitutionError, SubstitutionMap,
};
pub use file_io::{
    apply_plan_to_files, apply_plan_to_source, proposals_to_plan, read_source, write_source,
    FileRewriteError, FileRewriteResult,
};
pub use approval::{
    classify_rewrite, default_rules, ApprovalPolicy, ApprovalQueue, PendingRewrite, PolicyRule,
    RewriteKindFilter,
};
pub use governance::{
    check_cross_module_invariants, GovernancePolicy, GovernanceViolation, RewriteTracker,
};
pub use locator::{find_function, find_function_first, FunctionLocation};
pub use proposal_converter::{convert_proposal, ConvertError};
pub use rewriter::{RewriteEngine, RewriteError};
pub use rollback::{
    changed_since_checkpoint, create_checkpoint, rollback, sha256_hex, CheckpointStore,
    FileSnapshot, RewriteCheckpoint, RollbackError,
};
pub use audit_trail::{
    AuditAction, AuditEntry, AuditEntryBuilder, AuditSummary, AuditTrail, ApprovalStatus,
    ReverificationResult,
};
pub use validation::{
    check_semantic_preservation, parse_simplified_ast, validate_rewrite,
    validate_rewrite_with_config, AstNode, CheckResult, SemanticDiff, ValidationCheck,
    ValidationConfig, ValidationResult,
};
pub use ast_rewriter::{
    compute_indentation, detect_indent_unit, resolve_target, AstRewriteError, AstRewriteTarget,
    SemanticRewrite,
};
pub use ast_validation::{
    validate_rewrite_ast, AstValidationError, AstValidationResult, ParseTarget,
};
pub use type_guided::{
    generate_ensures_from_types, generate_requires_from_types, infer_bounds_from_type,
    infer_lifetime_constraints, infer_nullability, match_patterns, FormulaHint, SignatureHints,
    TypeAnalyzer, TypePattern,
};
pub use diff_gen::{
    apply_diff, format_colored, format_github, format_unified, generate_diff, merge_diffs,
    reverse_diff, DiffApplyError, DiffGenerator, DiffHunk, UnifiedDiff,
};

use serde::{Deserialize, Serialize};
use trust_strengthen::{Proposal, ProposalKind};

/// A plan describing a set of source rewrites to apply.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RewritePlan {
    /// Individual rewrites in this plan, ordered by file then descending offset.
    pub rewrites: Vec<SourceRewrite>,
    /// Summary of what this plan does.
    pub summary: String,
}

impl RewritePlan {
    /// Create a new empty rewrite plan.
    #[must_use]
    pub fn new(summary: impl Into<String>) -> Self {
        Self {
            rewrites: Vec::new(),
            summary: summary.into(),
        }
    }

    /// Number of rewrites in this plan.
    #[must_use]
    pub fn len(&self) -> usize {
        self.rewrites.len()
    }

    /// Whether the plan is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.rewrites.is_empty()
    }

    /// Sort rewrites so they can be applied bottom-up (descending offset)
    /// within each file, preventing offset invalidation.
    pub fn sort_for_application(&mut self) {
        self.rewrites.sort_by(|a, b| {
            a.file_path
                .cmp(&b.file_path)
                .then(b.offset.cmp(&a.offset))
        });
    }
}

/// A single source-level rewrite operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceRewrite {
    /// Path to the source file to modify.
    pub file_path: String,
    /// Byte offset in the file where the rewrite applies.
    pub offset: usize,
    /// What kind of rewrite to perform.
    pub kind: RewriteKind,
    /// The function this rewrite targets.
    pub function_name: String,
    /// Human-readable rationale for this rewrite.
    pub rationale: String,
}

/// The kind of source-level rewrite.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RewriteKind {
    /// Insert an attribute before a function: `#[requires("...")]` or `#[ensures("...")]`.
    InsertAttribute { attribute: String },
    /// Replace an expression with a new one (e.g., `a + b` -> `a.checked_add(b).unwrap()`).
    ReplaceExpression {
        old_text: String,
        new_text: String,
    },
    /// Insert an assertion before a statement.
    InsertAssertion { assertion: String },
}

/// Convert a list of proposals from trust-strengthen into a rewrite plan.
///
/// This is the main entry point for trust-backprop. It:
/// 1. Checks each proposal against governance rules
/// 2. Converts accepted proposals into source rewrites
/// 3. Returns a plan that can be applied to the source tree
///
/// # Errors
///
/// Returns `RewriteError::Governance` if a proposal violates governance rules
/// and `strict` mode is enabled in the policy.
pub fn apply_plan(
    proposals: &[Proposal],
    policy: &GovernancePolicy,
) -> Result<RewritePlan, RewriteError> {
    let mut plan = RewritePlan::new(format!(
        "Backprop plan: {} proposals",
        proposals.len()
    ));

    for proposal in proposals {
        // Check governance rules
        let violations = policy.check(proposal);
        if !violations.is_empty() {
            if policy.strict {
                return Err(RewriteError::Governance {
                    function: proposal.function_name.clone(),
                    violations,
                });
            }
            // In non-strict mode, skip proposals that violate governance
            continue;
        }

        // Convert proposal to source rewrites
        let rewrites = proposal_to_rewrites(proposal);
        plan.rewrites.extend(rewrites);
    }

    plan.sort_for_application();
    Ok(plan)
}

/// Convert a single proposal into zero or more source rewrites.
///
/// Computes the byte offset from the proposal's `function_path` (source file) by
/// reading the file and locating the function with `locator::find_function_first`.
/// Falls back to offset 0 when the file cannot be read or the function is not found
/// (e.g., in tests where `function_path` is a module path like `"test::f"`).
fn proposal_to_rewrites(proposal: &Proposal) -> Vec<SourceRewrite> {
    // Try to read the source file and locate the function to compute real offsets.
    let loc = std::fs::read_to_string(&proposal.function_path)
        .ok()
        .and_then(|source| locator::find_function_first(&source, &proposal.function_name));

    let item_offset = loc.as_ref().map_or(0, |l| l.item_offset);
    let fn_offset = loc.as_ref().map_or(0, |l| l.fn_offset);

    match &proposal.kind {
        ProposalKind::AddPrecondition { spec_body } => {
            vec![SourceRewrite {
                file_path: proposal.function_path.clone(),
                offset: item_offset,
                kind: RewriteKind::InsertAttribute {
                    attribute: format!("#[requires(\"{spec_body}\")]"),
                },
                function_name: proposal.function_name.clone(),
                rationale: proposal.rationale.clone(),
            }]
        }
        ProposalKind::AddPostcondition { spec_body } => {
            vec![SourceRewrite {
                file_path: proposal.function_path.clone(),
                offset: item_offset,
                kind: RewriteKind::InsertAttribute {
                    attribute: format!("#[ensures(\"{spec_body}\")]"),
                },
                function_name: proposal.function_name.clone(),
                rationale: proposal.rationale.clone(),
            }]
        }
        ProposalKind::AddInvariant { spec_body } => {
            vec![SourceRewrite {
                file_path: proposal.function_path.clone(),
                offset: item_offset,
                kind: RewriteKind::InsertAttribute {
                    attribute: format!("#[invariant(\"{spec_body}\")]"),
                },
                function_name: proposal.function_name.clone(),
                rationale: proposal.rationale.clone(),
            }]
        }
        ProposalKind::SafeArithmetic {
            original,
            replacement,
        } => {
            // For expression replacement, search for the expression after the fn keyword
            let expr_offset = std::fs::read_to_string(&proposal.function_path)
                .ok()
                .and_then(|source| {
                    source[fn_offset..].find(original.as_str()).map(|i| fn_offset + i)
                })
                .unwrap_or(fn_offset);
            vec![SourceRewrite {
                file_path: proposal.function_path.clone(),
                offset: expr_offset,
                kind: RewriteKind::ReplaceExpression {
                    old_text: original.clone(),
                    new_text: replacement.clone(),
                },
                function_name: proposal.function_name.clone(),
                rationale: proposal.rationale.clone(),
            }]
        }
        ProposalKind::AddBoundsCheck { check_expr } => {
            vec![SourceRewrite {
                file_path: proposal.function_path.clone(),
                offset: fn_offset,
                kind: RewriteKind::InsertAssertion {
                    assertion: check_expr.clone(),
                },
                function_name: proposal.function_name.clone(),
                rationale: proposal.rationale.clone(),
            }]
        }
        ProposalKind::AddNonZeroCheck { check_expr } => {
            vec![SourceRewrite {
                file_path: proposal.function_path.clone(),
                offset: fn_offset,
                kind: RewriteKind::InsertAssertion {
                    assertion: check_expr.clone(),
                },
                function_name: proposal.function_name.clone(),
                rationale: proposal.rationale.clone(),
            }]
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_strengthen::{Proposal, ProposalKind};

    fn make_precondition_proposal(func: &str, spec: &str) -> Proposal {
        Proposal {
            function_path: format!("test::{func}"),
            function_name: func.into(),
            kind: ProposalKind::AddPrecondition {
                spec_body: spec.into(),
            },
            confidence: 0.9,
            rationale: "test proposal".into(),
        }
    }

    fn make_safe_arithmetic_proposal(func: &str) -> Proposal {
        Proposal {
            function_path: format!("test::{func}"),
            function_name: func.into(),
            kind: ProposalKind::SafeArithmetic {
                original: "a + b".into(),
                replacement: "a.checked_add(b).unwrap()".into(),
            },
            confidence: 0.8,
            rationale: "Replace raw addition with checked_add".into(),
        }
    }

    #[test]
    fn test_apply_plan_empty_proposals() {
        let policy = GovernancePolicy::default();
        let plan = apply_plan(&[], &policy).expect("should succeed with empty proposals");
        assert!(plan.is_empty());
        assert_eq!(plan.len(), 0);
    }

    #[test]
    fn test_apply_plan_single_precondition() {
        let policy = GovernancePolicy::default();
        let proposals = vec![make_precondition_proposal("get_midpoint", "a + b < u64::MAX")];
        let plan = apply_plan(&proposals, &policy).expect("should succeed");
        assert_eq!(plan.len(), 1);
        assert!(matches!(
            &plan.rewrites[0].kind,
            RewriteKind::InsertAttribute { attribute } if attribute.contains("requires")
        ));
    }

    #[test]
    fn test_apply_plan_safe_arithmetic() {
        let policy = GovernancePolicy::default();
        let proposals = vec![make_safe_arithmetic_proposal("get_midpoint")];
        let plan = apply_plan(&proposals, &policy).expect("should succeed");
        assert_eq!(plan.len(), 1);
        assert!(matches!(
            &plan.rewrites[0].kind,
            RewriteKind::ReplaceExpression { old_text, new_text }
                if old_text == "a + b" && new_text.contains("checked_add")
        ));
    }

    #[test]
    fn test_apply_plan_governance_blocks_pub_fn_strict() {
        let policy = GovernancePolicy {
            immutable_pub_signatures: true,
            immutable_tests: true,
            strict: true,
            protected_functions: vec!["get_midpoint".into()],
            allow_spec_only_on_protected: false,
            ..Default::default()
        };
        let proposals = vec![make_precondition_proposal("get_midpoint", "x > 0")];
        let result = apply_plan(&proposals, &policy);
        assert!(result.is_err());
    }

    #[test]
    fn test_apply_plan_governance_skips_in_nonstrict() {
        let policy = GovernancePolicy {
            immutable_pub_signatures: true,
            immutable_tests: true,
            strict: false,
            protected_functions: vec!["get_midpoint".into()],
            allow_spec_only_on_protected: false,
            ..Default::default()
        };
        let proposals = vec![make_precondition_proposal("get_midpoint", "x > 0")];
        let plan = apply_plan(&proposals, &policy).expect("should succeed in non-strict");
        assert!(plan.is_empty());
    }

    #[test]
    fn test_apply_plan_multiple_proposals() {
        let policy = GovernancePolicy::default();
        let proposals = vec![
            make_precondition_proposal("fn_a", "x > 0"),
            make_safe_arithmetic_proposal("fn_b"),
            Proposal {
                function_path: "test::fn_c".into(),
                function_name: "fn_c".into(),
                kind: ProposalKind::AddBoundsCheck {
                    check_expr: "assert!(i < v.len())".into(),
                },
                confidence: 0.8,
                rationale: "bounds check".into(),
            },
        ];
        let plan = apply_plan(&proposals, &policy).expect("should succeed");
        assert_eq!(plan.len(), 3);
    }

    #[test]
    fn test_rewrite_plan_sort_descending_offset() {
        let mut plan = RewritePlan::new("test");
        plan.rewrites = vec![
            SourceRewrite {
                file_path: "a.rs".into(),
                offset: 10,
                kind: RewriteKind::InsertAssertion {
                    assertion: "first".into(),
                },
                function_name: "f".into(),
                rationale: String::new(),
            },
            SourceRewrite {
                file_path: "a.rs".into(),
                offset: 50,
                kind: RewriteKind::InsertAssertion {
                    assertion: "second".into(),
                },
                function_name: "f".into(),
                rationale: String::new(),
            },
            SourceRewrite {
                file_path: "a.rs".into(),
                offset: 30,
                kind: RewriteKind::InsertAssertion {
                    assertion: "third".into(),
                },
                function_name: "f".into(),
                rationale: String::new(),
            },
        ];
        plan.sort_for_application();

        // Should be sorted descending by offset within same file
        assert_eq!(plan.rewrites[0].offset, 50);
        assert_eq!(plan.rewrites[1].offset, 30);
        assert_eq!(plan.rewrites[2].offset, 10);
    }

    #[test]
    fn test_proposal_to_rewrites_postcondition() {
        let proposal = Proposal {
            function_path: "test::f".into(),
            function_name: "f".into(),
            kind: ProposalKind::AddPostcondition {
                spec_body: "result >= 0".into(),
            },
            confidence: 0.7,
            rationale: "test".into(),
        };
        let rewrites = proposal_to_rewrites(&proposal);
        assert_eq!(rewrites.len(), 1);
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertAttribute { attribute } if attribute.contains("ensures")
        ));
    }

    #[test]
    fn test_proposal_to_rewrites_invariant() {
        let proposal = Proposal {
            function_path: "test::f".into(),
            function_name: "f".into(),
            kind: ProposalKind::AddInvariant {
                spec_body: "i < n".into(),
            },
            confidence: 0.6,
            rationale: "test".into(),
        };
        let rewrites = proposal_to_rewrites(&proposal);
        assert_eq!(rewrites.len(), 1);
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertAttribute { attribute } if attribute.contains("invariant")
        ));
    }

    #[test]
    fn test_proposal_to_rewrites_non_zero_check() {
        let proposal = Proposal {
            function_path: "test::f".into(),
            function_name: "f".into(),
            kind: ProposalKind::AddNonZeroCheck {
                check_expr: "assert!(d != 0)".into(),
            },
            confidence: 0.8,
            rationale: "test".into(),
        };
        let rewrites = proposal_to_rewrites(&proposal);
        assert_eq!(rewrites.len(), 1);
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertAssertion { assertion } if assertion.contains("!= 0")
        ));
    }
}
