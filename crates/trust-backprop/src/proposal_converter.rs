//! Convert `trust-strengthen::Proposal` into `SourceRewrite` with actual byte offsets.
//!
//! The key challenge: `Proposal` has `function_name` but no byte offset.
//! This module reads the source file, locates the function, and produces
//! `SourceRewrite` values with real offsets that `RewriteEngine` can apply.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::locator::{find_function_first, FunctionLocation};
use crate::rewriter::RewriteError;
use crate::{RewriteKind, SourceRewrite};
use trust_strengthen::{Proposal, ProposalKind};

/// Errors specific to proposal conversion.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ConvertError {
    /// The function named in the proposal was not found in the source.
    #[error("function `{name}` not found in `{file_path}`")]
    FunctionNotFound { name: String, file_path: String },
    /// The expression to replace was not found in the function body.
    #[error("expression `{expr}` not found in function `{name}` in `{file_path}`")]
    ExpressionNotFound {
        expr: String,
        name: String,
        file_path: String,
    },
}

impl From<ConvertError> for RewriteError {
    fn from(e: ConvertError) -> Self {
        match e {
            ConvertError::FunctionNotFound { name, file_path } => RewriteError::SourceMismatch {
                file_path,
                offset: 0,
                expected: format!("fn {name}("),
            },
            ConvertError::ExpressionNotFound {
                expr,
                name: _,
                file_path,
            } => RewriteError::SourceMismatch {
                file_path,
                offset: 0,
                expected: expr,
            },
        }
    }
}

/// Convert a `Proposal` into `SourceRewrite` values with real byte offsets,
/// by locating the function in the provided source text.
///
/// # Arguments
///
/// * `proposal` - The proposal from trust-strengthen.
/// * `source` - The source text of the file referenced by `proposal.function_path`.
/// * `file_path` - The actual filesystem path to the source file (used in `SourceRewrite`).
///
/// # Errors
///
/// Returns `ConvertError::FunctionNotFound` if the function cannot be located.
/// Returns `ConvertError::ExpressionNotFound` for `SafeArithmetic` if the old expression
/// is not found within the function body.
pub fn convert_proposal(
    proposal: &Proposal,
    source: &str,
    file_path: &str,
) -> Result<Vec<SourceRewrite>, ConvertError> {
    let loc = find_function_first(source, &proposal.function_name).ok_or_else(|| {
        ConvertError::FunctionNotFound {
            name: proposal.function_name.clone(),
            file_path: file_path.to_owned(),
        }
    })?;

    match &proposal.kind {
        ProposalKind::AddPrecondition { spec_body } => {
            Ok(vec![make_attribute_rewrite(
                file_path,
                &loc,
                &proposal.function_name,
                &format!("#[requires(\"{spec_body}\")]"),
                &proposal.rationale,
            )])
        }
        ProposalKind::AddPostcondition { spec_body } => {
            Ok(vec![make_attribute_rewrite(
                file_path,
                &loc,
                &proposal.function_name,
                &format!("#[ensures(\"{spec_body}\")]"),
                &proposal.rationale,
            )])
        }
        ProposalKind::AddInvariant { spec_body } => {
            Ok(vec![make_attribute_rewrite(
                file_path,
                &loc,
                &proposal.function_name,
                &format!("#[invariant(\"{spec_body}\")]"),
                &proposal.rationale,
            )])
        }
        ProposalKind::SafeArithmetic {
            original,
            replacement,
        } => {
            let expr_offset = find_expr_in_function(source, &loc, original).ok_or_else(|| {
                ConvertError::ExpressionNotFound {
                    expr: original.clone(),
                    name: proposal.function_name.clone(),
                    file_path: file_path.to_owned(),
                }
            })?;
            Ok(vec![SourceRewrite {
                file_path: file_path.to_owned(),
                offset: expr_offset,
                kind: RewriteKind::ReplaceExpression {
                    old_text: original.clone(),
                    new_text: replacement.clone(),
                },
                function_name: proposal.function_name.clone(),
                rationale: proposal.rationale.clone(),
            }])
        }
        ProposalKind::AddBoundsCheck { check_expr } => {
            Ok(vec![make_assertion_rewrite(
                file_path,
                source,
                &loc,
                &proposal.function_name,
                check_expr,
                &proposal.rationale,
            )])
        }
        ProposalKind::AddNonZeroCheck { check_expr } => {
            Ok(vec![make_assertion_rewrite(
                file_path,
                source,
                &loc,
                &proposal.function_name,
                check_expr,
                &proposal.rationale,
            )])
        }
    }
}

/// Create an attribute insertion rewrite at the item's start offset.
fn make_attribute_rewrite(
    file_path: &str,
    loc: &FunctionLocation,
    function_name: &str,
    attribute: &str,
    rationale: &str,
) -> SourceRewrite {
    // Format attribute with the same indentation as the function
    let formatted = if loc.indent.is_empty() {
        attribute.to_owned()
    } else {
        format!("{}{attribute}", loc.indent)
    };

    SourceRewrite {
        file_path: file_path.to_owned(),
        offset: loc.item_offset,
        kind: RewriteKind::InsertAttribute {
            attribute: formatted,
        },
        function_name: function_name.to_owned(),
        rationale: rationale.to_owned(),
    }
}

/// Create an assertion insertion rewrite at the start of the function body.
fn make_assertion_rewrite(
    file_path: &str,
    source: &str,
    loc: &FunctionLocation,
    function_name: &str,
    assertion: &str,
    rationale: &str,
) -> SourceRewrite {
    // Find the opening brace `{` after the function signature
    let body_start = source[loc.fn_offset..]
        .find('{')
        .map(|i| loc.fn_offset + i + 1) // +1 to get past the `{`
        .unwrap_or(loc.fn_offset);

    // Skip any newline right after `{`
    let insert_at = if source[body_start..].starts_with('\n') {
        body_start + 1
    } else {
        body_start
    };

    SourceRewrite {
        file_path: file_path.to_owned(),
        offset: insert_at,
        kind: RewriteKind::InsertAssertion {
            assertion: assertion.to_owned(),
        },
        function_name: function_name.to_owned(),
        rationale: rationale.to_owned(),
    }
}

/// Find an expression within the function body, returning its byte offset in the full source.
fn find_expr_in_function(
    source: &str,
    loc: &FunctionLocation,
    expr: &str,
) -> Option<usize> {
    // Search from the fn keyword onward for the expression
    let search_start = loc.fn_offset;
    source[search_start..]
        .find(expr)
        .map(|i| search_start + i)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_strengthen::{Proposal, ProposalKind};

    fn make_source() -> &'static str {
        "pub fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n"
    }

    fn make_proposal(kind: ProposalKind) -> Proposal {
        Proposal {
            function_path: "crate::get_midpoint".into(),
            function_name: "get_midpoint".into(),
            kind,
            confidence: 0.9,
            rationale: "overflow protection".into(),
        }
    }

    #[test]
    fn test_convert_precondition() {
        let source = make_source();
        let proposal = make_proposal(ProposalKind::AddPrecondition {
            spec_body: "a + b < u64::MAX".into(),
        });
        let rewrites = convert_proposal(&proposal, source, "src/lib.rs").unwrap();
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].offset, 0); // item starts at 0
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertAttribute { attribute } if attribute.contains("requires")
        ));
    }

    #[test]
    fn test_convert_postcondition() {
        let source = make_source();
        let proposal = make_proposal(ProposalKind::AddPostcondition {
            spec_body: "result <= a && result <= b".into(),
        });
        let rewrites = convert_proposal(&proposal, source, "src/lib.rs").unwrap();
        assert_eq!(rewrites.len(), 1);
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertAttribute { attribute } if attribute.contains("ensures")
        ));
    }

    #[test]
    fn test_convert_safe_arithmetic() {
        let source = make_source();
        let proposal = make_proposal(ProposalKind::SafeArithmetic {
            original: "a + b".into(),
            replacement: "a.checked_add(b).expect(\"overflow\")".into(),
        });
        let rewrites = convert_proposal(&proposal, source, "src/lib.rs").unwrap();
        assert_eq!(rewrites.len(), 1);
        // The offset should point to where "a + b" appears in the function body
        let offset = rewrites[0].offset;
        assert_eq!(&source[offset..offset + 5], "a + b");
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::ReplaceExpression { old_text, new_text }
                if old_text == "a + b" && new_text.contains("checked_add")
        ));
    }

    #[test]
    fn test_convert_bounds_check() {
        let source = "fn index_into(v: &[u8], i: usize) -> u8 {\n    v[i]\n}\n";
        let proposal = Proposal {
            function_path: "crate::index_into".into(),
            function_name: "index_into".into(),
            kind: ProposalKind::AddBoundsCheck {
                check_expr: "assert!(i < v.len());".into(),
            },
            confidence: 0.85,
            rationale: "bounds check".into(),
        };
        let rewrites = convert_proposal(&proposal, source, "src/lib.rs").unwrap();
        assert_eq!(rewrites.len(), 1);
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertAssertion { assertion } if assertion.contains("assert!")
        ));
    }

    #[test]
    fn test_convert_non_zero_check() {
        let source = "fn divide(a: u64, b: u64) -> u64 {\n    a / b\n}\n";
        let proposal = Proposal {
            function_path: "crate::divide".into(),
            function_name: "divide".into(),
            kind: ProposalKind::AddNonZeroCheck {
                check_expr: "assert!(b != 0, \"division by zero\");".into(),
            },
            confidence: 0.95,
            rationale: "prevent division by zero".into(),
        };
        let rewrites = convert_proposal(&proposal, source, "src/lib.rs").unwrap();
        assert_eq!(rewrites.len(), 1);
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertAssertion { assertion } if assertion.contains("!= 0")
        ));
    }

    #[test]
    fn test_convert_function_not_found() {
        let source = "fn foo() {}\n";
        let proposal = make_proposal(ProposalKind::AddPrecondition {
            spec_body: "true".into(),
        });
        let result = convert_proposal(&proposal, source, "src/lib.rs");
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            ConvertError::FunctionNotFound { .. }
        ));
    }

    #[test]
    fn test_convert_expression_not_found() {
        let source = "fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n";
        let proposal = make_proposal(ProposalKind::SafeArithmetic {
            original: "x * y".into(),
            replacement: "x.checked_mul(y).unwrap()".into(),
        });
        let result = convert_proposal(&proposal, source, "src/lib.rs");
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            ConvertError::ExpressionNotFound { .. }
        ));
    }

    #[test]
    fn test_convert_indented_function() {
        let source = "impl Calculator {\n    pub fn add(&self, a: u64, b: u64) -> u64 {\n        a + b\n    }\n}\n";
        let proposal = Proposal {
            function_path: "crate::Calculator::add".into(),
            function_name: "add".into(),
            kind: ProposalKind::AddPrecondition {
                spec_body: "a + b < u64::MAX".into(),
            },
            confidence: 0.9,
            rationale: "overflow".into(),
        };
        let rewrites = convert_proposal(&proposal, source, "src/lib.rs").unwrap();
        assert_eq!(rewrites.len(), 1);
        // The attribute should have the same indentation as the function
        if let RewriteKind::InsertAttribute { attribute } = &rewrites[0].kind {
            assert!(attribute.starts_with("    "), "attribute should be indented: {attribute:?}");
        } else {
            panic!("expected InsertAttribute");
        }
    }

    #[test]
    fn test_convert_error_into_rewrite_error() {
        let err = ConvertError::FunctionNotFound {
            name: "foo".into(),
            file_path: "bar.rs".into(),
        };
        let rewrite_err: RewriteError = err.into();
        assert!(matches!(rewrite_err, RewriteError::SourceMismatch { .. }));
    }

    #[test]
    fn test_convert_invariant() {
        let source = make_source();
        let proposal = make_proposal(ProposalKind::AddInvariant {
            spec_body: "i < n".into(),
        });
        let rewrites = convert_proposal(&proposal, source, "src/lib.rs").unwrap();
        assert_eq!(rewrites.len(), 1);
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertAttribute { attribute } if attribute.contains("invariant")
        ));
    }
}
