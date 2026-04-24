// trust-vcgen/spec_parser.rs: Generate VCs from FunctionSpec attributes
//
// Bridges the FunctionSpec (string-based #[requires], #[ensures], #[invariant]
// attributes) on VerifiableFunction to verification conditions. Uses the
// spec expression parser in trust-types to convert spec strings to Formulas.
//
// This complements contracts.rs which processes the Vec<Contract> field.
// spec_parser.rs processes the FunctionSpec field, which is populated by
// trust-mir-extract from parsed #[requires("...")] / #[ensures("...")] attributes.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    Formula, FunctionSpec, VcKind, VerifiableFunction, VerificationCondition, parse_spec_expr,
};

/// Generate verification conditions from a function's `FunctionSpec` field.
///
/// For each parseable spec clause:
/// - `requires` clauses become `Precondition` VCs
/// - `ensures` clauses become `Postcondition` VCs
/// - `invariant` clauses become `Assertion` VCs
///
/// Each VC's formula is the *negation* of the spec formula (we check for
/// violations: if UNSAT, the spec holds; if SAT, the model is a counterexample).
///
/// Unparseable spec strings are silently skipped (the parser returns None).
#[cfg_attr(feature = "pipeline-v2", allow(dead_code))]
pub(crate) fn generate_spec_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let spec = &func.spec;
    if spec.is_empty() {
        return Vec::new();
    }

    let contract_metadata = Some(spec.to_contract_metadata());
    let mut vcs = Vec::new();

    // Preconditions: #[requires("...")]
    for expr in &spec.requires {
        if let Some(formula) = parse_spec_expr(expr) {
            vcs.push(VerificationCondition {
                kind: VcKind::Precondition { callee: func.name.clone() },
                function: func.name.as_str().into(),
                location: func.span.clone(),
                formula: Formula::Not(Box::new(formula)),
                contract_metadata,
            });
        }
    }

    // Postconditions: #[ensures("...")]
    for expr in &spec.ensures {
        if let Some(formula) = parse_spec_expr(expr) {
            vcs.push(VerificationCondition {
                kind: VcKind::Postcondition,
                function: func.name.as_str().into(),
                location: func.span.clone(),
                formula: Formula::Not(Box::new(formula)),
                contract_metadata,
            });
        }
    }

    // Invariants: #[invariant("...")]
    for expr in &spec.invariants {
        if let Some(formula) = parse_spec_expr(expr) {
            vcs.push(VerificationCondition {
                kind: VcKind::Assertion { message: format!("invariant: {expr}") },
                function: func.name.as_str().into(),
                location: func.span.clone(),
                formula: Formula::Not(Box::new(formula)),
                contract_metadata,
            });
        }
    }

    vcs
}

/// Check if a FunctionSpec would produce any VCs (without actually generating them).
///
/// Useful for pre-filtering functions before full VC generation.
#[must_use]
pub fn has_spec_vcs(spec: &FunctionSpec) -> bool {
    if spec.is_empty() {
        return false;
    }
    // Check if at least one clause is parseable
    spec.requires.iter().any(|e| parse_spec_expr(e).is_some())
        || spec.ensures.iter().any(|e| parse_spec_expr(e).is_some())
        || spec.invariants.iter().any(|e| parse_spec_expr(e).is_some())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{
        BasicBlock, BlockId, Formula, LocalDecl, Sort, SourceSpan, Terminator, Ty, VerifiableBody,
    };

    fn spec_test_function(spec: FunctionSpec) -> VerifiableFunction {
        VerifiableFunction {
            name: "spec_fn".to_string(),
            def_path: "test::spec_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("y".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec,
        }
    }

    #[test]
    fn test_empty_spec_produces_no_vcs() {
        let func = spec_test_function(FunctionSpec::default());
        let vcs = generate_spec_vcs(&func);
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_requires_generates_precondition_vc() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec![],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(&vcs[0].kind, VcKind::Precondition { callee } if callee == "spec_fn"));
        assert_eq!(
            vcs[0].formula,
            Formula::Not(Box::new(Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
        );
    }

    #[test]
    fn test_ensures_generates_postcondition_vc() {
        let spec = FunctionSpec {
            requires: vec![],
            ensures: vec!["result >= 0".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::Postcondition));
        // "result" maps to "_0" in the spec parser
        assert_eq!(
            vcs[0].formula,
            Formula::Not(Box::new(Formula::Ge(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
        );
    }

    #[test]
    fn test_invariant_generates_assertion_vc() {
        let spec = FunctionSpec {
            requires: vec![],
            ensures: vec![],
            invariants: vec!["n > 0".to_string()],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(
            matches!(&vcs[0].kind, VcKind::Assertion { message } if message == "invariant: n > 0")
        );
    }

    #[test]
    fn test_multiple_specs_generate_multiple_vcs() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string(), "y > 0".to_string()],
            ensures: vec!["result >= x".to_string()],
            invariants: vec!["x + y > 0".to_string()],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 4);

        let pre_count =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).count();
        let post_count = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).count();
        let inv_count = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Assertion { .. })).count();

        assert_eq!(pre_count, 2);
        assert_eq!(post_count, 1);
        assert_eq!(inv_count, 1);
    }

    #[test]
    fn test_unparseable_specs_skipped() {
        let spec = FunctionSpec {
            requires: vec!["???".to_string(), "x > 0".to_string()],
            ensures: vec!["@@@".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        // Only "x > 0" should produce a VC
        assert_eq!(vcs.len(), 1);
        assert!(matches!(&vcs[0].kind, VcKind::Precondition { .. }));
    }

    #[test]
    fn test_contract_metadata_attached() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec!["result >= 0".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        for vc in &vcs {
            let meta = vc.contract_metadata.expect("should have contract metadata");
            assert!(meta.has_requires);
            assert!(meta.has_ensures);
            assert!(!meta.has_invariant);
            assert!(!meta.has_variant);
            assert!(meta.has_any());
        }
    }

    #[test]
    fn test_ensures_result_maps_to_return_var() {
        let spec = FunctionSpec {
            requires: vec![],
            ensures: vec!["result == a + b".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 1);
        // The inner formula (before negation) should reference _0 for "result"
        match &vcs[0].formula {
            Formula::Not(inner) => {
                let free_vars = inner.free_variables();
                assert!(free_vars.contains("_0"), "result should map to _0");
                assert!(free_vars.contains("a"));
                assert!(free_vars.contains("b"));
                assert!(!free_vars.contains("result"), "result should not appear literally");
            }
            _ => panic!("expected Not(...)"),
        }
    }

    #[test]
    fn test_has_spec_vcs_empty() {
        assert!(!has_spec_vcs(&FunctionSpec::default()));
    }

    #[test]
    fn test_has_spec_vcs_with_parseable() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec![],
            invariants: vec![],
        };
        assert!(has_spec_vcs(&spec));
    }

    #[test]
    fn test_has_spec_vcs_all_unparseable() {
        let spec = FunctionSpec {
            requires: vec!["???".to_string()],
            ensures: vec!["@@@".to_string()],
            invariants: vec![],
        };
        assert!(!has_spec_vcs(&spec));
    }

    #[test]
    fn test_complex_ensures_with_arithmetic() {
        let spec = FunctionSpec {
            requires: vec![],
            ensures: vec!["result >= x + y && result <= x * y".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        assert_eq!(vcs.len(), 1);
        // Should be Not(And([Ge(...), Le(...)]))
        match &vcs[0].formula {
            Formula::Not(inner) => {
                assert!(matches!(inner.as_ref(), Formula::And(terms) if terms.len() == 2));
            }
            _ => panic!("expected Not(And(...))"),
        }
    }

    #[test]
    fn test_vcs_reference_correct_function_name() {
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec!["result > 0".to_string()],
            invariants: vec!["x > 0".to_string()],
        };
        let func = spec_test_function(spec);
        let vcs = generate_spec_vcs(&func);

        for vc in &vcs {
            assert_eq!(vc.function, "spec_fn");
        }
    }

    #[test]
    fn test_spec_vcs_integrated_with_generate_vcs() {
        // Verify that spec VCs show up in the full generate_vcs pipeline
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec!["result >= 0".to_string()],
            invariants: vec![],
        };
        let func = spec_test_function(spec);
        let vcs = crate::generate_vcs(&func);

        let pre_count =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).count();
        let post_count = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).count();

        assert!(pre_count >= 1, "should have at least 1 precondition VC from spec");
        assert!(post_count >= 1, "should have at least 1 postcondition VC from spec");
    }
}
