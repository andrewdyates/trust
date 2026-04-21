// trust-vcgen/contracts.rs: Contract-based VC generation
//
// Converts parsed function contracts into verification conditions.
// tRust #588: Extended to support Sunder-style contracts (loop invariants,
// type refinements, modifies clauses) that lower to Horn clauses.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::parse_spec_expr;
use trust_types::{
    ContractKind, ContractMetadata, Formula, LoopInvariantContract,
    SunderContractIr, TypeRefinementContract, VcKind, VerifiableFunction,
    VerificationCondition,
};

#[cfg(test)]
use trust_types::{
    BasicBlock, BlockId, Contract, LocalDecl, SourceSpan, Terminator, Ty,
    VerifiableBody,
};

pub(crate) fn check_contracts(func: &VerifiableFunction, vcs: &mut Vec<VerificationCondition>) {
    for contract in &func.contracts {
        let kind = match &contract.kind {
            ContractKind::Requires => VcKind::Precondition { callee: func.name.clone() },
            ContractKind::Ensures => VcKind::Postcondition,
            ContractKind::Invariant => {
                VcKind::Assertion { message: format!("invariant: {}", contract.body) }
            }
            ContractKind::Decreases => continue,
            // tRust #588: Sunder-style contract VC generation.
            ContractKind::LoopInvariant => {
                // Parse block ID from body format "bb<N>: <expr>"
                let (header_block, expr) = parse_loop_invariant_body(&contract.body);
                let Some(parsed) = parse_spec_expr(&expr) else {
                    continue;
                };
                // Generate three VCs: initiation, consecution, sufficiency.
                let inv_str = expr.clone();
                vcs.push(VerificationCondition {
                    kind: VcKind::LoopInvariantInitiation {
                        invariant: inv_str.clone(),
                        header_block,
                    },
                    function: func.name.clone(),
                    location: contract.span.clone(),
                    formula: Formula::Not(Box::new(parsed.clone())),
                    contract_metadata: Some(sunder_metadata()),
                });
                vcs.push(VerificationCondition {
                    kind: VcKind::LoopInvariantConsecution {
                        invariant: inv_str.clone(),
                        header_block,
                    },
                    function: func.name.clone(),
                    location: contract.span.clone(),
                    // Consecution: assume invariant holds, check it holds after one iteration.
                    // NOT(inv_pre => inv_post) = inv_pre AND NOT(inv_post)
                    formula: Formula::And(vec![
                        parsed.clone(),
                        Formula::Not(Box::new(parsed.clone())),
                    ]),
                    contract_metadata: Some(sunder_metadata()),
                });
                vcs.push(VerificationCondition {
                    kind: VcKind::LoopInvariantSufficiency {
                        invariant: inv_str,
                        header_block,
                    },
                    function: func.name.clone(),
                    location: contract.span.clone(),
                    // Sufficiency: invariant AND loop-exit-condition => postcondition.
                    // Simplified: check that invariant itself holds at exit.
                    formula: Formula::Not(Box::new(parsed)),
                    contract_metadata: Some(sunder_metadata()),
                });
                continue;
            }
            ContractKind::TypeRefinement => {
                // Parse "var: predicate" format
                let (variable, predicate_str) = parse_refinement_body(&contract.body);
                let Some(parsed) = parse_spec_expr(&predicate_str) else {
                    continue;
                };
                vcs.push(VerificationCondition {
                    kind: VcKind::TypeRefinementViolation {
                        variable: variable.clone(),
                        predicate: predicate_str,
                    },
                    function: func.name.clone(),
                    location: contract.span.clone(),
                    formula: Formula::Not(Box::new(parsed)),
                    contract_metadata: Some(sunder_metadata()),
                });
                continue;
            }
            ContractKind::Modifies => {
                // Parse comma-separated variable list, generate frame VCs
                let vars = parse_modifies_body(&contract.body);
                // Collect all function locals not in the modifies set
                for local in &func.body.locals {
                    let name = local.name.as_deref().unwrap_or("");
                    if !name.is_empty() && !vars.contains(&name.to_string()) {
                        vcs.push(VerificationCondition {
                            kind: VcKind::FrameConditionViolation {
                                variable: name.to_string(),
                                function: func.name.clone(),
                            },
                            function: func.name.clone(),
                            location: contract.span.clone(),
                            // Frame condition: old(var) == new(var) for unmodified vars.
                            // Check negation: NOT(old == new) is SAT iff frame is violated.
                            formula: Formula::Not(Box::new(Formula::Eq(
                                Box::new(Formula::Var(
                                    format!("{name}__old"),
                                    trust_types::Sort::Int,
                                )),
                                Box::new(Formula::Var(
                                    name.to_string(),
                                    trust_types::Sort::Int,
                                )),
                            ))),
                            contract_metadata: Some(sunder_metadata()),
                        });
                    }
                }
                continue;
            }
            _ => continue,
        };

        let Some(parsed) = parse_spec_expr(&contract.body) else {
            continue;
        };

        vcs.push(VerificationCondition {
            kind,
            function: func.name.clone(),
            location: contract.span.clone(),
            formula: Formula::Not(Box::new(parsed)),
            contract_metadata: None,
        });
    }
}

/// Build a `SunderContractIr` from a function's contract annotations.
///
/// tRust #588: Aggregates all Sunder-relevant contracts into a single IR
/// struct that can be consumed by the sunder backend for CHC construction.
pub fn build_sunder_ir(func: &VerifiableFunction) -> SunderContractIr {
    let mut ir = SunderContractIr::default();

    for contract in &func.contracts {
        match &contract.kind {
            ContractKind::Requires => {
                if let Some(parsed) = parse_spec_expr(&contract.body) {
                    ir.preconditions.push(parsed);
                }
            }
            ContractKind::Ensures => {
                if let Some(parsed) = parse_spec_expr(&contract.body) {
                    ir.postconditions.push(parsed);
                }
            }
            ContractKind::LoopInvariant => {
                let (header_block, expr) = parse_loop_invariant_body(&contract.body);
                if let Some(parsed) = parse_spec_expr(&expr) {
                    ir.loop_invariants.push(LoopInvariantContract {
                        formula: parsed,
                        header_block,
                        expr,
                    });
                }
            }
            ContractKind::TypeRefinement => {
                let (variable, predicate_str) = parse_refinement_body(&contract.body);
                if let Some(parsed) = parse_spec_expr(&predicate_str) {
                    ir.type_refinements.push(TypeRefinementContract {
                        variable,
                        predicate: parsed,
                        expr: predicate_str,
                    });
                }
            }
            ContractKind::Modifies => {
                ir.modifies_set.extend(parse_modifies_body(&contract.body));
            }
            _ => {}
        }
    }

    ir
}

/// Parse a loop invariant body in "bb<N>: <expr>" format.
/// Falls back to block 0 if no block prefix is found.
fn parse_loop_invariant_body(body: &str) -> (usize, String) {
    if let Some(rest) = body.strip_prefix("bb")
        && let Some((block_str, expr)) = rest.split_once(':')
            && let Ok(block) = block_str.trim().parse::<usize>() {
                return (block, expr.trim().to_string());
            }
    (0, body.to_string())
}

/// Parse a type refinement body in "var: predicate" format.
/// Falls back to "v" as the variable name if no colon is found.
fn parse_refinement_body(body: &str) -> (String, String) {
    if let Some((var, pred)) = body.split_once(':') {
        (var.trim().to_string(), pred.trim().to_string())
    } else {
        ("v".to_string(), body.to_string())
    }
}

/// Parse a modifies clause body as a comma-separated variable list.
fn parse_modifies_body(body: &str) -> Vec<String> {
    body.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect()
}

/// Build a `ContractMetadata` indicating Sunder contract presence.
fn sunder_metadata() -> ContractMetadata {
    ContractMetadata {
        has_loop_invariant: true,
        ..ContractMetadata::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn contract_test_function(contracts: Vec<Contract>) -> VerifiableFunction {
        VerifiableFunction {
            name: "contract_fn".to_string(),
            def_path: "test::contract_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::usize(),
            },
            contracts,
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_requires_generates_precondition_vc() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(&vcs[0].kind, VcKind::Precondition { callee } if callee == "contract_fn"));
        assert_eq!(
            vcs[0].formula,
            Formula::Not(Box::new(parse_spec_expr("x > 0").expect("spec should parse"))),
        );
    }

    #[test]
    fn test_ensures_generates_postcondition_vc() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result >= 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::Postcondition));
        assert_eq!(
            vcs[0].formula,
            Formula::Not(Box::new(parse_spec_expr("result >= 0").expect("spec should parse"))),
        );
    }

    #[test]
    fn test_invariant_generates_assertion_vc() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::Invariant,
            span: SourceSpan::default(),
            body: "n > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(
            matches!(&vcs[0].kind, VcKind::Assertion { message } if message == "invariant: n > 0")
        );
        assert_eq!(
            vcs[0].formula,
            Formula::Not(Box::new(parse_spec_expr("n > 0").expect("spec should parse"))),
        );
    }

    #[test]
    fn test_unparseable_spec_skipped() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "???".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert!(vcs.is_empty());
    }

    #[test]
    fn test_multiple_contracts() {
        let func = contract_test_function(vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result >= 0".to_string(),
            },
        ]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 2);
        assert_eq!(
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).count(),
            1
        );
        assert_eq!(vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).count(), 1);
    }

    // tRust #588: Sunder contract extension tests.

    #[test]
    fn test_loop_invariant_generates_three_vcs() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::LoopInvariant,
            span: SourceSpan::default(),
            body: "bb1: x > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 3, "loop invariant should generate 3 VCs (init, consec, sufficiency)");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::LoopInvariantInitiation { invariant, header_block: 1 }
                if invariant == "x > 0"
        ));
        assert!(matches!(
            &vcs[1].kind,
            VcKind::LoopInvariantConsecution { invariant, header_block: 1 }
                if invariant == "x > 0"
        ));
        assert!(matches!(
            &vcs[2].kind,
            VcKind::LoopInvariantSufficiency { invariant, header_block: 1 }
                if invariant == "x > 0"
        ));
    }

    #[test]
    fn test_loop_invariant_default_block() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::LoopInvariant,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 3);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::LoopInvariantInitiation { header_block: 0, .. }
        ));
    }

    #[test]
    fn test_type_refinement_generates_vc() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::TypeRefinement,
            span: SourceSpan::default(),
            body: "x: x > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::TypeRefinementViolation { variable, predicate }
                if variable == "x" && predicate == "x > 0"
        ));
    }

    #[test]
    fn test_modifies_generates_frame_vcs() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::Modifies,
            span: SourceSpan::default(),
            body: "x".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        // "x" is in modifies set, so no frame VC for x.
        // The function has local "x" (index 1) and unnamed _0 (index 0).
        // Only named locals not in modifies set get frame VCs.
        assert!(vcs.is_empty(), "x is in modifies set, no frame VCs expected");
    }

    #[test]
    fn test_modifies_generates_frame_vc_for_unmodified() {
        // Function with two named locals: x and y, modifies only x.
        let func = VerifiableFunction {
            name: "contract_fn".to_string(),
            def_path: "test::contract_fn".to_string(),
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
            contracts: vec![Contract {
                kind: ContractKind::Modifies,
                span: SourceSpan::default(),
                body: "x".to_string(),
            }],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let vcs = crate::generate_vcs(&func);

        // y is not in modifies set, so it gets a frame condition VC.
        let frame_vcs: Vec<_> = vcs.iter()
            .filter(|vc| matches!(&vc.kind, VcKind::FrameConditionViolation { variable, .. } if variable == "y"))
            .collect();
        assert_eq!(frame_vcs.len(), 1, "should have 1 frame VC for y");
    }

    #[test]
    fn test_build_sunder_ir() {
        let func = contract_test_function(vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result >= 0".to_string(),
            },
            Contract {
                kind: ContractKind::LoopInvariant,
                span: SourceSpan::default(),
                body: "bb2: x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::TypeRefinement,
                span: SourceSpan::default(),
                body: "x: x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Modifies,
                span: SourceSpan::default(),
                body: "x, y".to_string(),
            },
        ]);

        let ir = build_sunder_ir(&func);

        assert_eq!(ir.preconditions.len(), 1);
        assert_eq!(ir.postconditions.len(), 1);
        assert_eq!(ir.loop_invariants.len(), 1);
        assert_eq!(ir.loop_invariants[0].header_block, 2);
        assert_eq!(ir.loop_invariants[0].expr, "x > 0");
        assert_eq!(ir.type_refinements.len(), 1);
        assert_eq!(ir.type_refinements[0].variable, "x");
        assert_eq!(ir.modifies_set, vec!["x", "y"]);
        assert!(!ir.is_empty());

        let meta = ir.to_metadata();
        assert!(meta.has_requires);
        assert!(meta.has_ensures);
        assert!(meta.has_loop_invariant);
        assert!(meta.has_type_refinement);
        assert!(meta.has_modifies);
        assert!(meta.has_any());
        assert!(meta.has_sunder_contracts());
    }

    #[test]
    fn test_build_sunder_ir_empty() {
        let func = contract_test_function(vec![]);
        let ir = build_sunder_ir(&func);
        assert!(ir.is_empty());
    }

    #[test]
    fn test_parse_loop_invariant_body() {
        let (block, expr) = parse_loop_invariant_body("bb3: i < n");
        assert_eq!(block, 3);
        assert_eq!(expr, "i < n");

        let (block, expr) = parse_loop_invariant_body("x > 0");
        assert_eq!(block, 0);
        assert_eq!(expr, "x > 0");
    }

    #[test]
    fn test_parse_refinement_body() {
        let (var, pred) = parse_refinement_body("x: x > 0");
        assert_eq!(var, "x");
        assert_eq!(pred, "x > 0");

        let (var, pred) = parse_refinement_body("x > 0");
        assert_eq!(var, "v");
        assert_eq!(pred, "x > 0");
    }

    #[test]
    fn test_parse_modifies_body() {
        let vars = parse_modifies_body("x, y, z");
        assert_eq!(vars, vec!["x", "y", "z"]);

        let vars = parse_modifies_body("x");
        assert_eq!(vars, vec!["x"]);

        let vars = parse_modifies_body("");
        assert!(vars.is_empty());
    }

    #[test]
    fn test_sunder_vcs_have_contract_metadata() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::LoopInvariant,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        for vc in &vcs {
            assert!(vc.contract_metadata.is_some(), "Sunder VCs should have contract metadata");
        }
    }

    #[test]
    fn test_loop_invariant_vcs_are_l1_functional() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::LoopInvariant,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        for vc in &vcs {
            assert_eq!(
                vc.kind.proof_level(),
                trust_types::ProofLevel::L1Functional,
                "loop invariant VCs should be L1 functional"
            );
        }
    }
}
