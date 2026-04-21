// trust-vcgen/unreachable.rs: Reachable unreachable-block VC generation
//
// Generates VCs for `Terminator::Unreachable` blocks that are reachable from
// the entry block under some conjunction of guards. The VC formula is the path
// condition itself: SAT means there exists an execution reaching the block that
// MIR marked as unreachable.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::guards::guards_to_assumption;

/// Generate VCs for reachable `Unreachable` terminators.
pub(crate) fn check_unreachable(func: &VerifiableFunction, vcs: &mut Vec<VerificationCondition>) {
    for entry in func.body.path_map() {
        let Some(block) = func.body.blocks.get(entry.block.0) else {
            continue;
        };

        if !matches!(block.terminator, Terminator::Unreachable) {
            continue;
        }

        vcs.push(VerificationCondition {
            kind: VcKind::Unreachable,
            function: func.name.clone(),
            location: block_span(block).unwrap_or_else(|| func.span.clone()),
            formula: guards_to_assumption(func, &entry.guards),
            contract_metadata: None,
        });
    }
}

fn block_span(block: &BasicBlock) -> Option<SourceSpan> {
    block.stmts.iter().find_map(|stmt| match stmt {
        Statement::Assign { span, .. } => Some(span.clone()),
        Statement::Nop => None,
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn guarded_unreachable_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "guarded_unreachable".to_string(),
            def_path: "test::guarded_unreachable".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Unreachable,
                    },
                    BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn dead_unreachable_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "dead_unreachable".to_string(),
            def_path: "test::dead_unreachable".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![
                    BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Unreachable,
                    },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn entry_unreachable_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "entry_unreachable".to_string(),
            def_path: "test::entry_unreachable".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Unreachable,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn reachable_unreachable_generates_guarded_vc() {
        let func = guarded_unreachable_function();
        let mut vcs = Vec::new();

        check_unreachable(&func, &mut vcs);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::Unreachable));
        // guards.rs::guard_to_formula uses Formula::Int for all switch values
        assert_eq!(
            vcs[0].formula,
            Formula::Eq(
                Box::new(Formula::Var("flag".into(), Sort::Bool)),
                Box::new(Formula::Int(1)),
            ),
        );
    }

    #[test]
    fn dead_unreachable_block_does_not_generate_vc() {
        let func = dead_unreachable_function();
        let mut vcs = Vec::new();

        check_unreachable(&func, &mut vcs);

        assert!(vcs.is_empty());
    }

    #[test]
    fn entry_unreachable_generates_unconditional_vc() {
        let func = entry_unreachable_function();
        let mut vcs = Vec::new();

        check_unreachable(&func, &mut vcs);

        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }
}
