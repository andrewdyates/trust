// trust-vcgen/resilience.rs: Failure path analysis for external dependencies
//
// For each external call site, checks whether the error path might panic.
// A "resilience violation" occurs when an external call returns Result/Option
// and the error path leads to a panic (unwrap, expect, unreachable).
//
// In MIR terms, this analyzes the SwitchInt after a Call that returns a
// Result/Option — if the error branch reaches an Unreachable or a panic
// (Assert fail / Call to panic functions), we emit a ResilienceViolation VC.
//
// Part of #53: External dependency failure modeling and resilience proofs
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

/// Check a function for resilience violations from external dependency failures.
///
/// For each external call site detected in the failure model, walk the MIR
/// downstream to determine if the error path could panic. Returns VCs for
/// each unhandled failure path.
pub(crate) fn check_resilience(
    func: &VerifiableFunction,
    failure_model: &FailureModel,
    vcs: &mut Vec<VerificationCondition>,
) {
    for dep in &failure_model.dependencies {
        // Find the block containing this external call
        let call_block = match func.body.blocks.get(dep.block.0) {
            Some(block) => block,
            None => continue,
        };

        // Get the target block (where execution continues after the call)
        let target_block_id = match &call_block.terminator {
            Terminator::Call { target: Some(target), .. } => *target,
            _ => continue,
        };

        // Check if the target block has a SwitchInt that discriminates on the
        // Result variant (Ok=0, Err=1 or vice versa). If so, follow the error
        // branch and check for panics.
        let target_block = match func.body.blocks.get(target_block_id.0) {
            Some(block) => block,
            None => continue,
        };

        let panic_paths = find_panic_paths_from_block(func, target_block_id);

        if !panic_paths.is_empty() {
            for failure_mode in &dep.failure_modes {
                for panic_path in &panic_paths {
                    vcs.push(VerificationCondition {
                        kind: VcKind::ResilienceViolation {
                            service: dep.name.clone(),
                            failure_mode: failure_mode.to_string(),
                            reason: panic_path.reason.clone(),
                        },
                        function: func.name.clone(),
                        location: panic_path.span.clone().unwrap_or_else(|| dep.span.clone()),
                        formula: Formula::Bool(true), // tRust: always satisfiable = always a violation
                        contract_metadata: None,
                    });
                }
            }
        } else {
            // No direct panic path from the call successor. Check if there's
            // a SwitchInt discriminating on the result — if not, the call result
            // might be unwrapped later. Do a deeper scan of downstream blocks.
            check_downstream_unwrap(func, target_block, dep, vcs);
        }
    }
}

/// A discovered path from an external call to a panic.
struct PanicPath {
    reason: String,
    span: Option<SourceSpan>,
}

/// Search downstream from a block for paths that lead to panics.
///
/// Uses bounded BFS (max depth 8) to avoid explosion.
fn find_panic_paths_from_block(func: &VerifiableFunction, start: BlockId) -> Vec<PanicPath> {
    let mut paths = Vec::new();
    let mut visited = vec![false; func.body.blocks.len()];
    let mut queue = std::collections::VecDeque::new();
    queue.push_back((start, 0u8));

    while let Some((block_id, depth)) = queue.pop_front() {
        if depth > 8 {
            continue;
        }
        let idx = block_id.0;
        if idx >= func.body.blocks.len() || visited[idx] {
            continue;
        }
        visited[idx] = true;

        let block = &func.body.blocks[idx];

        match &block.terminator {
            Terminator::Unreachable => {
                paths.push(PanicPath {
                    reason: "unreachable code on failure path".to_string(),
                    span: None,
                });
            }
            Terminator::Call { func: func_name, span, .. } if is_panic_call(func_name) => {
                paths.push(PanicPath {
                    reason: format!("panic call `{func_name}` on failure path"),
                    span: Some(span.clone()),
                });
            }
            Terminator::Assert { target, span, .. } => {
                // Assert can panic on the failure branch
                paths.push(PanicPath {
                    reason: "assert on failure path may panic".to_string(),
                    span: Some(span.clone()),
                });
                queue.push_back((*target, depth + 1));
            }
            Terminator::Goto(target) => {
                queue.push_back((*target, depth + 1));
            }
            Terminator::SwitchInt { targets, otherwise, .. } => {
                for (_, target) in targets {
                    queue.push_back((*target, depth + 1));
                }
                queue.push_back((*otherwise, depth + 1));
            }
            Terminator::Call { target: Some(target), .. } => {
                queue.push_back((*target, depth + 1));
            }
            Terminator::Drop { target, .. } => {
                queue.push_back((*target, depth + 1));
            }
            Terminator::Return | Terminator::Call { target: None, .. } => {
                // Return = graceful. No-target call = diverging but not necessarily our problem.
            }
            _ => {},
        }
    }

    paths
}

// strip_generics: uses trust_types::strip_generics (#160)

/// Check if a call is to a panic/abort function.
fn is_panic_call(func_name: &str) -> bool {
    let normalized = strip_generics(func_name);
    const PANIC_PATTERNS: &[&str] = &[
        "core::panicking::panic",
        "std::panicking::begin_panic",
        "core::panicking::panic_fmt",
        "std::process::abort",
        "core::panicking::panic_nounwind",
        "std::rt::begin_panic",
        "core::panic!",
    ];

    PANIC_PATTERNS.iter().any(|pattern| normalized.contains(pattern))
}

/// Check for unwrap/expect patterns downstream of an external call.
///
/// Looks for Call terminators to `unwrap`, `expect`, or `unwrap_or_else`
/// that operate on the Result from the external call.
fn check_downstream_unwrap(
    func: &VerifiableFunction,
    block: &BasicBlock,
    dep: &ExternalDependency,
    vcs: &mut Vec<VerificationCondition>,
) {
    let mut visited = vec![false; func.body.blocks.len()];
    let mut queue = std::collections::VecDeque::new();
    queue.push_back((block.id, 0u8));

    while let Some((block_id, depth)) = queue.pop_front() {
        if depth > 6 {
            continue;
        }
        let idx = block_id.0;
        if idx >= func.body.blocks.len() || visited[idx] {
            continue;
        }
        visited[idx] = true;

        let bb = &func.body.blocks[idx];

        if let Terminator::Call { func: func_name, span, target, .. } = &bb.terminator {
            if is_unwrap_call(func_name) {
                for failure_mode in &dep.failure_modes {
                    vcs.push(VerificationCondition {
                        kind: VcKind::ResilienceViolation {
                            service: dep.name.clone(),
                            failure_mode: failure_mode.to_string(),
                            reason: format!(
                                "`{func_name}` on result from `{}`",
                                dep.call_path
                            ),
                        },
                        function: func.name.clone(),
                        location: span.clone(),
                        formula: Formula::Bool(true),
                        contract_metadata: None,
                    });
                }
                // Don't continue past unwrap — it's the violation site
                continue;
            }

            if let Some(target) = target {
                queue.push_back((*target, depth + 1));
            }
        } else {
            // Follow non-call terminators
            match &bb.terminator {
                Terminator::Goto(target) => queue.push_back((*target, depth + 1)),
                Terminator::SwitchInt { targets, otherwise, .. } => {
                    for (_, target) in targets {
                        queue.push_back((*target, depth + 1));
                    }
                    queue.push_back((*otherwise, depth + 1));
                }
                Terminator::Drop { target, .. } => queue.push_back((*target, depth + 1)),
                Terminator::Assert { target, .. } => queue.push_back((*target, depth + 1)),
                _ => {}
            }
        }
    }
}

/// Check if a call is to an unwrap/expect method.
fn is_unwrap_call(func_name: &str) -> bool {
    let normalized = strip_generics(func_name);
    const UNWRAP_PATTERNS: &[&str] = &[
        "Result::unwrap",
        "Option::unwrap",
        "Result::expect",
        "Option::expect",
    ];

    UNWRAP_PATTERNS.iter().any(|pattern| normalized.contains(pattern))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a resilient function: external call followed by match on Result,
    /// both branches return gracefully (no panic).
    fn resilient_function() -> (VerifiableFunction, FailureModel) {
        let func = VerifiableFunction {
            name: "resilient_handler".to_string(),
            def_path: "server::resilient_handler".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Unit, name: Some("result".into()) },
                    LocalDecl { index: 2, ty: Ty::Unit, name: Some("discr".into()) },
                ],
                blocks: vec![
                    // bb0: external call (redis get)
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "redis::Commands::get".to_string(),
                            args: vec![],
                            dest: Place::local(1),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // bb1: match on Result discriminant
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(0, BlockId(2))], // Ok branch
                            otherwise: BlockId(3),          // Err branch
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2: Ok path - return value
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                    // bb3: Err path - return error gracefully
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let model = FailureModel {
            function: "server::resilient_handler".to_string(),
            dependencies: vec![ExternalDependency {
                name: "redis".to_string(),
                failure_modes: vec![FailureMode::Timeout, FailureMode::Error],
                block: BlockId(0),
                span: SourceSpan::default(),
                call_path: "redis::Commands::get".to_string(),
            }],
        };

        (func, model)
    }

    /// Build a non-resilient function: external call followed by unwrap.
    fn non_resilient_function() -> (VerifiableFunction, FailureModel) {
        let func = VerifiableFunction {
            name: "fragile_handler".to_string(),
            def_path: "server::fragile_handler".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Unit, name: Some("result".into()) },
                    LocalDecl { index: 2, ty: Ty::Unit, name: Some("value".into()) },
                ],
                blocks: vec![
                    // bb0: external call (redis get)
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "redis::Commands::get".to_string(),
                            args: vec![],
                            dest: Place::local(1),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // bb1: unwrap the result (will panic on error!)
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "core::result::Result::<T, E>::unwrap".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(2)),
                            span: SourceSpan {
                                file: "server.rs".into(),
                                line_start: 15,
                                col_start: 8,
                                line_end: 15,
                                col_end: 24,
                            },
                            atomic: None,
                        },
                    },
                    // bb2: use the unwrapped value
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let model = FailureModel {
            function: "server::fragile_handler".to_string(),
            dependencies: vec![ExternalDependency {
                name: "redis".to_string(),
                failure_modes: vec![FailureMode::Timeout, FailureMode::Error],
                block: BlockId(0),
                span: SourceSpan::default(),
                call_path: "redis::Commands::get".to_string(),
            }],
        };

        (func, model)
    }

    /// Build a function with panic on the error path via Unreachable terminator.
    fn unreachable_error_function() -> (VerifiableFunction, FailureModel) {
        let func = VerifiableFunction {
            name: "unreachable_handler".to_string(),
            def_path: "server::unreachable_handler".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::Unit, name: Some("result".into()) },
                    LocalDecl { index: 2, ty: Ty::Unit, name: Some("discr".into()) },
                ],
                blocks: vec![
                    // bb0: external call
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "std::fs::File::open".to_string(),
                            args: vec![],
                            dest: Place::local(1),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // bb1: switch on result
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(0, BlockId(2))],
                            otherwise: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2: Ok path
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                    // bb3: Err path -> unreachable (panic!)
                    BasicBlock {
                        id: BlockId(3),
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
        };

        let model = FailureModel {
            function: "server::unreachable_handler".to_string(),
            dependencies: vec![ExternalDependency {
                name: "filesystem".to_string(),
                failure_modes: vec![FailureMode::Error],
                block: BlockId(0),
                span: SourceSpan::default(),
                call_path: "std::fs::File::open".to_string(),
            }],
        };

        (func, model)
    }

    #[test]
    fn test_resilient_function_no_violations() {
        let (func, model) = resilient_function();
        let mut vcs = Vec::new();
        check_resilience(&func, &model, &mut vcs);

        let resilience_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(vc.kind, VcKind::ResilienceViolation { .. }))
            .collect();

        assert!(
            resilience_vcs.is_empty(),
            "resilient function should have no resilience violations, got {}",
            resilience_vcs.len()
        );
    }

    #[test]
    fn test_non_resilient_function_has_violations() {
        let (func, model) = non_resilient_function();
        let mut vcs = Vec::new();
        check_resilience(&func, &model, &mut vcs);

        let resilience_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(vc.kind, VcKind::ResilienceViolation { .. }))
            .collect();

        // Should find violations: one per failure mode (timeout, error)
        assert_eq!(
            resilience_vcs.len(), 2,
            "non-resilient function with 2 failure modes should have 2 violations"
        );

        // Verify they reference the correct service
        for vc in &resilience_vcs {
            if let VcKind::ResilienceViolation { service, reason, .. } = &vc.kind {
                assert_eq!(service, "redis");
                assert!(reason.contains("unwrap"), "reason should mention unwrap: {reason}");
            }
        }
    }

    #[test]
    fn test_unreachable_error_path_has_violations() {
        let (func, model) = unreachable_error_function();
        let mut vcs = Vec::new();
        check_resilience(&func, &model, &mut vcs);

        let resilience_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(vc.kind, VcKind::ResilienceViolation { .. }))
            .collect();

        // Should find a violation for the unreachable on error path
        assert!(
            !resilience_vcs.is_empty(),
            "function with unreachable on error path should have violations"
        );

        for vc in &resilience_vcs {
            if let VcKind::ResilienceViolation { service, .. } = &vc.kind {
                assert_eq!(service, "filesystem");
            }
        }
    }

    #[test]
    fn test_resilience_vc_proof_level() {
        let vc_kind = VcKind::ResilienceViolation {
            service: "redis".to_string(),
            failure_mode: "timeout".to_string(),
            reason: "unwrap on error".to_string(),
        };
        assert_eq!(vc_kind.proof_level(), ProofLevel::L1Functional);
    }

    #[test]
    fn test_resilience_vc_description() {
        let vc_kind = VcKind::ResilienceViolation {
            service: "redis".to_string(),
            failure_mode: "timeout".to_string(),
            reason: "unwrap on error".to_string(),
        };
        let desc = vc_kind.description();
        assert!(desc.contains("redis"));
        assert!(desc.contains("timeout"));
        assert!(desc.contains("unwrap on error"));
    }

    #[test]
    fn test_is_panic_call() {
        assert!(is_panic_call("core::panicking::panic"));
        assert!(is_panic_call("core::panicking::panic_fmt"));
        assert!(is_panic_call("std::panicking::begin_panic"));
        assert!(is_panic_call("std::process::abort"));
        assert!(!is_panic_call("std::vec::Vec::push"));
        assert!(!is_panic_call("redis::Commands::get"));
    }

    #[test]
    fn test_is_unwrap_call() {
        assert!(is_unwrap_call("core::result::Result::<T, E>::unwrap"));
        assert!(is_unwrap_call("core::option::Option::<T>::unwrap"));
        assert!(is_unwrap_call("core::result::Result::<T, E>::expect"));
        assert!(!is_unwrap_call("std::vec::Vec::push"));
    }

    #[test]
    fn test_empty_failure_model_no_vcs() {
        let func = VerifiableFunction {
            name: "simple".to_string(),
            def_path: "simple".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let model = FailureModel::new("simple");
        let mut vcs = Vec::new();
        check_resilience(&func, &model, &mut vcs);
        assert!(vcs.is_empty());
    }
}
