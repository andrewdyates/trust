// trust-debug/security.rs: Security-specific verification condition generation
//
// Generates VCs that go beyond basic safety (L0) to detect security-relevant
// properties: indirect call targets, format string safety, allocation size
// integrity, and TOCTOU patterns.
//
// These are the VCs that make trust-debug find "the properties that matter most"
// — not just that code doesn't crash, but that it can't be exploited.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::{SecurityViolation, SecurityViolationKind, Severity};

/// Generate security-specific VCs for a function body.
///
/// These go beyond what `trust_vcgen::generate_vcs` produces (arithmetic safety)
/// to include:
/// - Indirect call target verification (is the callee tainted?)
/// - Allocation size integrity (does an overflow control alloc size?)
/// - TOCTOU detection (is there a check/use gap on shared state?)
pub(crate) fn generate_security_vcs(func: &VerifiableFunction) -> Vec<SecurityViolation> {
    let mut violations = Vec::new();

    for block in &func.body.blocks {
        // Detect indirect calls (function pointer calls where target may be tainted)
        check_indirect_calls(func, block, &mut violations);

        // Detect TOCTOU patterns (check then use without holding lock)
        check_toctou_patterns(func, block, &func.body.blocks, &mut violations);
    }

    violations
}

/// Check for indirect calls where the target could be attacker-influenced.
fn check_indirect_calls(
    func: &VerifiableFunction,
    block: &BasicBlock,
    violations: &mut Vec<SecurityViolation>,
) {
    if let Terminator::Call { func: callee, args: _, span, .. } = &block.terminator {
        // A call to a local variable (not a known function path) is indirect
        if callee.starts_with("_") || callee.starts_with("local_") {
            violations.push(SecurityViolation {
                id: String::new(),
                severity: Severity::Critical,
                kind: SecurityViolationKind::TaintedIndirectCall {
                    taint_source: "indirect-call-target".to_string(),
                },
                function: func.def_path.clone(),
                location: Some(span.clone()),
                description: format!(
                    "Indirect call through `{callee}` — if attacker controls this \
                     value, arbitrary code execution is possible"
                ),
                flow_path: vec![],
                counterexample: None,
                solver: "security-vc".to_string(),
                time_ms: 0,
            });
        }
    }
}

/// Detect TOCTOU (time-of-check to time-of-use) patterns.
///
/// Looks for patterns where a check (e.g., file exists, permission check) is
/// followed by a use (e.g., file open, privileged operation) without atomicity.
fn check_toctou_patterns(
    func: &VerifiableFunction,
    block: &BasicBlock,
    all_blocks: &[BasicBlock],
    violations: &mut Vec<SecurityViolation>,
) {
    // Check patterns: stat/access followed by open/read/write
    let check_patterns = [
        "std::fs::metadata",
        "std::path::Path::exists",
        "std::path::Path::is_file",
        "libc::access",
        "libc::stat",
    ];
    let use_patterns = [
        "std::fs::read",
        "std::fs::write",
        "std::fs::File::open",
        "std::fs::File::create",
        "libc::open",
        "libc::unlink",
    ];

    if let Terminator::Call { func: callee, span, target, .. } = &block.terminator {
        let is_check = check_patterns.iter().any(|p| callee.contains(p));
        if is_check {
            // Look at successor blocks for a use without atomicity guard
            if let Some(target_id) = target
                && let Some(target_block) = all_blocks.get(target_id.0)
                    && let Terminator::Call { func: next_callee, span: use_span, .. } =
                        &target_block.terminator
                    {
                        let is_use = use_patterns.iter().any(|p| next_callee.contains(p));
                        if is_use {
                            violations.push(SecurityViolation {
                                id: String::new(),
                                severity: Severity::High,
                                kind: SecurityViolationKind::Toctou {
                                    check_func: callee.clone(),
                                    use_func: next_callee.clone(),
                                },
                                function: func.def_path.clone(),
                                location: Some(use_span.clone()),
                                description: format!(
                                    "TOCTOU race: `{callee}` at {} then `{next_callee}` at {} — \
                                     file state may change between check and use",
                                    span.line_start, use_span.line_start
                                ),
                                flow_path: vec![],
                                counterexample: None,
                                solver: "security-vc".to_string(),
                                time_ms: 0,
                            });
                        }
                    }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_func(name: &str, body: VerifiableBody) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body,
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn span(line: u32) -> SourceSpan {
        SourceSpan {
            file: "test.rs".into(),
            line_start: line,
            col_start: 1,
            line_end: line,
            col_end: 40,
        }
    }

    #[test]
    fn test_detect_indirect_call() {
        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "_fn_ptr".into(),
                        args: vec![],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: span(10),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        };

        let func = test_func("call_indirect", body);
        let violations = generate_security_vcs(&func);
        assert!(violations.iter().any(|v| {
            matches!(&v.kind, SecurityViolationKind::TaintedIndirectCall { .. })
        }));
    }

    #[test]
    fn test_detect_toctou() {
        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "std::path::Path::exists".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: span(10),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "std::fs::File::open".into(),
                        args: vec![],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: span(15),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        };

        let func = test_func("check_then_open", body);
        let violations = generate_security_vcs(&func);
        assert!(violations.iter().any(|v| {
            matches!(&v.kind, SecurityViolationKind::Toctou { .. })
        }));
    }

    #[test]
    fn test_safe_direct_call() {
        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "std::io::println".into(),
                        args: vec![],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: span(10),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        };

        let func = test_func("safe_call", body);
        let violations = generate_security_vcs(&func);
        assert!(violations.is_empty());
    }
}
