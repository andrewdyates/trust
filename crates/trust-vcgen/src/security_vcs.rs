// trust-vcgen/security_vcs.rs: Security-focused verification condition generation
//
// Takes binary patterns from binary_analysis.rs and generates solver-ready VCs
// for security properties: buffer overflow, use-after-free, format string
// injection, integer overflow in security contexts, and control flow hijack.
//
// All generated VCs use VcKind::Assertion with `[security:*]` prefixed
// messages so reporters can distinguish them from other assertion VCs.
//
// Part of #148: Binary analysis pipeline
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::*;

use crate::binary_analysis::{BinaryPattern, RecoveredType};

// ────────────────────────────────────────────────────────────────────────────
// Security property types
// ────────────────────────────────────────────────────────────────────────────

/// A categorized security property that can be checked via VC generation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SecurityProperty {
    /// Buffer overflow: write beyond allocated bounds.
    BufferOverflow {
        /// Buffer local index.
        buffer_local: usize,
        /// Known buffer size, if available.
        buffer_size: Option<u64>,
        /// Access size (bytes written).
        access_size: Option<u64>,
    },
    /// Use-after-free: accessing memory after deallocation.
    UseAfterFree {
        /// The freed local.
        freed_local: usize,
    },
    /// Format string injection: attacker-controlled format string.
    FormatString {
        /// The callee consuming the format string.
        callee: String,
    },
    /// Integer overflow in a security-sensitive context (size calculation,
    /// allocation, bounds check).
    IntegerOverflowSecurity {
        /// The operation that may overflow.
        op: BinOp,
        /// How the result is used.
        context: String,
    },
    /// Control flow hijack: indirect call through potentially corrupted
    /// function pointer.
    ControlFlowHijack {
        /// Local holding the function pointer.
        fn_ptr_local: usize,
    },
    /// Stack buffer overflow: writing beyond a stack-allocated array.
    StackBufferOverflow {
        /// Buffer local index.
        buffer_local: usize,
        /// Stack buffer size.
        buffer_size: u64,
    },
}

impl SecurityProperty {
    /// Human-readable description for reports.
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            Self::BufferOverflow { buffer_local, buffer_size, access_size } => {
                let size_info = match (buffer_size, access_size) {
                    (Some(bs), Some(as_)) => format!(" (buf={bs}, access={as_})"),
                    (Some(bs), None) => format!(" (buf={bs})"),
                    _ => String::new(),
                };
                format!("buffer overflow on _{buffer_local}{size_info}")
            }
            Self::UseAfterFree { freed_local } => {
                format!("use-after-free of _{freed_local}")
            }
            Self::FormatString { callee } => {
                format!("format string injection in {callee}")
            }
            Self::IntegerOverflowSecurity { op, context } => {
                format!("integer overflow ({op:?}) in security context: {context}")
            }
            Self::ControlFlowHijack { fn_ptr_local } => {
                format!("control flow hijack via _{fn_ptr_local}")
            }
            Self::StackBufferOverflow { buffer_local, buffer_size } => {
                format!("stack buffer overflow on _{buffer_local} (size={buffer_size})")
            }
        }
    }

    /// Severity level (higher = more critical). Range 1-10.
    #[must_use]
    pub fn severity(&self) -> u8 {
        match self {
            Self::ControlFlowHijack { .. } => 10,
            Self::UseAfterFree { .. } => 9,
            Self::BufferOverflow { .. } => 8,
            Self::StackBufferOverflow { .. } => 8,
            Self::FormatString { .. } => 7,
            Self::IntegerOverflowSecurity { .. } => 6,
        }
    }

    /// CWE identifier for the vulnerability class.
    #[must_use]
    pub fn cwe_id(&self) -> &str {
        match self {
            Self::BufferOverflow { .. } | Self::StackBufferOverflow { .. } => "CWE-120",
            Self::UseAfterFree { .. } => "CWE-416",
            Self::FormatString { .. } => "CWE-134",
            Self::IntegerOverflowSecurity { .. } => "CWE-190",
            Self::ControlFlowHijack { .. } => "CWE-822",
        }
    }
}

/// A security VC with its associated property metadata.
#[derive(Debug, Clone)]
pub struct SecurityVc {
    /// The solver-facing verification condition.
    pub vc: VerificationCondition,
    /// The security property this VC checks.
    pub property: SecurityProperty,
}

// ────────────────────────────────────────────────────────────────────────────
// VC generation
// ────────────────────────────────────────────────────────────────────────────

/// Generate security-focused VCs from detected binary patterns and recovered types.
///
/// This is the main entry point. It converts each `BinaryPattern` into one or
/// more `SecurityVc` items with solver-ready formulas.
#[must_use]
pub fn generate_security_vcs(
    func: &VerifiableFunction,
    patterns: &[BinaryPattern],
    recovered_types: &[RecoveredType],
) -> Vec<SecurityVc> {
    let mut vcs = Vec::new();

    for pattern in patterns {
        match pattern {
            BinaryPattern::BufferCopy { src_local, dst_local, size_local, block_id } => {
                generate_buffer_overflow_vcs(
                    func,
                    *dst_local,
                    *src_local,
                    *size_local,
                    *block_id,
                    recovered_types,
                    &mut vcs,
                );
            }
            BinaryPattern::FormatString { callee, block_id, .. } => {
                generate_format_string_vcs(func, callee, *block_id, &mut vcs);
            }
            BinaryPattern::IndirectCall { fn_ptr_local, block_id } => {
                generate_control_flow_hijack_vcs(func, *fn_ptr_local, *block_id, &mut vcs);
            }
            BinaryPattern::StackBuffer { local, length, block_id, .. } => {
                generate_stack_overflow_vcs(func, *local, *length, *block_id, &mut vcs);
            }
            BinaryPattern::UncheckedSizeUse { size_local, use_block, use_kind } => {
                generate_integer_overflow_security_vcs(
                    func,
                    *size_local,
                    *use_block,
                    *use_kind,
                    &mut vcs,
                );
            }
            BinaryPattern::UseAfterFree { dropped_local, use_block, .. } => {
                generate_use_after_free_vcs(func, *dropped_local, *use_block, &mut vcs);
            }
        }
    }

    vcs
}

/// Generate buffer overflow VCs for a memory copy operation.
fn generate_buffer_overflow_vcs(
    func: &VerifiableFunction,
    dst_local: usize,
    _src_local: usize,
    size_local: Option<usize>,
    block_id: BlockId,
    recovered_types: &[RecoveredType],
    out: &mut Vec<SecurityVc>,
) {
    let span = block_span(func, block_id);

    // Look up buffer size from recovered types
    let buffer_size = recovered_types.iter().find_map(|rt| match rt {
        RecoveredType::BufferPointer { local, buffer_len, .. } if *local == dst_local => {
            *buffer_len
        }
        RecoveredType::ArrayLike { local, length, .. } if *local == dst_local => *length,
        _ => None,
    });

    // VC 1: copy size must not exceed destination buffer size
    let copy_size_var = match size_local {
        Some(sl) => Formula::Var(format!("copy_size_{sl}"), Sort::Int),
        None => Formula::Var("copy_size_unknown".into(), Sort::Int),
    };

    let dst_size_var = match buffer_size {
        Some(bs) => Formula::Int(bs as i128),
        None => Formula::Var(format!("dst_capacity_{dst_local}"), Sort::Int),
    };

    out.push(SecurityVc {
        vc: VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[security:buffer_overflow] copy size exceeds destination buffer _{dst_local}"
                ),
            },
            function: func.name.clone(),
            location: span.clone(),
            // Violation: copy_size > dst_capacity
            formula: Formula::Gt(
                Box::new(copy_size_var.clone()),
                Box::new(dst_size_var),
            ),
            contract_metadata: None,
        },
        property: SecurityProperty::BufferOverflow {
            buffer_local: dst_local,
            buffer_size,
            access_size: None,
        },
    });

    // VC 2: copy size must be non-negative
    out.push(SecurityVc {
        vc: VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[security:buffer_overflow] negative copy size for _{dst_local}"
                ),
            },
            function: func.name.clone(),
            location: span,
            // Violation: copy_size < 0
            formula: Formula::Lt(
                Box::new(copy_size_var),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        },
        property: SecurityProperty::BufferOverflow {
            buffer_local: dst_local,
            buffer_size,
            access_size: None,
        },
    });
}

/// Generate format string injection VCs.
fn generate_format_string_vcs(
    func: &VerifiableFunction,
    callee: &str,
    block_id: BlockId,
    out: &mut Vec<SecurityVc>,
) {
    let span = block_span(func, block_id);

    // VC: format string argument must not be attacker-controlled
    let tainted_var = Formula::Var(
        format!("fmt_tainted_{}", callee.replace("::", "_")),
        Sort::Bool,
    );

    out.push(SecurityVc {
        vc: VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[security:format_string] attacker-controlled format string in {callee}"
                ),
            },
            function: func.name.clone(),
            location: span,
            // Violation: format string is tainted
            formula: tainted_var,
            contract_metadata: None,
        },
        property: SecurityProperty::FormatString {
            callee: callee.to_string(),
        },
    });
}

/// Generate control flow hijack VCs for indirect calls.
fn generate_control_flow_hijack_vcs(
    func: &VerifiableFunction,
    fn_ptr_local: usize,
    block_id: BlockId,
    out: &mut Vec<SecurityVc>,
) {
    let span = block_span(func, block_id);
    let ptr_var = Formula::Var(format!("fn_ptr_{fn_ptr_local}"), Sort::Int);

    // VC 1: function pointer must point to valid code
    let code_range_lo = Formula::Var("code_segment_lo".into(), Sort::Int);
    let code_range_hi = Formula::Var("code_segment_hi".into(), Sort::Int);

    out.push(SecurityVc {
        vc: VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[security:control_flow] function pointer _{fn_ptr_local} outside code segment"
                ),
            },
            function: func.name.clone(),
            location: span.clone(),
            // Violation: ptr < code_lo OR ptr >= code_hi
            formula: Formula::Or(vec![
                Formula::Lt(
                    Box::new(ptr_var.clone()),
                    Box::new(code_range_lo),
                ),
                Formula::Ge(
                    Box::new(ptr_var.clone()),
                    Box::new(code_range_hi),
                ),
            ]),
            contract_metadata: None,
        },
        property: SecurityProperty::ControlFlowHijack { fn_ptr_local },
    });

    // VC 2: function pointer must not be null
    out.push(SecurityVc {
        vc: VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[security:control_flow] null function pointer _{fn_ptr_local}"
                ),
            },
            function: func.name.clone(),
            location: span,
            // Violation: ptr == 0
            formula: Formula::Eq(
                Box::new(ptr_var),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        },
        property: SecurityProperty::ControlFlowHijack { fn_ptr_local },
    });
}

/// Generate stack buffer overflow VCs.
fn generate_stack_overflow_vcs(
    func: &VerifiableFunction,
    buffer_local: usize,
    buffer_size: u64,
    block_id: BlockId,
    out: &mut Vec<SecurityVc>,
) {
    let span = block_span(func, block_id);
    let access_idx = Formula::Var(format!("stack_access_idx_{buffer_local}"), Sort::Int);

    // VC: access index must be within [0, buffer_size)
    out.push(SecurityVc {
        vc: VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[security:stack_overflow] access beyond stack buffer _{buffer_local} (size={buffer_size})"
                ),
            },
            function: func.name.clone(),
            location: span,
            // Violation: idx < 0 OR idx >= buffer_size
            formula: Formula::Or(vec![
                Formula::Lt(
                    Box::new(access_idx.clone()),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Ge(
                    Box::new(access_idx),
                    Box::new(Formula::Int(buffer_size as i128)),
                ),
            ]),
            contract_metadata: None,
        },
        property: SecurityProperty::StackBufferOverflow {
            buffer_local,
            buffer_size,
        },
    });
}

/// Generate integer overflow VCs in security-sensitive contexts.
fn generate_integer_overflow_security_vcs(
    func: &VerifiableFunction,
    size_local: usize,
    use_block: BlockId,
    use_kind: crate::binary_analysis::SizeUseKind,
    out: &mut Vec<SecurityVc>,
) {
    let span = block_span(func, use_block);
    let size_var = Formula::Var(format!("size_{size_local}"), Sort::Int);

    let context = match use_kind {
        crate::binary_analysis::SizeUseKind::Index => "array index",
        crate::binary_analysis::SizeUseKind::AllocationSize => "allocation size",
        crate::binary_analysis::SizeUseKind::CopyLength => "copy length",
        crate::binary_analysis::SizeUseKind::LoopBound => "loop bound",
    };

    // VC 1: size value must not be negative (for signed types)
    out.push(SecurityVc {
        vc: VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[security:integer_overflow] negative {context} from _{size_local}"
                ),
            },
            function: func.name.clone(),
            location: span.clone(),
            // Violation: size < 0
            formula: Formula::Lt(
                Box::new(size_var.clone()),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        },
        property: SecurityProperty::IntegerOverflowSecurity {
            op: BinOp::Add,
            context: context.to_string(),
        },
    });

    // VC 2: size value must not overflow the maximum representable value
    let max_val = Formula::Int((1i128 << 63) - 1); // conservative isize::MAX
    out.push(SecurityVc {
        vc: VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[security:integer_overflow] {context} overflow from _{size_local}"
                ),
            },
            function: func.name.clone(),
            location: span,
            // Violation: size > MAX
            formula: Formula::Gt(
                Box::new(size_var),
                Box::new(max_val),
            ),
            contract_metadata: None,
        },
        property: SecurityProperty::IntegerOverflowSecurity {
            op: BinOp::Add,
            context: context.to_string(),
        },
    });
}

/// Generate use-after-free VCs.
fn generate_use_after_free_vcs(
    func: &VerifiableFunction,
    freed_local: usize,
    use_block: BlockId,
    out: &mut Vec<SecurityVc>,
) {
    let span = block_span(func, use_block);

    // VC: accessing freed memory is always a violation
    // We use Bool(true) to indicate "this is always a finding if the pattern exists"
    // (similar to the missing-SAFETY-comment pattern in unsafe_verify.rs)
    out.push(SecurityVc {
        vc: VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[security:use_after_free] access to _{freed_local} after drop"
                ),
            },
            function: func.name.clone(),
            location: span,
            // Always a finding: use after free is unconditionally unsafe
            formula: Formula::Bool(true),
            contract_metadata: None,
        },
        property: SecurityProperty::UseAfterFree { freed_local },
    });
}

// ────────────────────────────────────────────────────────────────────────────
// Helpers
// ────────────────────────────────────────────────────────────────────────────

/// Get the source span for a block, falling back to the function span.
fn block_span(func: &VerifiableFunction, block_id: BlockId) -> SourceSpan {
    func.body
        .blocks
        .iter()
        .find(|b| b.id == block_id)
        .and_then(|b| {
            // Use the first statement's span, or the terminator's span
            b.stmts.iter().find_map(|s| {
                if let Statement::Assign { span, .. } = s
                    && span != &SourceSpan::default() {
                        return Some(span.clone());
                    }
                None
            }).or_else(|| match &b.terminator {
                Terminator::Call { span, .. }
                | Terminator::Assert { span, .. }
                | Terminator::Drop { span, .. }
                | Terminator::SwitchInt { span, .. } => {
                    if span != &SourceSpan::default() {
                        Some(span.clone())
                    } else {
                        None
                    }
                }
                _ => None,
            })
        })
        .unwrap_or_else(|| func.span.clone())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary_analysis::{detect_binary_patterns, recover_types, SizeUseKind};

    /// Helper: build a buffer copy function (same as binary_analysis tests).
    fn buffer_copy_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "do_copy".to_string(),
            def_path: "test::do_copy".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::Int { width: 8, signed: false }) },
                        name: Some("src".into()),
                    },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::Int { width: 8, signed: false }) },
                        name: Some("dst".into()),
                    },
                    LocalDecl {
                        index: 3,
                        ty: Ty::usize(),
                        name: Some("len".into()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "core::ptr::copy_nonoverlapping".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(3)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan {
                            file: "test.rs".into(),
                            line_start: 5,
                            col_start: 4,
                            line_end: 5,
                            col_end: 50,
                        },
                        atomic: None,
                    },
                }],
                arg_count: 3,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Helper: build a use-after-free function.
    fn uaf_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "uaf".to_string(),
            def_path: "test::uaf".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                        name: Some("ptr".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("val".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Drop {
                            place: Place::local(1),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // ── End-to-end tests ──

    #[test]
    fn test_generate_security_vcs_buffer_overflow() {
        let func = buffer_copy_function();
        let patterns = detect_binary_patterns(&func);
        let types = recover_types(&func);
        let vcs = generate_security_vcs(&func, &patterns, &types);

        let overflow_vcs: Vec<_> = vcs
            .iter()
            .filter(|svc| matches!(&svc.property, SecurityProperty::BufferOverflow { .. }))
            .collect();
        assert_eq!(overflow_vcs.len(), 2, "should generate 2 buffer overflow VCs (size + negative)");

        // Check messages contain [security:buffer_overflow]
        for svc in &overflow_vcs {
            if let VcKind::Assertion { message } = &svc.vc.kind {
                assert!(
                    message.contains("[security:buffer_overflow]"),
                    "message should have security prefix: {message}"
                );
            }
        }
    }

    #[test]
    fn test_generate_security_vcs_use_after_free() {
        let func = uaf_function();
        let patterns = detect_binary_patterns(&func);
        let types = recover_types(&func);
        let vcs = generate_security_vcs(&func, &patterns, &types);

        let uaf_vcs: Vec<_> = vcs
            .iter()
            .filter(|svc| matches!(&svc.property, SecurityProperty::UseAfterFree { .. }))
            .collect();
        assert_eq!(uaf_vcs.len(), 1, "should generate 1 use-after-free VC");

        // UAF is always a finding
        assert!(
            matches!(uaf_vcs[0].vc.formula, Formula::Bool(true)),
            "UAF VC should be Bool(true) (always a finding)"
        );

        if let VcKind::Assertion { message } = &uaf_vcs[0].vc.kind {
            assert!(message.contains("[security:use_after_free]"));
        }
    }

    #[test]
    fn test_generate_security_vcs_format_string() {
        let func = VerifiableFunction {
            name: "do_format".to_string(),
            def_path: "test::do_format".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::Int { width: 8, signed: false }) },
                        name: Some("fmt".into()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "std::fmt::write".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                }],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let patterns = detect_binary_patterns(&func);
        let types = recover_types(&func);
        let vcs = generate_security_vcs(&func, &patterns, &types);

        let fmt_vcs: Vec<_> = vcs
            .iter()
            .filter(|svc| matches!(&svc.property, SecurityProperty::FormatString { .. }))
            .collect();
        assert_eq!(fmt_vcs.len(), 1, "should generate 1 format string VC");

        if let VcKind::Assertion { message } = &fmt_vcs[0].vc.kind {
            assert!(message.contains("[security:format_string]"));
        }
    }

    #[test]
    fn test_generate_security_vcs_empty_patterns() {
        let func = VerifiableFunction {
            name: "safe".to_string(),
            def_path: "test::safe".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::u32(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let vcs = generate_security_vcs(&func, &[], &[]);
        assert!(vcs.is_empty(), "no patterns should produce no VCs");
    }

    // ── SecurityProperty tests ──

    #[test]
    fn test_security_property_descriptions() {
        let props = vec![
            SecurityProperty::BufferOverflow {
                buffer_local: 1,
                buffer_size: Some(256),
                access_size: Some(512),
            },
            SecurityProperty::UseAfterFree { freed_local: 2 },
            SecurityProperty::FormatString { callee: "printf".into() },
            SecurityProperty::IntegerOverflowSecurity {
                op: BinOp::Mul,
                context: "allocation size".into(),
            },
            SecurityProperty::ControlFlowHijack { fn_ptr_local: 3 },
            SecurityProperty::StackBufferOverflow {
                buffer_local: 4,
                buffer_size: 1024,
            },
        ];

        for p in &props {
            let desc = p.description();
            assert!(!desc.is_empty(), "description should not be empty for {p:?}");
        }

        assert!(props[0].description().contains("buffer overflow"));
        assert!(props[1].description().contains("use-after-free"));
        assert!(props[2].description().contains("format string"));
        assert!(props[3].description().contains("integer overflow"));
        assert!(props[4].description().contains("control flow hijack"));
        assert!(props[5].description().contains("stack buffer overflow"));
    }

    #[test]
    fn test_security_property_severity_ordering() {
        let cfh = SecurityProperty::ControlFlowHijack { fn_ptr_local: 0 };
        let uaf = SecurityProperty::UseAfterFree { freed_local: 0 };
        let bof = SecurityProperty::BufferOverflow {
            buffer_local: 0,
            buffer_size: None,
            access_size: None,
        };
        let fmt = SecurityProperty::FormatString { callee: "x".into() };
        let iof = SecurityProperty::IntegerOverflowSecurity {
            op: BinOp::Add,
            context: "x".into(),
        };

        assert!(cfh.severity() > uaf.severity());
        assert!(uaf.severity() > bof.severity());
        assert!(bof.severity() > fmt.severity());
        assert!(fmt.severity() > iof.severity());
    }

    #[test]
    fn test_security_property_cwe_ids() {
        assert_eq!(
            SecurityProperty::BufferOverflow {
                buffer_local: 0,
                buffer_size: None,
                access_size: None,
            }
            .cwe_id(),
            "CWE-120"
        );
        assert_eq!(
            SecurityProperty::UseAfterFree { freed_local: 0 }.cwe_id(),
            "CWE-416"
        );
        assert_eq!(
            SecurityProperty::FormatString { callee: "x".into() }.cwe_id(),
            "CWE-134"
        );
        assert_eq!(
            SecurityProperty::IntegerOverflowSecurity {
                op: BinOp::Add,
                context: "x".into(),
            }
            .cwe_id(),
            "CWE-190"
        );
        assert_eq!(
            SecurityProperty::ControlFlowHijack { fn_ptr_local: 0 }.cwe_id(),
            "CWE-822"
        );
        assert_eq!(
            SecurityProperty::StackBufferOverflow {
                buffer_local: 0,
                buffer_size: 100,
            }
            .cwe_id(),
            "CWE-120"
        );
    }

    #[test]
    fn test_security_property_serialization_roundtrip() {
        let props = vec![
            SecurityProperty::BufferOverflow {
                buffer_local: 1,
                buffer_size: Some(256),
                access_size: None,
            },
            SecurityProperty::UseAfterFree { freed_local: 2 },
            SecurityProperty::FormatString { callee: "printf".into() },
            SecurityProperty::IntegerOverflowSecurity {
                op: BinOp::Mul,
                context: "alloc".into(),
            },
            SecurityProperty::ControlFlowHijack { fn_ptr_local: 5 },
            SecurityProperty::StackBufferOverflow {
                buffer_local: 3,
                buffer_size: 512,
            },
        ];

        for prop in &props {
            let json = serde_json::to_string(prop).expect("serialize");
            let round: SecurityProperty = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(&round, prop);
        }
    }

    // ── Individual generator tests ──

    #[test]
    fn test_generate_control_flow_hijack_vcs_directly() {
        let func = VerifiableFunction {
            name: "indirect".to_string(),
            def_path: "test::indirect".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::u32(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let patterns = vec![BinaryPattern::IndirectCall {
            fn_ptr_local: 5,
            block_id: BlockId(0),
        }];
        let vcs = generate_security_vcs(&func, &patterns, &[]);

        assert_eq!(vcs.len(), 2, "should generate 2 control flow hijack VCs");
        assert!(vcs.iter().all(|svc| matches!(
            &svc.property,
            SecurityProperty::ControlFlowHijack { fn_ptr_local: 5 }
        )));

        // One should check code segment bounds, one should check null
        let messages: Vec<_> = vcs
            .iter()
            .filter_map(|svc| {
                if let VcKind::Assertion { message } = &svc.vc.kind {
                    Some(message.clone())
                } else {
                    None
                }
            })
            .collect();
        assert!(messages.iter().any(|m| m.contains("outside code segment")));
        assert!(messages.iter().any(|m| m.contains("null function pointer")));
    }

    #[test]
    fn test_generate_stack_overflow_vcs_directly() {
        let func = VerifiableFunction {
            name: "stack".to_string(),
            def_path: "test::stack".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Array { elem: Box::new(Ty::Int { width: 8, signed: false }), len: 64 },
                        name: Some("buf".into()),
                    },
                ],
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

        let patterns = vec![BinaryPattern::StackBuffer {
            local: 1,
            elem_ty: Ty::Int { width: 8, signed: false },
            length: 64,
            block_id: BlockId(0),
        }];
        let vcs = generate_security_vcs(&func, &patterns, &[]);

        assert_eq!(vcs.len(), 1, "should generate 1 stack overflow VC");
        if let VcKind::Assertion { message } = &vcs[0].vc.kind {
            assert!(message.contains("[security:stack_overflow]"));
            assert!(message.contains("size=64"));
        }
    }

    #[test]
    fn test_generate_integer_overflow_security_vcs_directly() {
        let func = VerifiableFunction {
            name: "int_ovf".to_string(),
            def_path: "test::int_ovf".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("size".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let patterns = vec![BinaryPattern::UncheckedSizeUse {
            size_local: 1,
            use_block: BlockId(0),
            use_kind: SizeUseKind::AllocationSize,
        }];
        let vcs = generate_security_vcs(&func, &patterns, &[]);

        assert_eq!(vcs.len(), 2, "should generate 2 integer overflow VCs (negative + overflow)");

        let messages: Vec<_> = vcs
            .iter()
            .filter_map(|svc| {
                if let VcKind::Assertion { message } = &svc.vc.kind {
                    Some(message.clone())
                } else {
                    None
                }
            })
            .collect();
        assert!(messages.iter().any(|m| m.contains("negative")));
        assert!(messages.iter().any(|m| m.contains("overflow")));
    }

    #[test]
    fn test_all_security_vcs_are_l0_safety() {
        let func = buffer_copy_function();
        let patterns = detect_binary_patterns(&func);
        let types = recover_types(&func);
        let vcs = generate_security_vcs(&func, &patterns, &types);

        for svc in &vcs {
            assert_eq!(
                svc.vc.kind.proof_level(),
                ProofLevel::L0Safety,
                "security VCs should be L0 Safety level"
            );
        }
    }

    #[test]
    fn test_security_vcs_have_correct_function_name() {
        let func = buffer_copy_function();
        let patterns = detect_binary_patterns(&func);
        let types = recover_types(&func);
        let vcs = generate_security_vcs(&func, &patterns, &types);

        for svc in &vcs {
            assert_eq!(svc.vc.function, "do_copy", "function name should match");
        }
    }
}
