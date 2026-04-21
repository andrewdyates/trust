// trust-vcgen/unsafe_patterns.rs: Unsafe pattern detection, classification, and VC generation
//
// Scans VerifiableFunction bodies for unsafe operations, classifies them by
// risk level, and generates targeted safety obligations (VCs) specific to
// each pattern category.
//
// Part of #132: Comprehensive unsafe code verification
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::*;

use crate::unsafe_verify::UnsafeVcKind;

// ────────────────────────────────────────────────────────────────────────────
// Unsafe pattern types
// ────────────────────────────────────────────────────────────────────────────

/// A categorized unsafe pattern detected in MIR.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum UnsafePattern {
    /// Raw pointer dereference (*ptr).
    RawPointerDeref {
        /// Local index of the pointer being dereferenced.
        pointer_local: usize,
        /// Block where the deref occurs.
        block_id: BlockId,
    },
    /// Union field access (reinterprets bits).
    UnionFieldAccess {
        /// Name of the union type.
        union_name: String,
        /// Field index accessed.
        field_index: usize,
        block_id: BlockId,
    },
    /// Call to an extern/FFI function.
    ExternCall {
        /// Fully-qualified callee name.
        callee: String,
        /// Number of arguments.
        arg_count: usize,
        block_id: BlockId,
    },
    /// Transmute or transmute_copy call.
    Transmute {
        callee: String,
        block_id: BlockId,
    },
    /// Access to a mutable static variable.
    MutableStaticAccess {
        /// Name or local index of the static.
        static_name: String,
        block_id: BlockId,
    },
    /// Inline assembly block.
    InlineAsm {
        block_id: BlockId,
    },
    /// Unsafe call to an intrinsic function.
    UnsafeIntrinsic {
        callee: String,
        block_id: BlockId,
    },
    /// Slice creation from raw parts.
    SliceFromRawParts {
        callee: String,
        block_id: BlockId,
    },
}

impl UnsafePattern {
    /// Block ID where this pattern was detected.
    #[must_use]
    pub fn block_id(&self) -> BlockId {
        match self {
            Self::RawPointerDeref { block_id, .. }
            | Self::UnionFieldAccess { block_id, .. }
            | Self::ExternCall { block_id, .. }
            | Self::Transmute { block_id, .. }
            | Self::MutableStaticAccess { block_id, .. }
            | Self::InlineAsm { block_id }
            | Self::UnsafeIntrinsic { block_id, .. }
            | Self::SliceFromRawParts { block_id, .. } => *block_id,
        }
    }

    /// Human-readable label for this pattern.
    #[must_use]
    pub fn label(&self) -> &str {
        match self {
            Self::RawPointerDeref { .. } => "raw pointer dereference",
            Self::UnionFieldAccess { .. } => "union field access",
            Self::ExternCall { .. } => "extern/FFI call",
            Self::Transmute { .. } => "transmute",
            Self::MutableStaticAccess { .. } => "mutable static access",
            Self::InlineAsm { .. } => "inline assembly",
            Self::UnsafeIntrinsic { .. } => "unsafe intrinsic",
            Self::SliceFromRawParts { .. } => "slice from raw parts",
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Risk classification
// ────────────────────────────────────────────────────────────────────────────

/// Risk level assigned to an unsafe pattern.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum RiskLevel {
    /// Low risk: well-understood pattern with known verification strategy.
    Low = 1,
    /// Medium risk: requires careful verification but has standard approach.
    Medium = 2,
    /// High risk: complex pattern requiring deep analysis.
    High = 3,
    /// Critical risk: opaque to the compiler, limited verification possible.
    Critical = 4,
}

impl RiskLevel {
    /// Numeric risk score (1-4).
    #[must_use]
    pub fn score(self) -> u8 {
        self as u8
    }

    /// Human-readable label.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Low => "low",
            Self::Medium => "medium",
            Self::High => "high",
            Self::Critical => "critical",
        }
    }
}

/// Classify the risk level of an unsafe pattern.
#[must_use]
pub fn classify_risk(pattern: &UnsafePattern) -> RiskLevel {
    match pattern {
        // Raw pointer derefs are common and have well-known safety conditions
        UnsafePattern::RawPointerDeref { .. } => RiskLevel::Medium,
        // Union field access is type punning -- needs layout analysis
        UnsafePattern::UnionFieldAccess { .. } => RiskLevel::High,
        // FFI calls are opaque -- pre/post conditions must be stated
        UnsafePattern::ExternCall { .. } => RiskLevel::High,
        // Transmute is dangerous -- layout + validity must match
        UnsafePattern::Transmute { .. } => RiskLevel::High,
        // Mutable statics have data race potential
        UnsafePattern::MutableStaticAccess { .. } => RiskLevel::High,
        // Inline asm is opaque to the compiler
        UnsafePattern::InlineAsm { .. } => RiskLevel::Critical,
        // Intrinsics are well-typed but may have preconditions
        UnsafePattern::UnsafeIntrinsic { .. } => RiskLevel::Medium,
        // Slice from raw parts needs pointer + length validity
        UnsafePattern::SliceFromRawParts { .. } => RiskLevel::Medium,
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Pattern detection
// ────────────────────────────────────────────────────────────────────────────

/// Scan a function for all unsafe patterns.
#[must_use]
pub fn detect_unsafe_patterns(func: &VerifiableFunction) -> Vec<UnsafePattern> {
    let mut patterns = Vec::new();

    for block in &func.body.blocks {
        // Check statements for raw pointer derefs
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt {
                detect_deref_pattern(rvalue, block.id, &mut patterns);
            }
        }

        // Check terminator for call-based unsafe patterns
        if let Terminator::Call { func: callee, args, .. } = &block.terminator {
            detect_call_pattern(callee, args.len(), block.id, &mut patterns);
        }
    }

    patterns
}

/// Detect raw pointer dereference patterns in an rvalue.
fn detect_deref_pattern(
    rvalue: &Rvalue,
    block_id: BlockId,
    out: &mut Vec<UnsafePattern>,
) {
    match rvalue {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
            if place.projections.iter().any(|p| matches!(p, Projection::Deref)) {
                out.push(UnsafePattern::RawPointerDeref {
                    pointer_local: place.local,
                    block_id,
                });
            }
        }
        Rvalue::Ref { place, .. } => {
            if place.projections.iter().any(|p| matches!(p, Projection::Deref)) {
                out.push(UnsafePattern::RawPointerDeref {
                    pointer_local: place.local,
                    block_id,
                });
            }
        }
        _ => {}
    }
}

/// Detect unsafe call patterns from a terminator.
fn detect_call_pattern(
    callee: &str,
    arg_count: usize,
    block_id: BlockId,
    out: &mut Vec<UnsafePattern>,
) {
    let lower = callee.to_lowercase();

    if lower.contains("mem::transmute") || lower.contains("mem::transmute_copy") {
        out.push(UnsafePattern::Transmute {
            callee: callee.to_string(),
            block_id,
        });
    } else if lower.contains("slice::from_raw_parts") {
        out.push(UnsafePattern::SliceFromRawParts {
            callee: callee.to_string(),
            block_id,
        });
    } else if lower.contains("::ffi::") || lower.contains("extern") {
        out.push(UnsafePattern::ExternCall {
            callee: callee.to_string(),
            arg_count,
            block_id,
        });
    } else if lower.contains("intrinsics::") {
        out.push(UnsafePattern::UnsafeIntrinsic {
            callee: callee.to_string(),
            block_id,
        });
    } else if lower.contains("ptr::read")
        || lower.contains("ptr::write")
        || lower.contains("ptr::copy")
        || lower.contains("ptr::swap")
        || lower.contains("ptr::replace")
        || lower.contains("ptr::drop_in_place")
        || lower.contains("alloc::alloc")
        || lower.contains("alloc::dealloc")
        || lower.contains("alloc::realloc")
        || lower.contains("str::from_utf8_unchecked")
        || lower.contains("string::from_raw_parts")
    {
        // These are unsafe calls but classified as pointer operations
        out.push(UnsafePattern::RawPointerDeref {
            pointer_local: 0, // unknown -- call-based, not deref-based
            block_id,
        });
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Safety obligation generation
// ────────────────────────────────────────────────────────────────────────────

/// A safety obligation generated from an unsafe pattern.
#[derive(Debug, Clone)]
pub struct SafetyObligation {
    /// The VC to send to the solver.
    pub vc: VerificationCondition,
    /// The pattern that generated this obligation.
    pub pattern: UnsafePattern,
    /// The risk level of the pattern.
    pub risk: RiskLevel,
    /// Categorized VC kind for audit reporting.
    pub vc_kind: UnsafeVcKind,
}

/// Generate safety obligations for all detected patterns in a function.
#[must_use]
pub fn generate_safety_obligations(
    func: &VerifiableFunction,
) -> Vec<SafetyObligation> {
    let patterns = detect_unsafe_patterns(func);
    let mut obligations = Vec::new();

    for pattern in &patterns {
        let risk = classify_risk(pattern);
        let span = find_pattern_span(func, pattern);
        generate_pattern_obligations(func, pattern, risk, &span, &mut obligations);
    }

    obligations
}

/// Find the source span for a pattern's block.
fn find_pattern_span(func: &VerifiableFunction, pattern: &UnsafePattern) -> SourceSpan {
    let block_id = pattern.block_id();
    func.body
        .blocks
        .iter()
        .find(|b| b.id == block_id)
        .map(|b| {
            // Use terminator span if available, otherwise first stmt span
            match &b.terminator {
                Terminator::Call { span, .. }
                | Terminator::Assert { span, .. }
                | Terminator::SwitchInt { span, .. }
                | Terminator::Drop { span, .. } => span.clone(),
                _ => b
                    .stmts
                    .first()
                    .and_then(|s| match s {
                        Statement::Assign { span, .. } => Some(span.clone()),
                        _ => None,
                    })
                    .unwrap_or_default(),
            }
        })
        .unwrap_or_default()
}

/// Generate VCs for a single pattern.
fn generate_pattern_obligations(
    func: &VerifiableFunction,
    pattern: &UnsafePattern,
    risk: RiskLevel,
    span: &SourceSpan,
    out: &mut Vec<SafetyObligation>,
) {
    match pattern {
        UnsafePattern::RawPointerDeref { pointer_local, .. } => {
            let ptr_name = func
                .body
                .locals
                .get(*pointer_local)
                .and_then(|d| d.name.as_deref())
                .unwrap_or(&format!("_{pointer_local}"))
                .to_string();
            let ptr_var = Formula::Var(format!("ptr_{ptr_name}"), Sort::Int);

            // Non-null check
            out.push(SafetyObligation {
                vc: VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:pattern] null check for *{ptr_name}"
                        ),
                    },
                    function: func.name.clone(),
                    location: span.clone(),
                    formula: Formula::Eq(
                        Box::new(ptr_var.clone()),
                        Box::new(Formula::Int(0)),
                    ),
                    contract_metadata: None,
                },
                pattern: pattern.clone(),
                risk,
                vc_kind: UnsafeVcKind::RawPointerDeref {
                    pointer_expr: format!("*{ptr_name}"),
                },
            });

            // Alignment check
            let align_var = Formula::Var(format!("align_{ptr_name}"), Sort::Int);
            out.push(SafetyObligation {
                vc: VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:pattern] alignment check for *{ptr_name}"
                        ),
                    },
                    function: func.name.clone(),
                    location: span.clone(),
                    formula: Formula::Not(Box::new(Formula::Eq(
                        Box::new(Formula::Rem(
                            Box::new(ptr_var.clone()),
                            Box::new(align_var),
                        )),
                        Box::new(Formula::Int(0)),
                    ))),
                    contract_metadata: None,
                },
                pattern: pattern.clone(),
                risk,
                vc_kind: UnsafeVcKind::RawPointerDeref {
                    pointer_expr: format!("*{ptr_name}"),
                },
            });

            // Bounds check
            let alloc_base = Formula::Var(format!("alloc_base_{ptr_name}"), Sort::Int);
            let alloc_size = Formula::Var(format!("alloc_size_{ptr_name}"), Sort::Int);
            out.push(SafetyObligation {
                vc: VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:pattern] bounds check for *{ptr_name}"
                        ),
                    },
                    function: func.name.clone(),
                    location: span.clone(),
                    formula: Formula::Or(vec![
                        Formula::Lt(
                            Box::new(ptr_var.clone()),
                            Box::new(alloc_base.clone()),
                        ),
                        Formula::Ge(
                            Box::new(ptr_var),
                            Box::new(Formula::Add(
                                Box::new(alloc_base),
                                Box::new(alloc_size),
                            )),
                        ),
                    ]),
                    contract_metadata: None,
                },
                pattern: pattern.clone(),
                risk,
                vc_kind: UnsafeVcKind::RawPointerDeref {
                    pointer_expr: format!("*{ptr_name}"),
                },
            });
        }
        UnsafePattern::Transmute { callee, .. } => {
            // Layout compatibility
            let src_size = Formula::Var("size_src".into(), Sort::Int);
            let dst_size = Formula::Var("size_dst".into(), Sort::Int);
            out.push(SafetyObligation {
                vc: VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:pattern] transmute layout compatibility: {callee}"
                        ),
                    },
                    function: func.name.clone(),
                    location: span.clone(),
                    formula: Formula::Not(Box::new(Formula::Eq(
                        Box::new(src_size),
                        Box::new(dst_size),
                    ))),
                    contract_metadata: None,
                },
                pattern: pattern.clone(),
                risk,
                vc_kind: UnsafeVcKind::Transmute {
                    from_ty: "T_src".into(),
                    to_ty: "T_dst".into(),
                },
            });

            // Validity invariant
            let validity = Formula::Var(
                format!("transmute_valid_{}", callee.replace("::", "_")),
                Sort::Bool,
            );
            out.push(SafetyObligation {
                vc: VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:pattern] transmute validity invariant: {callee}"
                        ),
                    },
                    function: func.name.clone(),
                    location: span.clone(),
                    formula: Formula::Not(Box::new(validity)),
                    contract_metadata: None,
                },
                pattern: pattern.clone(),
                risk,
                vc_kind: UnsafeVcKind::Transmute {
                    from_ty: "T_src".into(),
                    to_ty: "T_dst".into(),
                },
            });
        }
        UnsafePattern::ExternCall { callee, .. } => {
            // Precondition
            let precond = Formula::Var(
                format!("ffi_pre_{}", callee.replace("::", "_")),
                Sort::Bool,
            );
            out.push(SafetyObligation {
                vc: VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:pattern] FFI precondition: {callee}"
                        ),
                    },
                    function: func.name.clone(),
                    location: span.clone(),
                    formula: Formula::Not(Box::new(precond)),
                    contract_metadata: None,
                },
                pattern: pattern.clone(),
                risk,
                vc_kind: UnsafeVcKind::FfiCall {
                    callee: callee.clone(),
                },
            });

            // Null pointer argument check
            let null_arg = Formula::Var(
                format!("ffi_ptr_{}", callee.replace("::", "_")),
                Sort::Int,
            );
            out.push(SafetyObligation {
                vc: VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:pattern] FFI null arg check: {callee}"
                        ),
                    },
                    function: func.name.clone(),
                    location: span.clone(),
                    formula: Formula::Eq(
                        Box::new(null_arg),
                        Box::new(Formula::Int(0)),
                    ),
                    contract_metadata: None,
                },
                pattern: pattern.clone(),
                risk,
                vc_kind: UnsafeVcKind::FfiCall {
                    callee: callee.clone(),
                },
            });
        }
        UnsafePattern::SliceFromRawParts { callee, .. } => {
            // Pointer non-null
            let ptr = Formula::Var("slice_ptr".into(), Sort::Int);
            out.push(SafetyObligation {
                vc: VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:pattern] slice_from_raw_parts null check: {callee}"
                        ),
                    },
                    function: func.name.clone(),
                    location: span.clone(),
                    formula: Formula::Eq(
                        Box::new(ptr.clone()),
                        Box::new(Formula::Int(0)),
                    ),
                    contract_metadata: None,
                },
                pattern: pattern.clone(),
                risk,
                vc_kind: UnsafeVcKind::RawPointerDeref {
                    pointer_expr: "slice_ptr".into(),
                },
            });

            // Length within allocation bounds
            let len = Formula::Var("slice_len".into(), Sort::Int);
            let alloc_size = Formula::Var("slice_alloc_size".into(), Sort::Int);
            out.push(SafetyObligation {
                vc: VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:pattern] slice_from_raw_parts length check: {callee}"
                        ),
                    },
                    function: func.name.clone(),
                    location: span.clone(),
                    formula: Formula::Gt(
                        Box::new(len),
                        Box::new(alloc_size),
                    ),
                    contract_metadata: None,
                },
                pattern: pattern.clone(),
                risk,
                vc_kind: UnsafeVcKind::RawPointerDeref {
                    pointer_expr: "slice_ptr".into(),
                },
            });
        }
        UnsafePattern::UnionFieldAccess { union_name, field_index, .. } => {
            // Active variant check
            let active = Formula::Var(
                format!("union_active_{union_name}"),
                Sort::Int,
            );
            out.push(SafetyObligation {
                vc: VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:pattern] union active variant check: {union_name}.{field_index}"
                        ),
                    },
                    function: func.name.clone(),
                    location: span.clone(),
                    formula: Formula::Not(Box::new(Formula::Eq(
                        Box::new(active),
                        Box::new(Formula::Int(*field_index as i128)),
                    ))),
                    contract_metadata: None,
                },
                pattern: pattern.clone(),
                risk,
                vc_kind: UnsafeVcKind::UnionAccess {
                    union_name: union_name.clone(),
                    field_name: format!("field_{field_index}"),
                },
            });
        }
        UnsafePattern::MutableStaticAccess { static_name, .. } => {
            // Data race freedom (symbolic)
            let race_free = Formula::Var(
                format!("race_free_{static_name}"),
                Sort::Bool,
            );
            out.push(SafetyObligation {
                vc: VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:pattern] mutable static data race check: {static_name}"
                        ),
                    },
                    function: func.name.clone(),
                    location: span.clone(),
                    formula: Formula::Not(Box::new(race_free)),
                    contract_metadata: None,
                },
                pattern: pattern.clone(),
                risk,
                vc_kind: UnsafeVcKind::MutableStaticAccess {
                    static_name: static_name.clone(),
                },
            });
        }
        UnsafePattern::InlineAsm { .. } => {
            // Inline asm is opaque -- emit a "manual audit required" VC
            out.push(SafetyObligation {
                vc: VerificationCondition {
                    kind: VcKind::Assertion {
                        message: "[unsafe:pattern] inline assembly requires manual audit"
                            .to_string(),
                    },
                    function: func.name.clone(),
                    location: span.clone(),
                    formula: Formula::Bool(true), // always a finding
                    contract_metadata: None,
                },
                pattern: pattern.clone(),
                risk,
                vc_kind: UnsafeVcKind::InlineAsm {
                    label: "asm_block".into(),
                },
            });
        }
        UnsafePattern::UnsafeIntrinsic { callee, .. } => {
            // Intrinsic precondition check
            let precond = Formula::Var(
                format!("intrinsic_pre_{}", callee.replace("::", "_")),
                Sort::Bool,
            );
            out.push(SafetyObligation {
                vc: VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:pattern] intrinsic precondition: {callee}"
                        ),
                    },
                    function: func.name.clone(),
                    location: span.clone(),
                    formula: Formula::Not(Box::new(precond)),
                    contract_metadata: None,
                },
                pattern: pattern.clone(),
                risk,
                vc_kind: UnsafeVcKind::RawPointerDeref {
                    pointer_expr: callee.clone(),
                },
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── Test helpers ─────────────────────────────────────────────────────

    fn deref_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "deref_raw".to_string(),
            def_path: "test::deref_raw".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                        name: Some("raw_ptr".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("value".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        })),
                        span: SourceSpan {
                            file: "test.rs".into(),
                            line_start: 5,
                            col_start: 4,
                            line_end: 5,
                            col_end: 15,
                        },
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn transmute_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "transmute_fn".to_string(),
            def_path: "test::transmute_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("input".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("output".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "core::mem::transmute".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan {
                                file: "test.rs".into(),
                                line_start: 8,
                                col_start: 4,
                                line_end: 8,
                                col_end: 40,
                            },
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
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

    fn ffi_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "call_ffi".to_string(),
            def_path: "test::call_ffi".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::Int { width: 8, signed: false }) },
                        name: Some("buf".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("result".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "libc::ffi::write".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan {
                                file: "test.rs".into(),
                                line_start: 12,
                                col_start: 4,
                                line_end: 12,
                                col_end: 30,
                            },
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn safe_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "safe_add".to_string(),
            def_path: "test::safe_add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn slice_from_raw_parts_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "make_slice".to_string(),
            def_path: "test::make_slice".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::Slice { elem: Box::new(Ty::u32()) },
                        name: None,
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                        name: Some("ptr".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("len".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "core::slice::from_raw_parts".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan {
                            file: "test.rs".into(),
                            line_start: 3,
                            col_start: 4,
                            line_end: 3,
                            col_end: 40,
                        },
                        atomic: None,
                    },
                }],
                arg_count: 2,
                return_ty: Ty::Slice { elem: Box::new(Ty::u32()) },
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn intrinsic_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "use_intrinsic".to_string(),
            def_path: "test::use_intrinsic".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "core::intrinsics::unchecked_add".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan {
                            file: "test.rs".into(),
                            line_start: 5,
                            col_start: 4,
                            line_end: 5,
                            col_end: 30,
                        },
                        atomic: None,
                    },
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // ── Detection tests ─────────────────────────────────────────────────

    #[test]
    fn test_detect_deref_pattern() {
        let func = deref_function();
        let patterns = detect_unsafe_patterns(&func);
        assert_eq!(patterns.len(), 1);
        assert!(matches!(
            &patterns[0],
            UnsafePattern::RawPointerDeref { pointer_local: 1, .. }
        ));
    }

    #[test]
    fn test_detect_transmute_pattern() {
        let func = transmute_function();
        let patterns = detect_unsafe_patterns(&func);
        assert_eq!(patterns.len(), 1);
        assert!(matches!(&patterns[0], UnsafePattern::Transmute { .. }));
    }

    #[test]
    fn test_detect_ffi_pattern() {
        let func = ffi_function();
        let patterns = detect_unsafe_patterns(&func);
        assert_eq!(patterns.len(), 1);
        assert!(matches!(&patterns[0], UnsafePattern::ExternCall { .. }));
    }

    #[test]
    fn test_detect_safe_function_no_patterns() {
        let func = safe_function();
        let patterns = detect_unsafe_patterns(&func);
        assert!(patterns.is_empty());
    }

    #[test]
    fn test_detect_slice_from_raw_parts() {
        let func = slice_from_raw_parts_function();
        let patterns = detect_unsafe_patterns(&func);
        assert_eq!(patterns.len(), 1);
        assert!(matches!(
            &patterns[0],
            UnsafePattern::SliceFromRawParts { .. }
        ));
    }

    #[test]
    fn test_detect_intrinsic_pattern() {
        let func = intrinsic_function();
        let patterns = detect_unsafe_patterns(&func);
        assert_eq!(patterns.len(), 1);
        assert!(matches!(
            &patterns[0],
            UnsafePattern::UnsafeIntrinsic { .. }
        ));
    }

    // ── Risk classification tests ───────────────────────────────────────

    #[test]
    fn test_risk_level_ordering() {
        assert!(RiskLevel::Low < RiskLevel::Medium);
        assert!(RiskLevel::Medium < RiskLevel::High);
        assert!(RiskLevel::High < RiskLevel::Critical);
    }

    #[test]
    fn test_risk_level_scores() {
        assert_eq!(RiskLevel::Low.score(), 1);
        assert_eq!(RiskLevel::Medium.score(), 2);
        assert_eq!(RiskLevel::High.score(), 3);
        assert_eq!(RiskLevel::Critical.score(), 4);
    }

    #[test]
    fn test_classify_risk_deref_is_medium() {
        let pattern = UnsafePattern::RawPointerDeref {
            pointer_local: 1,
            block_id: BlockId(0),
        };
        assert_eq!(classify_risk(&pattern), RiskLevel::Medium);
    }

    #[test]
    fn test_classify_risk_transmute_is_high() {
        let pattern = UnsafePattern::Transmute {
            callee: "core::mem::transmute".into(),
            block_id: BlockId(0),
        };
        assert_eq!(classify_risk(&pattern), RiskLevel::High);
    }

    #[test]
    fn test_classify_risk_extern_is_high() {
        let pattern = UnsafePattern::ExternCall {
            callee: "libc::ffi::write".into(),
            arg_count: 1,
            block_id: BlockId(0),
        };
        assert_eq!(classify_risk(&pattern), RiskLevel::High);
    }

    #[test]
    fn test_classify_risk_inline_asm_is_critical() {
        let pattern = UnsafePattern::InlineAsm {
            block_id: BlockId(0),
        };
        assert_eq!(classify_risk(&pattern), RiskLevel::Critical);
    }

    #[test]
    fn test_classify_risk_intrinsic_is_medium() {
        let pattern = UnsafePattern::UnsafeIntrinsic {
            callee: "core::intrinsics::copy".into(),
            block_id: BlockId(0),
        };
        assert_eq!(classify_risk(&pattern), RiskLevel::Medium);
    }

    #[test]
    fn test_classify_risk_slice_raw_parts_is_medium() {
        let pattern = UnsafePattern::SliceFromRawParts {
            callee: "core::slice::from_raw_parts".into(),
            block_id: BlockId(0),
        };
        assert_eq!(classify_risk(&pattern), RiskLevel::Medium);
    }

    // ── Pattern label tests ─────────────────────────────────────────────

    #[test]
    fn test_pattern_labels() {
        let cases = vec![
            (
                UnsafePattern::RawPointerDeref {
                    pointer_local: 0,
                    block_id: BlockId(0),
                },
                "raw pointer dereference",
            ),
            (
                UnsafePattern::UnionFieldAccess {
                    union_name: "U".into(),
                    field_index: 0,
                    block_id: BlockId(0),
                },
                "union field access",
            ),
            (
                UnsafePattern::ExternCall {
                    callee: "f".into(),
                    arg_count: 0,
                    block_id: BlockId(0),
                },
                "extern/FFI call",
            ),
            (
                UnsafePattern::Transmute {
                    callee: "t".into(),
                    block_id: BlockId(0),
                },
                "transmute",
            ),
            (
                UnsafePattern::InlineAsm {
                    block_id: BlockId(0),
                },
                "inline assembly",
            ),
        ];
        for (pattern, expected) in cases {
            assert_eq!(pattern.label(), expected);
        }
    }

    // ── Safety obligation generation tests ──────────────────────────────

    #[test]
    fn test_generate_deref_obligations() {
        let func = deref_function();
        let obligations = generate_safety_obligations(&func);

        // Deref generates 3 obligations: null, alignment, bounds
        assert_eq!(obligations.len(), 3, "deref should generate 3 obligations");

        let messages: Vec<_> = obligations
            .iter()
            .map(|o| match &o.vc.kind {
                VcKind::Assertion { message } => message.clone(),
                _ => String::new(),
            })
            .collect();
        assert!(messages.iter().any(|m| m.contains("null check")));
        assert!(messages.iter().any(|m| m.contains("alignment check")));
        assert!(messages.iter().any(|m| m.contains("bounds check")));

        // All should have medium risk
        for o in &obligations {
            assert_eq!(o.risk, RiskLevel::Medium);
        }
    }

    #[test]
    fn test_generate_transmute_obligations() {
        let func = transmute_function();
        let obligations = generate_safety_obligations(&func);

        // Transmute generates 2 obligations: layout + validity
        assert_eq!(obligations.len(), 2);

        let messages: Vec<_> = obligations
            .iter()
            .map(|o| match &o.vc.kind {
                VcKind::Assertion { message } => message.clone(),
                _ => String::new(),
            })
            .collect();
        assert!(messages.iter().any(|m| m.contains("layout compatibility")));
        assert!(messages.iter().any(|m| m.contains("validity invariant")));

        for o in &obligations {
            assert_eq!(o.risk, RiskLevel::High);
        }
    }

    #[test]
    fn test_generate_ffi_obligations() {
        let func = ffi_function();
        let obligations = generate_safety_obligations(&func);

        // FFI generates 2 obligations: precondition + null arg
        assert_eq!(obligations.len(), 2);

        let messages: Vec<_> = obligations
            .iter()
            .map(|o| match &o.vc.kind {
                VcKind::Assertion { message } => message.clone(),
                _ => String::new(),
            })
            .collect();
        assert!(messages.iter().any(|m| m.contains("precondition")));
        assert!(messages.iter().any(|m| m.contains("null arg")));
    }

    #[test]
    fn test_generate_slice_raw_parts_obligations() {
        let func = slice_from_raw_parts_function();
        let obligations = generate_safety_obligations(&func);

        // slice_from_raw_parts generates 2: null + length
        assert_eq!(obligations.len(), 2);

        let messages: Vec<_> = obligations
            .iter()
            .map(|o| match &o.vc.kind {
                VcKind::Assertion { message } => message.clone(),
                _ => String::new(),
            })
            .collect();
        assert!(messages.iter().any(|m| m.contains("null check")));
        assert!(messages.iter().any(|m| m.contains("length check")));
    }

    #[test]
    fn test_generate_intrinsic_obligations() {
        let func = intrinsic_function();
        let obligations = generate_safety_obligations(&func);

        assert_eq!(obligations.len(), 1);
        assert!(matches!(
            &obligations[0].vc.kind,
            VcKind::Assertion { message } if message.contains("intrinsic precondition")
        ));
    }

    #[test]
    fn test_generate_safe_function_no_obligations() {
        let func = safe_function();
        let obligations = generate_safety_obligations(&func);
        assert!(obligations.is_empty());
    }

    #[test]
    fn test_obligations_all_l0_safety() {
        let func = deref_function();
        let obligations = generate_safety_obligations(&func);
        for o in &obligations {
            assert_eq!(
                o.vc.kind.proof_level(),
                ProofLevel::L0Safety,
                "all unsafe pattern obligations should be L0"
            );
        }
    }

    #[test]
    fn test_pattern_serialization_roundtrip() {
        let patterns = vec![
            UnsafePattern::RawPointerDeref {
                pointer_local: 1,
                block_id: BlockId(0),
            },
            UnsafePattern::Transmute {
                callee: "core::mem::transmute".into(),
                block_id: BlockId(0),
            },
            UnsafePattern::ExternCall {
                callee: "libc::ffi::write".into(),
                arg_count: 2,
                block_id: BlockId(3),
            },
            UnsafePattern::SliceFromRawParts {
                callee: "core::slice::from_raw_parts".into(),
                block_id: BlockId(0),
            },
            UnsafePattern::InlineAsm {
                block_id: BlockId(0),
            },
        ];
        for p in &patterns {
            let json = serde_json::to_string(p).expect("serialize");
            let round: UnsafePattern =
                serde_json::from_str(&json).expect("deserialize");
            assert_eq!(&round, p);
        }
    }

    #[test]
    fn test_risk_level_serialization_roundtrip() {
        for r in [
            RiskLevel::Low,
            RiskLevel::Medium,
            RiskLevel::High,
            RiskLevel::Critical,
        ] {
            let json = serde_json::to_string(&r).expect("serialize");
            let round: RiskLevel =
                serde_json::from_str(&json).expect("deserialize");
            assert_eq!(round, r);
        }
    }

    #[test]
    fn test_risk_level_labels() {
        assert_eq!(RiskLevel::Low.label(), "low");
        assert_eq!(RiskLevel::Medium.label(), "medium");
        assert_eq!(RiskLevel::High.label(), "high");
        assert_eq!(RiskLevel::Critical.label(), "critical");
    }

    #[test]
    fn test_pattern_block_id_accessor() {
        let p = UnsafePattern::Transmute {
            callee: "t".into(),
            block_id: BlockId(7),
        };
        assert_eq!(p.block_id(), BlockId(7));
    }
}
