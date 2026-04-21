// trust-vcgen/binary_analysis/patterns.rs: Binary pattern detection and type recovery
//
// Scans VerifiableFunction bodies for security-relevant binary patterns
// (buffer copies, format strings, indirect calls, stack operations) and
// recovers types from usage patterns. This is the analysis layer that
// feeds into security_vcs.rs for VC generation.
//
// Part of #148: Binary analysis pipeline
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::*;

// ────────────────────────────────────────────────────────────────────────────
// Binary pattern types
// ────────────────────────────────────────────────────────────────────────────

/// A security-relevant binary pattern detected in a function's MIR.
///
/// These patterns correspond to common vulnerability classes found in
/// binary analysis (inspired by angr's SimProcedures and Ghidra's
/// decompiler pattern matching).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryPattern {
    /// Memory copy with potentially unchecked bounds (memcpy, memmove, ptr::copy).
    BufferCopy {
        /// Source operand (pointer/slice).
        src_local: usize,
        /// Destination operand.
        dst_local: usize,
        /// Size operand local index, if known.
        size_local: Option<usize>,
        /// Block where the copy occurs.
        block_id: BlockId,
    },
    /// Format string usage — callee takes a format string argument that
    /// could be attacker-controlled.
    FormatString {
        /// The callee function name.
        callee: String,
        /// Index of the format string argument in the call args.
        fmt_arg_index: usize,
        /// Block where the call occurs.
        block_id: BlockId,
    },
    /// Indirect call through a function pointer — potential control flow hijack.
    IndirectCall {
        /// Local holding the function pointer.
        fn_ptr_local: usize,
        /// Block where the call occurs.
        block_id: BlockId,
    },
    /// Stack buffer allocation via fixed-size array — potential stack overflow.
    StackBuffer {
        /// Local index of the array.
        local: usize,
        /// Element type.
        elem_ty: Ty,
        /// Array length.
        length: u64,
        /// Block where the allocation is used.
        block_id: BlockId,
    },
    /// Integer value flows into a size/index position without bounds check.
    UncheckedSizeUse {
        /// Local holding the integer value.
        size_local: usize,
        /// Where it's used as a size/index.
        use_block: BlockId,
        /// The operation using the size (e.g., index, alloc).
        use_kind: SizeUseKind,
    },
    /// Double free or use-after-free pattern: a local is used after a Drop.
    UseAfterFree {
        /// The local that was dropped.
        dropped_local: usize,
        /// Block where the drop occurred.
        drop_block: BlockId,
        /// Block where the use-after-free occurs.
        use_block: BlockId,
    },
}

/// How an integer value is used in a size-sensitive context.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SizeUseKind {
    /// Used as an array/slice index.
    Index,
    /// Used as an allocation size.
    AllocationSize,
    /// Used as a copy/move length.
    CopyLength,
    /// Used as a loop bound.
    LoopBound,
}

impl BinaryPattern {
    /// Human-readable description for diagnostics.
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            Self::BufferCopy { src_local, dst_local, .. } => {
                format!("buffer copy from _{src_local} to _{dst_local}")
            }
            Self::FormatString { callee, fmt_arg_index, .. } => {
                format!("format string arg {fmt_arg_index} in call to {callee}")
            }
            Self::IndirectCall { fn_ptr_local, .. } => {
                format!("indirect call through function pointer _{fn_ptr_local}")
            }
            Self::StackBuffer { local, length, .. } => {
                format!("stack buffer _{local} of length {length}")
            }
            Self::UncheckedSizeUse { size_local, use_kind, .. } => {
                let kind = match use_kind {
                    SizeUseKind::Index => "index",
                    SizeUseKind::AllocationSize => "allocation size",
                    SizeUseKind::CopyLength => "copy length",
                    SizeUseKind::LoopBound => "loop bound",
                };
                format!("unchecked size _{size_local} used as {kind}")
            }
            Self::UseAfterFree { dropped_local, .. } => {
                format!("use after free of _{dropped_local}")
            }
        }
    }

    /// The block ID where this pattern was detected.
    #[must_use]
    pub fn block_id(&self) -> BlockId {
        match self {
            Self::BufferCopy { block_id, .. }
            | Self::FormatString { block_id, .. }
            | Self::IndirectCall { block_id, .. }
            | Self::StackBuffer { block_id, .. } => *block_id,
            Self::UncheckedSizeUse { use_block, .. } => *use_block,
            Self::UseAfterFree { use_block, .. } => *use_block,
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Type recovery
// ────────────────────────────────────────────────────────────────────────────

/// A type recovered from usage patterns in binary analysis.
///
/// When lifting from binary, types are not directly available. We infer
/// them from how values are used: pointer arithmetic suggests pointers,
/// comparison with array lengths suggests indices, etc.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RecoveredType {
    /// A pointer to a buffer of known or unknown size.
    BufferPointer {
        /// Local index.
        local: usize,
        /// Inferred element size in bytes, if known.
        elem_size: Option<u64>,
        /// Inferred buffer length, if known.
        buffer_len: Option<u64>,
    },
    /// An array/slice stored on the stack or heap.
    ArrayLike { local: usize, elem_ty: Ty, length: Option<u64> },
    /// A size or length value used in allocation/bounds contexts.
    SizeValue {
        local: usize,
        /// Whether a bounds check was observed before use.
        bounds_checked: bool,
    },
    /// A function pointer.
    FunctionPointer {
        local: usize,
        /// Known target, if resolved.
        known_target: Option<String>,
    },
    /// A string (format string, file path, etc.).
    StringValue {
        local: usize,
        /// Whether the string could be attacker-controlled.
        tainted: bool,
    },
}

impl RecoveredType {
    /// The local index this recovery applies to.
    #[must_use]
    pub fn local(&self) -> usize {
        match self {
            Self::BufferPointer { local, .. }
            | Self::ArrayLike { local, .. }
            | Self::SizeValue { local, .. }
            | Self::FunctionPointer { local, .. }
            | Self::StringValue { local, .. } => *local,
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Pattern detection
// ────────────────────────────────────────────────────────────────────────────

/// Known unsafe copy function name patterns.
const COPY_PATTERNS: &[&str] = &[
    "ptr::copy",
    "ptr::copy_nonoverlapping",
    "slice::from_raw_parts",
    "intrinsics::copy",
    "memcpy",
    "memmove",
];

/// Known format-string-taking function patterns.
const FORMAT_PATTERNS: &[&str] = &[
    "fmt::write",
    "format_args",
    "println",
    "eprintln",
    "write!",
    "format!",
    "printf",
    "sprintf",
    "snprintf",
];

/// Scan a function for security-relevant binary patterns.
///
/// Examines each block's statements and terminators for patterns that
/// correspond to common vulnerability classes. Returns all detected
/// patterns sorted by block ID.
#[must_use]
pub fn detect_binary_patterns(func: &VerifiableFunction) -> Vec<BinaryPattern> {
    let mut patterns = Vec::new();

    // Track drops for use-after-free detection
    let mut dropped_locals: Vec<(usize, BlockId)> = Vec::new();

    for block in &func.body.blocks {
        // Check terminator for call-based patterns
        if let Terminator::Call { func: callee, args, span: _, .. } = &block.terminator {
            let lower = callee.to_lowercase();

            // Buffer copy detection
            if COPY_PATTERNS.iter().any(|p| lower.contains(&p.to_lowercase())) {
                let src = args.first().and_then(operand_local);
                let dst = args.get(1).and_then(operand_local);
                let size = args.get(2).and_then(operand_local);
                if let (Some(src_local), Some(dst_local)) = (src, dst) {
                    patterns.push(BinaryPattern::BufferCopy {
                        src_local,
                        dst_local,
                        size_local: size,
                        block_id: block.id,
                    });
                }
            }

            // Format string detection
            if FORMAT_PATTERNS.iter().any(|p| lower.contains(&p.to_lowercase())) {
                // First argument is typically the format string
                if !args.is_empty() {
                    patterns.push(BinaryPattern::FormatString {
                        callee: callee.clone(),
                        fmt_arg_index: 0,
                        block_id: block.id,
                    });
                }
            }
        }

        // Check for Drop terminators (for use-after-free tracking)
        if let Terminator::Drop { place, .. } = &block.terminator {
            dropped_locals.push((place.local, block.id));
        }

        // Check statements for patterns
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                // Stack buffer detection: array aggregate
                if let Rvalue::Aggregate(AggregateKind::Array, elements) = rvalue
                    && !elements.is_empty() {
                        let elem_ty = infer_operand_ty(func, &elements[0]);
                        patterns.push(BinaryPattern::StackBuffer {
                            local: place.local,
                            elem_ty,
                            length: elements.len() as u64,
                            block_id: block.id,
                        });
                    }

                // Detect use of fixed-size array types in locals
                if let Some(decl) = func.body.locals.get(place.local)
                    && let Ty::Array { elem, len } = &decl.ty
                        && matches!(rvalue, Rvalue::Aggregate(..)) {
                            patterns.push(BinaryPattern::StackBuffer {
                                local: place.local,
                                elem_ty: *elem.clone(),
                                length: *len,
                                block_id: block.id,
                            });
                        }

                // Unchecked size use: integer used as index without prior bounds check
                if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue
                    && !place.projections.is_empty()
                        && place.projections.iter().any(|p| matches!(p, Projection::Index(_)))
                    {
                        patterns.push(BinaryPattern::UncheckedSizeUse {
                            size_local: src.local,
                            use_block: block.id,
                            use_kind: SizeUseKind::Index,
                        });
                    }

                // Use-after-free: using a local that was previously dropped
                let used_locals = rvalue_used_locals(rvalue);
                for used in used_locals {
                    if let Some((_, drop_block)) = dropped_locals.iter().find(|(l, _)| *l == used) {
                        patterns.push(BinaryPattern::UseAfterFree {
                            dropped_local: used,
                            drop_block: *drop_block,
                            use_block: block.id,
                        });
                    }
                }
            }
        }
    }

    patterns
}

/// Recover types from usage patterns in a function.
///
/// Examines how locals are used (as pointers, indices, sizes, etc.) to
/// infer types that may not be explicitly available in lifted binary code.
#[must_use]
pub fn recover_types(func: &VerifiableFunction) -> Vec<RecoveredType> {
    let mut recovered = Vec::new();

    for (idx, decl) in func.body.locals.iter().enumerate() {
        match &decl.ty {
            // Pointer/reference types -> buffer pointers
            Ty::Ref { inner, .. } => {
                let (elem_size, buffer_len) = match inner.as_ref() {
                    Ty::Array { elem, len } => {
                        (elem.int_width().map(|w| u64::from(w) / 8), Some(*len))
                    }
                    Ty::Slice { elem } => (elem.int_width().map(|w| u64::from(w) / 8), None),
                    _ => (None, None),
                };
                recovered.push(RecoveredType::BufferPointer { local: idx, elem_size, buffer_len });
            }
            // Array types
            Ty::Array { elem, len } => {
                recovered.push(RecoveredType::ArrayLike {
                    local: idx,
                    elem_ty: *elem.clone(),
                    length: Some(*len),
                });
            }
            // Slice types
            Ty::Slice { elem } => {
                recovered.push(RecoveredType::ArrayLike {
                    local: idx,
                    elem_ty: *elem.clone(),
                    length: None,
                });
            }
            // Integer types used as sizes — heuristic: name contains "len", "size", "idx"
            Ty::Int { .. } => {
                if let Some(name) = &decl.name {
                    let lower = name.to_lowercase();
                    if lower.contains("len")
                        || lower.contains("size")
                        || lower.contains("count")
                        || lower.contains("idx")
                        || lower.contains("index")
                    {
                        // Check if there's a bounds check before use
                        let bounds_checked = has_bounds_check(func, idx);
                        recovered.push(RecoveredType::SizeValue { local: idx, bounds_checked });
                    }
                }
            }
            _ => {}
        }
    }

    recovered
}

// ────────────────────────────────────────────────────────────────────────────
// Helpers
// ────────────────────────────────────────────────────────────────────────────

/// Extract the local index from an operand, if it references a simple local.
fn operand_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            if place.projections.is_empty() {
                Some(place.local)
            } else {
                None
            }
        }
        Operand::Constant(_) => None,
        _ => None,
    }
}

/// Infer the type of an operand using the function's local declarations.
fn infer_operand_ty(func: &VerifiableFunction, op: &Operand) -> Ty {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            func.body.locals.get(place.local).map(|d| d.ty.clone()).unwrap_or(Ty::Int { width: 8, signed: false })
        }
        Operand::Constant(cv) => match cv {
            ConstValue::Bool(_) => Ty::Bool,
            ConstValue::Int(_) => Ty::Int { width: 64, signed: true },
            ConstValue::Uint(_, _) => Ty::Int { width: 64, signed: false },
            ConstValue::Float(_) => Ty::Float { width: 64 },
            ConstValue::Unit => Ty::Unit,
            _ => Ty::Unit,
        },
        _ => Ty::Unit,
    }
}

/// Collect all local indices used (read) by an rvalue.
fn rvalue_used_locals(rvalue: &Rvalue) -> Vec<usize> {
    let mut locals = Vec::new();
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => {
            if let Some(l) = operand_local(op) {
                locals.push(l);
            }
        }
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            if let Some(l) = operand_local(lhs) {
                locals.push(l);
            }
            if let Some(l) = operand_local(rhs) {
                locals.push(l);
            }
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => {
            locals.push(place.local);
        }
        Rvalue::Aggregate(_, ops) => {
            for op in ops {
                if let Some(l) = operand_local(op) {
                    locals.push(l);
                }
            }
        }
        Rvalue::Repeat(op, _) => {
            if let Some(l) = operand_local(op) {
                locals.push(l);
            }
        }
        _ => {},
    }
    locals
}

/// Check if there's a bounds check (Assert or comparison) on a local before
/// it's used as an index.
fn has_bounds_check(func: &VerifiableFunction, local: usize) -> bool {
    for block in &func.body.blocks {
        // Check if there's an Assert that references this local
        if let Terminator::Assert { cond, .. } = &block.terminator
            && let Some(l) = operand_local(cond)
                && l == local {
                    return true;
                }

        // Check for comparison operations involving this local
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt
                && let Rvalue::BinaryOp(op, lhs, rhs) = rvalue
                    && matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) {
                        let lhs_local = operand_local(lhs);
                        let rhs_local = operand_local(rhs);
                        if lhs_local == Some(local) || rhs_local == Some(local) {
                            return true;
                        }
                    }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a function with a ptr::copy call (buffer copy pattern).
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
                    LocalDecl { index: 3, ty: Ty::usize(), name: Some("len".into()) },
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
                        span: SourceSpan::default(),
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

    /// Build a function with a format string call.
    fn format_string_function() -> VerifiableFunction {
        VerifiableFunction {
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
        }
    }

    /// Build a function with a stack-allocated array.
    fn stack_buffer_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "stack_buf".to_string(),
            def_path: "test::stack_buf".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Array { elem: Box::new(Ty::Int { width: 8, signed: false }), len: 1024 },
                        name: Some("buf".into()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Array,
                            vec![Operand::Constant(ConstValue::Uint(0, 64)); 4],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
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

    /// Build a function with a use-after-free pattern.
    fn use_after_free_function() -> VerifiableFunction {
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

    /// Build a function with a size value and bounds check.
    fn bounded_index_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "bounded_idx".to_string(),
            def_path: "test::bounded_idx".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("idx".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("len".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("check".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(3)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
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

    // ── Pattern detection tests ──

    #[test]
    fn test_detect_buffer_copy_pattern() {
        let func = buffer_copy_function();
        let patterns = detect_binary_patterns(&func);

        let copies: Vec<_> =
            patterns.iter().filter(|p| matches!(p, BinaryPattern::BufferCopy { .. })).collect();
        assert_eq!(copies.len(), 1, "should detect 1 buffer copy");

        if let BinaryPattern::BufferCopy { src_local, dst_local, size_local, block_id } = &copies[0]
        {
            assert_eq!(*src_local, 1);
            assert_eq!(*dst_local, 2);
            assert_eq!(*size_local, Some(3));
            assert_eq!(*block_id, BlockId(0));
        }
    }

    #[test]
    fn test_detect_format_string_pattern() {
        let func = format_string_function();
        let patterns = detect_binary_patterns(&func);

        let fmts: Vec<_> =
            patterns.iter().filter(|p| matches!(p, BinaryPattern::FormatString { .. })).collect();
        assert_eq!(fmts.len(), 1, "should detect 1 format string");

        if let BinaryPattern::FormatString { callee, fmt_arg_index, .. } = &fmts[0] {
            assert!(callee.contains("fmt::write"));
            assert_eq!(*fmt_arg_index, 0);
        }
    }

    #[test]
    fn test_detect_stack_buffer_pattern() {
        let func = stack_buffer_function();
        let patterns = detect_binary_patterns(&func);

        let bufs: Vec<_> =
            patterns.iter().filter(|p| matches!(p, BinaryPattern::StackBuffer { .. })).collect();
        // Should detect the aggregate + the array type
        assert!(!bufs.is_empty(), "should detect stack buffer pattern");

        // At least one should be the array aggregate
        assert!(bufs.iter().any(|p| {
            if let BinaryPattern::StackBuffer { local, .. } = p { *local == 1 } else { false }
        }));
    }

    #[test]
    fn test_detect_use_after_free_pattern() {
        let func = use_after_free_function();
        let patterns = detect_binary_patterns(&func);

        let uafs: Vec<_> =
            patterns.iter().filter(|p| matches!(p, BinaryPattern::UseAfterFree { .. })).collect();
        assert_eq!(uafs.len(), 1, "should detect 1 use-after-free");

        if let BinaryPattern::UseAfterFree { dropped_local, drop_block, use_block } = &uafs[0] {
            assert_eq!(*dropped_local, 1);
            assert_eq!(*drop_block, BlockId(0));
            assert_eq!(*use_block, BlockId(1));
        }
    }

    #[test]
    fn test_detect_no_patterns_safe_function() {
        let func = VerifiableFunction {
            name: "safe".to_string(),
            def_path: "test::safe".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
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
        };
        let patterns = detect_binary_patterns(&func);
        assert!(patterns.is_empty(), "safe function should have no binary patterns");
    }

    // ── Type recovery tests ──

    #[test]
    fn test_recover_types_buffer_pointer() {
        let func = buffer_copy_function();
        let types = recover_types(&func);

        let ptrs: Vec<_> =
            types.iter().filter(|t| matches!(t, RecoveredType::BufferPointer { .. })).collect();
        assert!(!ptrs.is_empty(), "should recover buffer pointer types");
    }

    #[test]
    fn test_recover_types_size_value() {
        let func = buffer_copy_function();
        let types = recover_types(&func);

        let sizes: Vec<_> =
            types.iter().filter(|t| matches!(t, RecoveredType::SizeValue { .. })).collect();
        assert_eq!(sizes.len(), 1, "should recover 'len' as SizeValue");

        if let RecoveredType::SizeValue { local, .. } = &sizes[0] {
            assert_eq!(*local, 3);
        }
    }

    #[test]
    fn test_recover_types_array_like() {
        let func = stack_buffer_function();
        let types = recover_types(&func);

        let arrays: Vec<_> =
            types.iter().filter(|t| matches!(t, RecoveredType::ArrayLike { .. })).collect();
        assert_eq!(arrays.len(), 1, "should recover array type");

        if let RecoveredType::ArrayLike { local, length, .. } = &arrays[0] {
            assert_eq!(*local, 1);
            assert_eq!(*length, Some(1024));
        }
    }

    #[test]
    fn test_recover_types_bounded_index() {
        let func = bounded_index_function();
        let types = recover_types(&func);

        // "idx" should be recovered as SizeValue with bounds_checked = true
        let idx_types: Vec<_> = types
            .iter()
            .filter(|t| matches!(t, RecoveredType::SizeValue { local: 1, .. }))
            .collect();
        assert_eq!(idx_types.len(), 1);

        if let RecoveredType::SizeValue { bounds_checked, .. } = &idx_types[0] {
            assert!(*bounds_checked, "idx should be detected as bounds-checked");
        }

        // "len" should also be a SizeValue
        let len_types: Vec<_> = types
            .iter()
            .filter(|t| matches!(t, RecoveredType::SizeValue { local: 2, .. }))
            .collect();
        assert_eq!(len_types.len(), 1);
    }

    // ── Description and serialization tests ──

    #[test]
    fn test_binary_pattern_descriptions() {
        let patterns = vec![
            BinaryPattern::BufferCopy {
                src_local: 1,
                dst_local: 2,
                size_local: Some(3),
                block_id: BlockId(0),
            },
            BinaryPattern::FormatString {
                callee: "printf".into(),
                fmt_arg_index: 0,
                block_id: BlockId(0),
            },
            BinaryPattern::IndirectCall { fn_ptr_local: 5, block_id: BlockId(0) },
            BinaryPattern::StackBuffer {
                local: 1,
                elem_ty: Ty::Int { width: 8, signed: false },
                length: 256,
                block_id: BlockId(0),
            },
            BinaryPattern::UncheckedSizeUse {
                size_local: 3,
                use_block: BlockId(1),
                use_kind: SizeUseKind::AllocationSize,
            },
            BinaryPattern::UseAfterFree {
                dropped_local: 2,
                drop_block: BlockId(0),
                use_block: BlockId(1),
            },
        ];

        for p in &patterns {
            let desc = p.description();
            assert!(!desc.is_empty(), "description should not be empty");
        }

        assert!(patterns[0].description().contains("buffer copy"));
        assert!(patterns[1].description().contains("format string"));
        assert!(patterns[2].description().contains("indirect call"));
        assert!(patterns[3].description().contains("stack buffer"));
        assert!(patterns[4].description().contains("unchecked size"));
        assert!(patterns[5].description().contains("use after free"));
    }

    #[test]
    fn test_binary_pattern_serialization_roundtrip() {
        let pattern = BinaryPattern::BufferCopy {
            src_local: 1,
            dst_local: 2,
            size_local: Some(3),
            block_id: BlockId(0),
        };
        let json = serde_json::to_string(&pattern).expect("serialize");
        let round: BinaryPattern = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, pattern);
    }

    #[test]
    fn test_recovered_type_serialization_roundtrip() {
        let rt =
            RecoveredType::BufferPointer { local: 1, elem_size: Some(4), buffer_len: Some(256) };
        let json = serde_json::to_string(&rt).expect("serialize");
        let round: RecoveredType = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, rt);
    }

    #[test]
    fn test_recovered_type_local() {
        let types = [
            RecoveredType::BufferPointer { local: 1, elem_size: None, buffer_len: None },
            RecoveredType::ArrayLike { local: 2, elem_ty: Ty::u32(), length: Some(10) },
            RecoveredType::SizeValue { local: 3, bounds_checked: false },
            RecoveredType::FunctionPointer { local: 4, known_target: None },
            RecoveredType::StringValue { local: 5, tainted: true },
        ];

        for (i, t) in types.iter().enumerate() {
            assert_eq!(t.local(), i + 1);
        }
    }

    #[test]
    fn test_binary_pattern_block_id() {
        let p = BinaryPattern::BufferCopy {
            src_local: 0,
            dst_local: 1,
            size_local: None,
            block_id: BlockId(7),
        };
        assert_eq!(p.block_id(), BlockId(7));
    }

    #[test]
    fn test_size_use_kind_variants() {
        let kinds = vec![
            SizeUseKind::Index,
            SizeUseKind::AllocationSize,
            SizeUseKind::CopyLength,
            SizeUseKind::LoopBound,
        ];
        for kind in kinds {
            let json = serde_json::to_string(&kind).expect("serialize");
            let round: SizeUseKind = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(round, kind);
        }
    }
}
