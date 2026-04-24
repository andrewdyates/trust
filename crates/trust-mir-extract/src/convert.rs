// trust-mir-extract/convert.rs: Convert MIR structures to trust-types
//
// Handles: BasicBlock, Statement, Terminator, Rvalue, Operand, Place, BinOp
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;
use trust_types::*;

use crate::ty_convert;

/// Convert a rustc BasicBlock to our BasicBlock.
pub(crate) fn convert_basic_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    bb: mir::BasicBlock,
    bb_data: &mir::BasicBlockData<'tcx>,
) -> BasicBlock {
    let stmts: Vec<Statement> =
        bb_data.statements.iter().filter_map(|stmt| convert_statement(tcx, stmt)).collect();

    let terminator = convert_terminator(tcx, bb_data.terminator());

    BasicBlock { id: BlockId(bb.as_usize()), stmts, terminator }
}

/// Convert a rustc Statement. Returns None for statements we don't track.
fn convert_statement<'tcx>(tcx: TyCtxt<'tcx>, stmt: &mir::Statement<'tcx>) -> Option<Statement> {
    match &stmt.kind {
        mir::StatementKind::Assign(box (place, rvalue)) => Some(Statement::Assign {
            place: convert_place(place),
            rvalue: convert_rvalue(tcx, rvalue),
            span: convert_span(tcx, stmt.source_info.span), // tRust: per-statement source span
        }),
        // Skip storage markers, fake reads, retags, etc.
        _ => None,
    }
}

/// Convert a rustc Terminator to our Terminator.
fn convert_terminator<'tcx>(tcx: TyCtxt<'tcx>, terminator: &mir::Terminator<'tcx>) -> Terminator {
    // tRust: extract per-terminator source span for diagnostics
    let span = convert_span(tcx, terminator.source_info.span);
    match &terminator.kind {
        mir::TerminatorKind::Goto { target } => Terminator::Goto(BlockId(target.as_usize())),
        mir::TerminatorKind::SwitchInt { discr, targets } => {
            let switch_targets: Vec<(u128, BlockId)> =
                targets.iter().map(|(val, bb)| (val, BlockId(bb.as_usize()))).collect();
            let otherwise = BlockId(targets.otherwise().as_usize());

            Terminator::SwitchInt {
                discr: convert_operand(tcx, discr),
                targets: switch_targets,
                otherwise,
                span, // tRust: per-terminator source span
            }
        }
        mir::TerminatorKind::Return => Terminator::Return,
        mir::TerminatorKind::Unreachable => Terminator::Unreachable,
        mir::TerminatorKind::Call { func, args, destination, target, .. } => {
            let func_name = func_operand_name(tcx, func);
            let converted_args: Vec<Operand> =
                args.iter().map(|spanned| convert_operand(tcx, &spanned.node)).collect();
            let dest = convert_place(destination);

            // tRust #605: Detect atomic intrinsics and populate atomic metadata.
            let atomic = parse_atomic_intrinsic(&func_name, &converted_args, &dest, &span);

            Terminator::Call {
                func: func_name,
                args: converted_args,
                dest,
                target: target.map(|bb| BlockId(bb.as_usize())),
                span, // tRust: per-terminator source span
                atomic,
            }
        }
        // tRust: CRITICAL — Assert terminators encode rustc's overflow checks,
        // bounds checks, and div-by-zero checks.
        mir::TerminatorKind::Assert { cond, expected, msg, target, .. } => Terminator::Assert {
            cond: convert_operand(tcx, cond),
            expected: *expected,
            msg: convert_assert_message(tcx, msg),
            target: BlockId(target.as_usize()),
            span, // tRust: per-terminator source span
        },
        mir::TerminatorKind::Drop { place, target, .. } => Terminator::Drop {
            place: convert_place(place),
            target: BlockId(target.as_usize()),
            span, // tRust: per-terminator source span
        },
        // tRust: Map unsupported terminators (Yield, InlineAsm, CoroutineDrop,
        // Resume, UnwindResume, UnwindTerminate, FalseEdge, FalseUnwind) to
        // Unreachable rather than Goto(0), which would corrupt the CFG by
        // creating a false edge to the entry block. (#398)
        _ => Terminator::Unreachable,
    }
}

// tRust #605: Atomic intrinsic detection
// ---------------------------------------------------------------------------

/// Parse a MIR function call name to detect atomic intrinsics.
///
/// Handles two forms of atomic intrinsic calls in optimized MIR:
///
/// **Form A** (suffix-encoded ordering):
///   `core::intrinsics::atomic_load_seqcst(ptr)`
///   `core::intrinsics::atomic_cxchg_acqrel_acquire(ptr, old, new)`
///
/// **Form B** (generic atomic calls with explicit Ordering argument):
///   `atomic::atomic_load::<usize>(ptr, Ordering::Acquire)`
///
/// Returns `Some(AtomicOperation)` if the call is a recognized atomic intrinsic,
/// `None` otherwise.
pub(crate) fn parse_atomic_intrinsic(
    func_name: &str,
    args: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> Option<AtomicOperation> {
    // Form A: core::intrinsics::atomic_*
    if let Some(suffix) = func_name.strip_prefix("core::intrinsics::atomic_") {
        return parse_form_a(suffix, args, dest, span);
    }

    // Form B: contains "atomic::atomic_" — generic atomic calls
    if let Some(idx) = func_name.find("atomic::atomic_") {
        let after = &func_name[idx + "atomic::atomic_".len()..];
        // Strip generic suffix like "::<usize>"
        let op_name = after.split("::").next().unwrap_or(after);
        return parse_form_b(op_name, args, dest, span);
    }

    // Also handle bare "fence" or "atomic::fence" / "compiler_fence"
    if func_name.ends_with("::fence") || func_name == "fence" {
        return Some(AtomicOperation {
            place: Place::local(0),
            dest: None,
            op_kind: AtomicOpKind::Fence,
            ordering: ordering_from_args(args, 0).unwrap_or(AtomicOrdering::SeqCst),
            failure_ordering: None,
            span: span.clone(),
        });
    }
    if func_name.ends_with("::compiler_fence") || func_name == "compiler_fence" {
        return Some(AtomicOperation {
            place: Place::local(0),
            dest: None,
            op_kind: AtomicOpKind::CompilerFence,
            ordering: ordering_from_args(args, 0).unwrap_or(AtomicOrdering::SeqCst),
            failure_ordering: None,
            span: span.clone(),
        });
    }

    None
}

/// Parse Form A intrinsic: the part after "core::intrinsics::atomic_".
///
/// Patterns: `load_{ordering}`, `store_{ordering}`, `cxchg_{s}_{f}`,
/// `cxchgweak_{s}_{f}`, `xchg_{ordering}`, `fence_{ordering}`,
/// `singlethreadfence_{ordering}`, `xadd_{ordering}`, `xsub_{ordering}`,
/// `and_{ordering}`, `or_{ordering}`, `xor_{ordering}`, `nand_{ordering}`,
/// `min_{ordering}`, `max_{ordering}`, `umin_{ordering}`, `umax_{ordering}`.
fn parse_form_a(
    suffix: &str,
    args: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> Option<AtomicOperation> {
    // Try each operation prefix, longest-first to avoid ambiguity.
    let ops: &[(&str, AtomicOpKind, bool)] = &[
        ("cxchgweak_", AtomicOpKind::CompareExchangeWeak, true),
        ("cxchg_", AtomicOpKind::CompareExchange, true),
        ("singlethreadfence_", AtomicOpKind::CompilerFence, false),
        ("fence_", AtomicOpKind::Fence, false),
        ("load_", AtomicOpKind::Load, false),
        ("store_", AtomicOpKind::Store, false),
        ("xchg_", AtomicOpKind::Exchange, false),
        ("xadd_", AtomicOpKind::FetchAdd, false),
        ("xsub_", AtomicOpKind::FetchSub, false),
        ("nand_", AtomicOpKind::FetchNand, false),
        ("umin_", AtomicOpKind::FetchMin, false),
        ("umax_", AtomicOpKind::FetchMax, false),
        ("and_", AtomicOpKind::FetchAnd, false),
        ("or_", AtomicOpKind::FetchOr, false),
        ("xor_", AtomicOpKind::FetchXor, false),
        ("min_", AtomicOpKind::FetchMin, false),
        ("max_", AtomicOpKind::FetchMax, false),
    ];

    for &(prefix, op_kind, is_cas) in ops {
        if let Some(ordering_part) = suffix.strip_prefix(prefix) {
            let place = extract_place_from_args(args, op_kind);
            let has_dest = !op_kind.is_store() && !op_kind.is_fence();

            if is_cas {
                // CAS: ordering_part is "success_failure" e.g. "acqrel_acquire"
                let (success, failure) = parse_cas_orderings(ordering_part)?;
                return Some(AtomicOperation {
                    place,
                    dest: if has_dest { Some(dest.clone()) } else { None },
                    op_kind,
                    ordering: success,
                    failure_ordering: Some(failure),
                    span: span.clone(),
                });
            } else {
                let ordering = parse_ordering(ordering_part)?;
                return Some(AtomicOperation {
                    place,
                    dest: if has_dest { Some(dest.clone()) } else { None },
                    op_kind,
                    ordering,
                    failure_ordering: None,
                    span: span.clone(),
                });
            }
        }
    }

    None
}

/// Parse Form B intrinsic: the operation name extracted from the function path.
/// Ordering comes from function arguments (const Ordering operand).
fn parse_form_b(
    op_name: &str,
    args: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> Option<AtomicOperation> {
    let (op_kind, is_cas) = match op_name {
        "load" => (AtomicOpKind::Load, false),
        "store" => (AtomicOpKind::Store, false),
        "exchange" | "swap" => (AtomicOpKind::Exchange, false),
        "compare_exchange" | "cxchg" => (AtomicOpKind::CompareExchange, true),
        "compare_exchange_weak" | "cxchgweak" => (AtomicOpKind::CompareExchangeWeak, true),
        "fetch_add" | "xadd" => (AtomicOpKind::FetchAdd, false),
        "fetch_sub" | "xsub" => (AtomicOpKind::FetchSub, false),
        "fetch_and" => (AtomicOpKind::FetchAnd, false),
        "fetch_or" => (AtomicOpKind::FetchOr, false),
        "fetch_xor" => (AtomicOpKind::FetchXor, false),
        "fetch_nand" => (AtomicOpKind::FetchNand, false),
        "fetch_min" => (AtomicOpKind::FetchMin, false),
        "fetch_max" => (AtomicOpKind::FetchMax, false),
        "fence" => (AtomicOpKind::Fence, false),
        "compiler_fence" | "singlethreadfence" => (AtomicOpKind::CompilerFence, false),
        _ => return None,
    };

    let place = extract_place_from_args(args, op_kind);
    let has_dest = !op_kind.is_store() && !op_kind.is_fence();

    // For Form B, ordering is in the arguments. Ordering arg positions vary:
    // load(ptr, ordering) -> ordering at index 1
    // store(ptr, val, ordering) -> ordering at index 2
    // CAS(ptr, old, new, success_ord, failure_ord) -> indices 3, 4
    // fetch_*(ptr, val, ordering) -> ordering at index 2
    // fence(ordering) -> ordering at index 0
    if is_cas {
        let success = ordering_from_args(args, 3).unwrap_or(AtomicOrdering::SeqCst);
        let failure = ordering_from_args(args, 4).unwrap_or(AtomicOrdering::Relaxed);
        Some(AtomicOperation {
            place,
            dest: if has_dest { Some(dest.clone()) } else { None },
            op_kind,
            ordering: success,
            failure_ordering: Some(failure),
            span: span.clone(),
        })
    } else {
        let ord_idx = match op_kind {
            AtomicOpKind::Fence | AtomicOpKind::CompilerFence => 0,
            AtomicOpKind::Load => 1,
            _ => 2, // store, exchange, fetch_*
        };
        let ordering = ordering_from_args(args, ord_idx).unwrap_or(AtomicOrdering::SeqCst);
        Some(AtomicOperation {
            place,
            dest: if has_dest { Some(dest.clone()) } else { None },
            op_kind,
            ordering,
            failure_ordering: None,
            span: span.clone(),
        })
    }
}

/// Parse an ordering string from an intrinsic name suffix.
fn parse_ordering(s: &str) -> Option<AtomicOrdering> {
    match s {
        "relaxed" => Some(AtomicOrdering::Relaxed),
        "acquire" | "consume" => Some(AtomicOrdering::Acquire), // Consume maps to Acquire
        "release" => Some(AtomicOrdering::Release),
        "acqrel" => Some(AtomicOrdering::AcqRel),
        "seqcst" => Some(AtomicOrdering::SeqCst),
        _ => None,
    }
}

/// Parse CAS dual ordering from suffix like "acqrel_acquire" or "seqcst_seqcst".
fn parse_cas_orderings(s: &str) -> Option<(AtomicOrdering, AtomicOrdering)> {
    // Try each known ordering as the success prefix (longest first to avoid ambiguity).
    let orderings = ["seqcst", "acqrel", "acquire", "release", "relaxed", "consume"];
    for &success_str in &orderings {
        if let Some(rest) = s.strip_prefix(success_str) {
            if let Some(failure_str) = rest.strip_prefix('_') {
                let success = parse_ordering(success_str)?;
                let failure = parse_ordering(failure_str)?;
                return Some((success, failure));
            }
        }
    }
    None
}

/// Extract the accessed place from call arguments.
///
/// For non-fence operations, the first argument is a raw pointer to the
/// atomic location. We extract the Place from the operand. For fence
/// operations, there is no memory location — use a synthetic Place::local(0).
fn extract_place_from_args(args: &[Operand], op_kind: AtomicOpKind) -> Place {
    if op_kind.is_fence() {
        return Place::local(0);
    }
    args.first()
        .and_then(|arg| match arg {
            Operand::Copy(p) | Operand::Move(p) => Some(p.clone()),
            _ => None,
        })
        .unwrap_or_else(|| Place::local(0))
}

/// Try to extract an ordering from a const argument at the given index.
///
/// In Form B intrinsics, ordering is passed as an explicit `Ordering` enum
/// argument. We look for uint constants that map to the discriminant values
/// of `std::sync::atomic::Ordering`.
fn ordering_from_args(_args: &[Operand], _index: usize) -> Option<AtomicOrdering> {
    // In optimized MIR, Ordering enum variants are lowered to integer constants.
    // The discriminant values are: Relaxed=0, Release=1, Acquire=2, AcqRel=3, SeqCst=4
    // However, extracting these reliably requires const evaluation context.
    // For now, Form B relies on name parsing when possible; this function serves
    // as a hook for future const-operand extraction.
    None
}

// ---------------------------------------------------------------------------

/// Convert a rustc Rvalue.
fn convert_rvalue<'tcx>(tcx: TyCtxt<'tcx>, rvalue: &mir::Rvalue<'tcx>) -> Rvalue {
    match rvalue {
        mir::Rvalue::Use(mir::Operand::Constant(box const_op)) => {
            convert_const_aggregate_rvalue(tcx, const_op)
                .unwrap_or_else(|| Rvalue::Use(convert_const_operand(tcx, const_op)))
        }
        mir::Rvalue::Use(op) => Rvalue::Use(convert_operand(tcx, op)),

        mir::Rvalue::BinaryOp(bin_op, box (lhs, rhs)) => {
            let (our_op, checked) = convert_binop(*bin_op);
            let l = convert_operand(tcx, lhs);
            let r = convert_operand(tcx, rhs);

            if checked {
                Rvalue::CheckedBinaryOp(our_op, l, r)
            } else {
                Rvalue::BinaryOp(our_op, l, r)
            }
        }

        mir::Rvalue::UnaryOp(un_op, operand) => {
            let op = match un_op {
                mir::UnOp::Not => UnOp::Not,
                mir::UnOp::Neg => UnOp::Neg,
                // tRust: #386 — map PtrMetadata to its own variant instead
                // of incorrectly falling back to Not.
                mir::UnOp::PtrMetadata => UnOp::PtrMetadata,
            };
            Rvalue::UnaryOp(op, convert_operand(tcx, operand))
        }

        mir::Rvalue::Ref(_, borrow_kind, place) => {
            let mutable = matches!(borrow_kind, mir::BorrowKind::Mut { .. });
            Rvalue::Ref { mutable, place: convert_place(place) }
        }

        mir::Rvalue::Cast(_, operand, ty) => {
            Rvalue::Cast(convert_operand(tcx, operand), ty_convert::convert_ty(tcx, *ty))
        }

        mir::Rvalue::Aggregate(box mir::AggregateKind::Tuple, operands) if operands.is_empty() => {
            // Native MIR spells `()` as an empty tuple aggregate in some paths.
            // Canonicalize it to a unit constant so downstream lowering does not
            // materialize an uninitialized zero-field aggregate.
            Rvalue::Use(Operand::Constant(ConstValue::Unit))
        }

        mir::Rvalue::Aggregate(box agg_kind, operands) => {
            let kind = match agg_kind {
                mir::AggregateKind::Tuple => AggregateKind::Tuple,
                mir::AggregateKind::Array(_) => AggregateKind::Array,
                mir::AggregateKind::Adt(def_id, variant_idx, _, _, _) => AggregateKind::Adt {
                    name: crate::safe_def_path_str(tcx, *def_id),
                    variant: variant_idx.as_usize(),
                },
                _ => AggregateKind::Tuple,
            };
            let ops: Vec<Operand> = operands.iter().map(|op| convert_operand(tcx, op)).collect();
            Rvalue::Aggregate(kind, ops)
        }

        mir::Rvalue::Discriminant(place) => Rvalue::Discriminant(convert_place(place)),

        mir::Rvalue::Repeat(operand, count) => {
            // count is a ty::Const; extract the usize value or default to 0.
            let n = count.try_to_target_usize(tcx).map(|v| v as usize).unwrap_or(0);
            Rvalue::Repeat(convert_operand(tcx, operand), n)
        }

        mir::Rvalue::RawPtr(ptr_kind, place) => {
            let mutable = match ptr_kind {
                mir::RawPtrKind::Mut => true,
                mir::RawPtrKind::Const => false,
                mir::RawPtrKind::FakeForPtrMetadata => {
                    panic!(
                        "trust-mir-extract does not support RawPtrKind::FakeForPtrMetadata: {rvalue:?}"
                    )
                }
            };
            Rvalue::AddressOf(mutable, convert_place(place))
        }

        mir::Rvalue::CopyForDeref(place) => Rvalue::CopyForDeref(convert_place(place)),

        _ => panic!("trust-mir-extract does not support MIR rvalue: {rvalue:?}"),
    }
}

/// Convert a rustc BinOp. Returns (our BinOp, is_checked).
///
/// In current rustc, checked operations are BinOp variants like AddWithOverflow.
fn convert_binop(op: mir::BinOp) -> (BinOp, bool) {
    match op {
        mir::BinOp::Add => (BinOp::Add, false),
        mir::BinOp::AddUnchecked => (BinOp::Add, false),
        mir::BinOp::AddWithOverflow => (BinOp::Add, true),
        mir::BinOp::Sub => (BinOp::Sub, false),
        mir::BinOp::SubUnchecked => (BinOp::Sub, false),
        mir::BinOp::SubWithOverflow => (BinOp::Sub, true),
        mir::BinOp::Mul => (BinOp::Mul, false),
        mir::BinOp::MulUnchecked => (BinOp::Mul, false),
        mir::BinOp::MulWithOverflow => (BinOp::Mul, true),
        mir::BinOp::Div => (BinOp::Div, false),
        mir::BinOp::Rem => (BinOp::Rem, false),
        mir::BinOp::BitXor => (BinOp::BitXor, false),
        mir::BinOp::BitAnd => (BinOp::BitAnd, false),
        mir::BinOp::BitOr => (BinOp::BitOr, false),
        mir::BinOp::Shl => (BinOp::Shl, false),
        mir::BinOp::ShlUnchecked => (BinOp::Shl, false),
        mir::BinOp::Shr => (BinOp::Shr, false),
        mir::BinOp::ShrUnchecked => (BinOp::Shr, false),
        mir::BinOp::Eq => (BinOp::Eq, false),
        mir::BinOp::Lt => (BinOp::Lt, false),
        mir::BinOp::Le => (BinOp::Le, false),
        mir::BinOp::Ne => (BinOp::Ne, false),
        mir::BinOp::Ge => (BinOp::Ge, false),
        mir::BinOp::Gt => (BinOp::Gt, false),
        // tRust #383: Three-way comparison returns -1/0/1, not a boolean.
        mir::BinOp::Cmp => (BinOp::Cmp, false),
        mir::BinOp::Offset => (BinOp::Add, false),
    }
}

/// Convert a rustc Operand.
///
/// tRust: Exhaustive match — no wildcard fallback. If rustc adds new Operand
/// variants, this will fail to compile, which is the correct behavior (#409).
fn convert_operand<'tcx>(tcx: TyCtxt<'tcx>, operand: &mir::Operand<'tcx>) -> Operand {
    match operand {
        mir::Operand::Copy(place) => Operand::Copy(convert_place(place)),
        mir::Operand::Move(place) => Operand::Move(convert_place(place)),
        mir::Operand::Constant(box const_op) => convert_const_operand(tcx, const_op),
        mir::Operand::RuntimeChecks(check) => {
            Operand::Constant(ConstValue::Bool(check.value(tcx.sess)))
        }
    }
}

/// Convert a rustc ConstOperand to our Operand.
fn convert_const_operand<'tcx>(tcx: TyCtxt<'tcx>, const_op: &mir::ConstOperand<'tcx>) -> Operand {
    use rustc_middle::ty::TyKind;

    let c = const_op.const_;
    let ty = c.ty();

    // Type-directed constant extraction (check type FIRST to avoid panics)
    match ty.kind() {
        TyKind::Bool => {
            if let Some(b) = c.try_to_bool() {
                return Operand::Constant(ConstValue::Bool(b));
            }
        }
        TyKind::Char => {
            let size = rustc_abi::Size::from_bits(32);
            if let Some(bits) = c.try_to_bits(size) {
                return Operand::Constant(ConstValue::Uint(bits, 32));
            }
        }
        TyKind::Int(int_ty) => {
            let width = crate::ty_convert::int_width_from_int_ty(int_ty, tcx);
            let size = rustc_abi::Size::from_bits(width as u64);
            if let Some(bits) = c.try_to_bits(size) {
                // Sign-extend the bits to i128
                let val = rustc_abi::Size::from_bits(width as u64).sign_extend(bits) as i128;
                return Operand::Constant(ConstValue::Int(val));
            }
        }
        TyKind::Uint(uint_ty) => {
            let width = crate::ty_convert::uint_width_from_uint_ty(uint_ty, tcx);
            let size = rustc_abi::Size::from_bits(width as u64);
            if let Some(bits) = c.try_to_bits(size) {
                return Operand::Constant(ConstValue::Uint(bits, width));
            }
        }
        // tRust: Extract float constants from MIR (#406). Float bits are
        // IEEE 754; convert via f32/f64 from_bits to get the actual value.
        TyKind::Float(float_ty) => {
            let width: u32 = match float_ty {
                rustc_ast_ir::FloatTy::F16 => 16,
                rustc_ast_ir::FloatTy::F32 => 32,
                rustc_ast_ir::FloatTy::F64 => 64,
                rustc_ast_ir::FloatTy::F128 => 128,
            };
            let size = rustc_abi::Size::from_bits(width as u64);
            if let Some(bits) = c.try_to_bits(size) {
                let val = match width {
                    32 => f32::from_bits(bits as u32) as f64,
                    _ => f64::from_bits(bits as u64),
                };
                return Operand::Constant(ConstValue::Float(val));
            }
        }
        _ => {}
    }

    if let Some(value) = const_operand_value(tcx, const_op) {
        let ty_const = ty::Const::new_value(tcx, value.valtree, value.ty);
        if let Some(operand) = convert_ty_const_to_operand(tcx, ty_const) {
            return operand;
        }
    }

    // Unit type
    if ty.is_unit() {
        return Operand::Constant(ConstValue::Unit);
    }

    Operand::Constant(ConstValue::Unit)
}

/// Reconstruct aggregate constants that optimized MIR collapses into
/// `Rvalue::Use(const ...)` so downstream passes still see tuple/ADT structure.
fn convert_const_aggregate_rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    const_op: &mir::ConstOperand<'tcx>,
) -> Option<Rvalue> {
    if let mir::Const::Val(value, ty) = const_op.const_ {
        if let Some(rvalue) = convert_mir_const_value_aggregate_rvalue(tcx, value, ty) {
            return Some(rvalue);
        }
    }

    let value = const_operand_value(tcx, const_op)?;

    match value.ty.kind() {
        ty::TyKind::Tuple(fields) => {
            if fields.is_empty() {
                return Some(Rvalue::Use(Operand::Constant(ConstValue::Unit)));
            }
            let ops = value
                .try_to_branch()?
                .iter()
                .map(|field| convert_ty_const_to_operand(tcx, *field))
                .collect::<Option<Vec<_>>>()?;
            Some(Rvalue::Aggregate(AggregateKind::Tuple, ops))
        }
        ty::TyKind::Array(_, _) => {
            let ops = value
                .try_to_branch()?
                .iter()
                .map(|field| convert_ty_const_to_operand(tcx, *field))
                .collect::<Option<Vec<_>>>()?;
            Some(Rvalue::Aggregate(AggregateKind::Array, ops))
        }
        ty::TyKind::Adt(adt_def, _) => {
            let destructured = value.destructure_adt_const();
            let ops = destructured
                .fields
                .iter()
                .map(|field| convert_ty_const_to_operand(tcx, *field))
                .collect::<Option<Vec<_>>>()?;
            Some(Rvalue::Aggregate(
                AggregateKind::Adt {
                    name: crate::safe_def_path_str(tcx, adt_def.did()),
                    variant: destructured.variant.as_usize(),
                },
                ops,
            ))
        }
        _ => None,
    }
}

/// Reconstruct one-level tuple/ADT constants materialized as `mir::Const::Val`.
///
/// Field operands still have to be scalar or unit; nested aggregate fields remain
/// unsupported because `trust-types::Operand` cannot encode them losslessly.
fn convert_mir_const_value_aggregate_rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: mir::ConstValue,
    ty: ty::Ty<'tcx>,
) -> Option<Rvalue> {
    if ty.has_non_region_param() {
        return None;
    }

    let contents = tcx.try_destructure_mir_constant_for_user_output(value, ty)?;
    let ops = contents
        .fields
        .iter()
        .map(|(field_value, field_ty)| {
            convert_mir_const_value_to_operand(tcx, *field_value, *field_ty)
        })
        .collect::<Option<Vec<_>>>()?;

    match ty.kind() {
        ty::TyKind::Tuple(fields) => {
            if fields.is_empty() {
                return Some(Rvalue::Use(Operand::Constant(ConstValue::Unit)));
            }
            Some(Rvalue::Aggregate(AggregateKind::Tuple, ops))
        }
        ty::TyKind::Adt(adt_def, _) => Some(Rvalue::Aggregate(
            AggregateKind::Adt {
                name: crate::safe_def_path_str(tcx, adt_def.did()),
                variant: contents.variant?.as_usize(),
            },
            ops,
        )),
        _ => None,
    }
}

fn const_operand_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    const_op: &mir::ConstOperand<'tcx>,
) -> Option<ty::Value<'tcx>> {
    match const_op.const_ {
        mir::Const::Ty(_, ty_const) => ty_const.try_to_value(),
        mir::Const::Unevaluated(unevaluated, ty) => {
            let typing_env = ty::TypingEnv::fully_monomorphized();
            let instance =
                ty::Instance::try_resolve(tcx, typing_env, unevaluated.def, unevaluated.args)
                    .ok()
                    .flatten()?;
            let valtree = tcx
                .const_eval_global_id_for_typeck(
                    typing_env,
                    rustc_middle::mir::interpret::GlobalId {
                        instance,
                        promoted: unevaluated.promoted,
                    },
                    const_op.span,
                )
                .ok()?
                .ok()?;
            Some(ty::Value { ty, valtree })
        }
        mir::Const::Val(_, _) => None,
    }
}

fn convert_mir_const_value_to_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: mir::ConstValue,
    ty: ty::Ty<'tcx>,
) -> Option<Operand> {
    use rustc_middle::ty::TyKind;

    match ty.kind() {
        TyKind::Bool => Some(Operand::Constant(ConstValue::Bool(value.try_to_bool()?))),
        TyKind::Char => Some(Operand::Constant(ConstValue::Uint(
            value.try_to_bits_for_ty(tcx, ty::TypingEnv::fully_monomorphized(), ty)?,
            32,
        ))),
        TyKind::Int(int_ty) => {
            let width = crate::ty_convert::int_width_from_int_ty(int_ty, tcx);
            let bits = value.try_to_bits_for_ty(tcx, ty::TypingEnv::fully_monomorphized(), ty)?;
            let val = rustc_abi::Size::from_bits(width as u64).sign_extend(bits) as i128;
            Some(Operand::Constant(ConstValue::Int(val)))
        }
        TyKind::Uint(uint_ty) => {
            let width = crate::ty_convert::uint_width_from_uint_ty(uint_ty, tcx);
            let bits = value.try_to_bits_for_ty(tcx, ty::TypingEnv::fully_monomorphized(), ty)?;
            Some(Operand::Constant(ConstValue::Uint(bits, width)))
        }
        TyKind::Float(float_ty) => {
            let width: u32 = match float_ty {
                rustc_ast_ir::FloatTy::F16 => 16,
                rustc_ast_ir::FloatTy::F32 => 32,
                rustc_ast_ir::FloatTy::F64 => 64,
                rustc_ast_ir::FloatTy::F128 => 128,
            };
            let bits = value.try_to_bits_for_ty(tcx, ty::TypingEnv::fully_monomorphized(), ty)?;
            let val = match width {
                32 => f32::from_bits(bits as u32) as f64,
                _ => f64::from_bits(bits as u64),
            };
            Some(Operand::Constant(ConstValue::Float(val)))
        }
        _ if ty.is_unit() => Some(Operand::Constant(ConstValue::Unit)),
        _ => None,
    }
}

fn convert_ty_const_to_operand<'tcx>(tcx: TyCtxt<'tcx>, c: ty::Const<'tcx>) -> Option<Operand> {
    use rustc_middle::ty::TyKind;

    let value = c.try_to_value()?;
    let ty = value.ty;
    let typing_env = ty::TypingEnv::fully_monomorphized();

    match ty.kind() {
        TyKind::Bool => {
            return Some(Operand::Constant(ConstValue::Bool(value.try_to_bool()?)));
        }
        TyKind::Char => {
            let bits = value.try_to_bits(tcx, typing_env)?;
            return Some(Operand::Constant(ConstValue::Uint(bits, 32)));
        }
        TyKind::Int(int_ty) => {
            let width = crate::ty_convert::int_width_from_int_ty(int_ty, tcx);
            let bits = value.try_to_bits(tcx, typing_env)?;
            let val = rustc_abi::Size::from_bits(width as u64).sign_extend(bits) as i128;
            return Some(Operand::Constant(ConstValue::Int(val)));
        }
        TyKind::Uint(uint_ty) => {
            let width = crate::ty_convert::uint_width_from_uint_ty(uint_ty, tcx);
            let bits = value.try_to_bits(tcx, typing_env)?;
            return Some(Operand::Constant(ConstValue::Uint(bits, width)));
        }
        TyKind::Float(float_ty) => {
            let width: u32 = match float_ty {
                rustc_ast_ir::FloatTy::F16 => 16,
                rustc_ast_ir::FloatTy::F32 => 32,
                rustc_ast_ir::FloatTy::F64 => 64,
                rustc_ast_ir::FloatTy::F128 => 128,
            };
            let bits = value.try_to_bits(tcx, typing_env)?;
            let val = match width {
                32 => f32::from_bits(bits as u32) as f64,
                _ => f64::from_bits(bits as u64),
            };
            return Some(Operand::Constant(ConstValue::Float(val)));
        }
        _ => {}
    }

    if ty.is_unit() { Some(Operand::Constant(ConstValue::Unit)) } else { None }
}

/// Convert a rustc Place to our Place.
fn convert_place(place: &mir::Place<'_>) -> Place {
    let projections: Vec<Projection> = place
        .projection
        .iter()
        .filter_map(|elem| match elem {
            mir::PlaceElem::Field(field, _) => Some(Projection::Field(field.as_usize())),
            mir::PlaceElem::Index(local) => Some(Projection::Index(local.as_usize())),
            mir::PlaceElem::Deref => Some(Projection::Deref),
            mir::PlaceElem::Downcast(_, variant) => Some(Projection::Downcast(variant.as_usize())),
            mir::PlaceElem::ConstantIndex { offset, from_end, .. } => {
                Some(Projection::ConstantIndex { offset: offset as usize, from_end })
            }
            mir::PlaceElem::Subslice { from, to, from_end } => {
                Some(Projection::Subslice { from: from as usize, to: to as usize, from_end })
            }
            _ => None,
        })
        .collect();

    Place { local: place.local.as_usize(), projections }
}

/// Convert an AssertKind to our AssertMessage.
fn convert_assert_message<'tcx>(
    _tcx: TyCtxt<'tcx>,
    msg: &mir::AssertKind<mir::Operand<'tcx>>,
) -> AssertMessage {
    match msg {
        mir::AssertKind::BoundsCheck { .. } => AssertMessage::BoundsCheck,
        mir::AssertKind::Overflow(bin_op, _, _) => {
            let (our_op, _) = convert_binop(*bin_op);
            AssertMessage::Overflow(our_op)
        }
        mir::AssertKind::OverflowNeg(_) => AssertMessage::OverflowNeg,
        mir::AssertKind::DivisionByZero(_) => AssertMessage::DivisionByZero,
        mir::AssertKind::RemainderByZero(_) => AssertMessage::RemainderByZero,
        mir::AssertKind::ResumedAfterReturn(_) => AssertMessage::ResumedAfterReturn,
        mir::AssertKind::ResumedAfterPanic(_) => AssertMessage::ResumedAfterPanic,
        mir::AssertKind::MisalignedPointerDereference { .. } => {
            AssertMessage::MisalignedPointerDereference
        }
        // tRust: #413 — map new rustc AssertKind variants to specific AssertMessage variants
        // instead of falling through to the wildcard Custom arm.
        mir::AssertKind::ResumedAfterDrop(_) => AssertMessage::ResumedAfterDrop,
        mir::AssertKind::NullPointerDereference => AssertMessage::NullPointerDereference,
        mir::AssertKind::InvalidEnumConstruction(_) => AssertMessage::InvalidEnumConstruction,
        _ => AssertMessage::Custom(format!("{msg:?}")),
    }
}

/// Try to extract a function name from a Call operand.
fn func_operand_name<'tcx>(tcx: TyCtxt<'tcx>, func: &mir::Operand<'tcx>) -> String {
    match func {
        mir::Operand::Constant(box const_op) => {
            let ty = const_op.const_.ty();
            match ty.kind() {
                rustc_middle::ty::TyKind::FnDef(def_id, _) => {
                    crate::safe_def_path_str(tcx, *def_id)
                }
                _ => format!("{ty}"),
            }
        }
        _ => "<indirect>".to_string(),
    }
}

/// Convert a rustc Span to our SourceSpan.
pub(crate) fn convert_span(tcx: TyCtxt<'_>, span: Span) -> SourceSpan {
    if span.is_dummy() {
        return SourceSpan::default();
    }

    let source_map = tcx.sess.source_map();
    let lo = source_map.lookup_char_pos(span.lo());
    let hi = source_map.lookup_char_pos(span.hi());

    SourceSpan {
        file: lo.file.name.prefer_local_unconditionally().to_string(),
        line_start: lo.line as u32,
        col_start: lo.col.0 as u32,
        line_end: hi.line as u32,
        col_end: hi.col.0 as u32,
    }
}

// tRust #605: Tests for atomic intrinsic detection.
// These tests exercise parse_atomic_intrinsic with synthetic function names
// and do not require a rustc TyCtxt.
#[cfg(test)]
mod tests {
    use super::*;
    extern crate rustc_driver;
    extern crate rustc_hir;
    extern crate rustc_interface;

    use std::collections::BTreeMap;
    use std::io;
    use std::path::Path;
    use std::process::Command;
    use std::sync::{Arc, OnceLock};

    use rustc_driver::Compilation;
    use rustc_interface::interface::{Compiler, Config};

    const CONST_AGGREGATE_RETURN_SHAPES_SOURCE: &str = r#"
const ARR: [i32; 2] = [4, 5];
pub struct PlainStruct { x: i32, y: i32 }
pub struct TupleStruct(i32, i32);
pub enum EmptyEnum { A, B }
pub enum PairEnum { Pair(i32, i32), Empty }
pub enum TaggedPairEnum { Empty, Pair(i32, i32) }
pub fn char_return() -> char { 'A' }
pub fn unit_return() -> () { () }
pub fn tuple_char() -> (char, i32) { ('A', 1) }
pub fn tuple_unit_i32() -> ((), i32) { ((), 1) }
pub fn empty_enum_a() -> EmptyEnum { EmptyEnum::A }
pub fn empty_enum_b() -> EmptyEnum { EmptyEnum::B }
pub fn option_none() -> Option<i32> { None }
pub fn option_some() -> Option<i32> { Some(1) }
pub fn result_ok() -> Result<i32, i32> { Ok(1) }
pub fn result_err() -> Result<i32, i32> { Err(2) }
pub fn array_from_named_const() -> [i32; 2] { ARR }
pub fn plain_struct() -> PlainStruct { PlainStruct { x: 3, y: 4 } }
pub fn tuple_struct() -> TupleStruct { TupleStruct(7, 8) }
pub fn pair_enum() -> PairEnum { PairEnum::Pair(9, 10) }
pub fn tagged_pair_enum() -> TaggedPairEnum { TaggedPairEnum::Pair(11, 12) }
pub fn small_array() -> [i32; 2] { [5, 6] }
"#;
    const TEST_CRATE_PATH: &str = "return_shapes.rs";

    struct InMemoryFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(TEST_CRATE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CONST_AGGREGATE_RETURN_SHAPES_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected test file path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in convert.rs tests"))
        }
    }

    struct ReturnShapeCallbacks {
        results: BTreeMap<String, Rvalue>,
    }

    impl rustc_driver::Callbacks for ReturnShapeCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let fn_name = ident.name.to_string();
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.results
                        .insert(fn_name.clone(), extract_return_place_rvalue(tcx, body, &fn_name));
                }
            }

            Compilation::Stop
        }
    }

    fn compiler_sysroot() -> Option<String> {
        option_env!("TEST_SYSROOT")
            .map(str::to_owned)
            .or_else(|| std::env::var("RUSTC_SYSROOT").ok())
            .or_else(|| std::env::var("SYSROOT").ok())
            .or_else(|| {
                let rustc = std::env::var("RUSTC")
                    .ok()
                    .or_else(|| option_env!("RUSTC").map(str::to_owned))
                    .unwrap_or_else(|| "rustc".to_string());
                let output = Command::new(rustc).args(["--print", "sysroot"]).output().ok()?;
                if !output.status.success() {
                    return None;
                }
                let sysroot = String::from_utf8_lossy(&output.stdout).trim().to_string();
                (!sysroot.is_empty()).then_some(sysroot)
            })
    }

    fn compile_const_aggregate_return_shapes() -> BTreeMap<String, Rvalue> {
        let mut callbacks = ReturnShapeCallbacks { results: BTreeMap::new() };
        let mut args = vec![
            "rustc".to_string(),
            TEST_CRATE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_convert_return_shapes".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
        ];
        if let Some(sysroot) = compiler_sysroot() {
            args.push("--sysroot".to_string());
            args.push(sysroot);
        }

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile const aggregate return-shape test crate");

        callbacks.results
    }

    fn const_aggregate_return_shapes() -> &'static BTreeMap<String, Rvalue> {
        static RETURN_SHAPES: OnceLock<BTreeMap<String, Rvalue>> = OnceLock::new();
        RETURN_SHAPES.get_or_init(compile_const_aggregate_return_shapes)
    }

    fn extract_return_place_rvalue<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        fn_name: &str,
    ) -> Rvalue {
        let return_assignments = body
            .basic_blocks
            .iter()
            .flat_map(|bb| bb.statements.iter())
            .filter_map(|stmt| match &stmt.kind {
                mir::StatementKind::Assign(box (place, rvalue))
                    if place.local == mir::RETURN_PLACE =>
                {
                    Some(convert_rvalue(tcx, rvalue))
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        assert_eq!(
            return_assignments.len(),
            1,
            "expected a single `_0` assignment in optimized MIR for `{fn_name}`, got {return_assignments:?}",
        );
        return_assignments.into_iter().next().unwrap()
    }

    fn assert_constant_int_operand(operand: &Operand, expected: i128) {
        match operand {
            Operand::Constant(ConstValue::Int(value)) => assert_eq!(*value, expected),
            other => panic!("expected integer constant operand, got {other:?}"),
        }
    }

    fn assert_constant_uint_operand(operand: &Operand, expected: u128, expected_width: u32) {
        match operand {
            Operand::Constant(ConstValue::Uint(value, width)) => {
                assert_eq!(*value, expected);
                assert_eq!(*width, expected_width);
            }
            other => panic!("expected unsigned integer constant operand, got {other:?}"),
        }
    }

    fn assert_unit_operand(operand: &Operand) {
        assert!(matches!(operand, Operand::Constant(ConstValue::Unit)));
    }

    fn assert_adt_name(name: &str, expected_suffix: &str) {
        assert!(
            name.ends_with(expected_suffix),
            "expected ADT path ending with `{expected_suffix}`, got `{name}`",
        );
    }

    /// Helper: build args with a Copy operand as the first arg (pointer place).
    fn ptr_args() -> Vec<Operand> {
        vec![Operand::Copy(Place::local(1))]
    }

    /// Helper: build args with two operands (ptr + value).
    fn ptr_val_args() -> Vec<Operand> {
        vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Uint(42, 64))]
    }

    /// Helper: build args for CAS (ptr, old, new).
    fn cas_args() -> Vec<Operand> {
        vec![
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(0, 64)),
            Operand::Constant(ConstValue::Uint(1, 64)),
        ]
    }

    fn default_dest() -> Place {
        Place::local(0)
    }

    fn default_span() -> SourceSpan {
        SourceSpan::default()
    }

    // --- Form A: load ---

    #[test]
    fn form_a_load_seqcst() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_seqcst",
            &ptr_args(),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should detect atomic load");
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.failure_ordering.is_none());
        assert!(op.dest.is_some());
        assert_eq!(op.place, Place::local(1));
    }

    #[test]
    fn form_a_load_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_acquire",
            &ptr_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn form_a_load_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_relaxed",
            &ptr_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Relaxed);
    }

    // --- Form A: store ---

    #[test]
    fn form_a_store_release() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_store_release",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert_eq!(op.ordering, AtomicOrdering::Release);
        assert!(op.dest.is_none(), "store has no return value");
    }

    #[test]
    fn form_a_store_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_store_seqcst",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
    }

    #[test]
    fn form_a_store_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_store_relaxed",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert_eq!(op.ordering, AtomicOrdering::Relaxed);
    }

    // --- Form A: exchange ---

    #[test]
    fn form_a_xchg_acqrel() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xchg_acqrel",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Exchange);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
        assert!(op.dest.is_some());
    }

    // --- Form A: compare_exchange ---

    #[test]
    fn form_a_cxchg_seqcst_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchg_seqcst_seqcst",
            &cas_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::SeqCst));
    }

    #[test]
    fn form_a_cxchg_acqrel_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchg_acqrel_acquire",
            &cas_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Acquire));
    }

    #[test]
    fn form_a_cxchg_release_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchg_release_relaxed",
            &cas_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert_eq!(op.ordering, AtomicOrdering::Release);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Relaxed));
    }

    // --- Form A: compare_exchange_weak ---

    #[test]
    fn form_a_cxchgweak_acquire_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchgweak_acquire_relaxed",
            &cas_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchangeWeak);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Relaxed));
    }

    // --- Form A: fetch operations ---

    #[test]
    fn form_a_xadd_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xadd_seqcst",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchAdd);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.dest.is_some());
    }

    #[test]
    fn form_a_xsub_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xsub_relaxed",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchSub);
        assert_eq!(op.ordering, AtomicOrdering::Relaxed);
    }

    #[test]
    fn form_a_and_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_and_acquire",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchAnd);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn form_a_or_release() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_or_release",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchOr);
        assert_eq!(op.ordering, AtomicOrdering::Release);
    }

    #[test]
    fn form_a_xor_acqrel() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xor_acqrel",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchXor);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
    }

    #[test]
    fn form_a_nand_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_nand_seqcst",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchNand);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
    }

    #[test]
    fn form_a_min_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_min_relaxed",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchMin);
    }

    #[test]
    fn form_a_max_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_max_seqcst",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchMax);
    }

    #[test]
    fn form_a_umin_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_umin_relaxed",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchMin);
    }

    #[test]
    fn form_a_umax_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_umax_seqcst",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchMax);
    }

    // --- Form A: fence ---

    #[test]
    fn form_a_fence_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_seqcst",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.dest.is_none(), "fence has no return value");
        assert_eq!(op.place, Place::local(0), "fence has synthetic place");
    }

    #[test]
    fn form_a_fence_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_acquire",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn form_a_fence_release() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_release",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::Release);
    }

    #[test]
    fn form_a_fence_acqrel() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_acqrel",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
    }

    // --- Form A: singlethreadfence (compiler_fence) ---

    #[test]
    fn form_a_singlethreadfence_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_singlethreadfence_seqcst",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompilerFence);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.dest.is_none());
    }

    #[test]
    fn form_a_singlethreadfence_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_singlethreadfence_acquire",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompilerFence);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    // --- Form A: consume ordering maps to acquire ---

    #[test]
    fn form_a_load_consume_maps_to_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_consume",
            &ptr_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Acquire, "Consume maps to Acquire");
    }

    // --- Form B: generic atomic calls ---

    #[test]
    fn form_b_atomic_load() {
        let op = parse_atomic_intrinsic(
            "std::sync::atomic::atomic::atomic_load",
            &ptr_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        // Form B defaults to SeqCst when const ordering extraction not available
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
    }

    #[test]
    fn form_b_atomic_store() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_store",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert!(op.dest.is_none());
    }

    #[test]
    fn form_b_atomic_exchange() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_exchange",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Exchange);
        assert!(op.dest.is_some());
    }

    #[test]
    fn form_b_atomic_compare_exchange() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_compare_exchange",
            &cas_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert!(op.failure_ordering.is_some());
    }

    #[test]
    fn form_b_atomic_fetch_add() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_fetch_add",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchAdd);
    }

    #[test]
    fn form_b_atomic_fence() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_fence",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert!(op.dest.is_none());
    }

    // --- Non-atomic function names ---

    #[test]
    fn non_atomic_returns_none() {
        assert!(
            parse_atomic_intrinsic(
                "std::vec::Vec::push",
                &ptr_val_args(),
                &default_dest(),
                &default_span(),
            )
            .is_none()
        );
    }

    #[test]
    fn empty_name_returns_none() {
        assert!(parse_atomic_intrinsic("", &[], &default_dest(), &default_span(),).is_none());
    }

    #[test]
    fn indirect_call_returns_none() {
        assert!(
            parse_atomic_intrinsic("<indirect>", &[], &default_dest(), &default_span(),).is_none()
        );
    }

    // --- Place extraction ---

    #[test]
    fn place_extracted_from_copy_arg() {
        let args = vec![Operand::Copy(Place { local: 5, projections: vec![Projection::Deref] })];
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_seqcst",
            &args,
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.place.local, 5);
        assert_eq!(op.place.projections, vec![Projection::Deref]);
    }

    #[test]
    fn place_extracted_from_move_arg() {
        let args = vec![Operand::Move(Place::local(7))];
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_relaxed",
            &args,
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.place, Place::local(7));
    }

    #[test]
    fn place_fallback_for_constant_arg() {
        let args = vec![Operand::Constant(ConstValue::Uint(0, 64))];
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_relaxed",
            &args,
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.place, Place::local(0), "falls back to Place::local(0)");
    }

    #[test]
    fn place_fallback_for_no_args() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_relaxed",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.place, Place::local(0));
    }

    // --- Bare fence/compiler_fence paths ---

    #[test]
    fn bare_fence_path() {
        let op = parse_atomic_intrinsic(
            "std::sync::atomic::fence",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
    }

    #[test]
    fn bare_compiler_fence_path() {
        let op = parse_atomic_intrinsic(
            "std::sync::atomic::compiler_fence",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompilerFence);
    }

    // --- All five orderings on a single operation ---

    #[test]
    fn all_orderings_for_xadd() {
        let orderings = [
            ("relaxed", AtomicOrdering::Relaxed),
            ("acquire", AtomicOrdering::Acquire),
            ("release", AtomicOrdering::Release),
            ("acqrel", AtomicOrdering::AcqRel),
            ("seqcst", AtomicOrdering::SeqCst),
        ];
        for (suffix, expected) in &orderings {
            let name = format!("core::intrinsics::atomic_xadd_{suffix}");
            let op =
                parse_atomic_intrinsic(&name, &ptr_val_args(), &default_dest(), &default_span())
                    .unwrap();
            assert_eq!(op.ordering, *expected, "xadd_{suffix} should be {expected:?}");
        }
    }

    // --- CAS ordering combinations ---

    #[test]
    fn cas_all_valid_combinations() {
        let cases = [
            ("seqcst_seqcst", AtomicOrdering::SeqCst, AtomicOrdering::SeqCst),
            ("seqcst_acquire", AtomicOrdering::SeqCst, AtomicOrdering::Acquire),
            ("seqcst_relaxed", AtomicOrdering::SeqCst, AtomicOrdering::Relaxed),
            ("acqrel_acquire", AtomicOrdering::AcqRel, AtomicOrdering::Acquire),
            ("acqrel_relaxed", AtomicOrdering::AcqRel, AtomicOrdering::Relaxed),
            ("acquire_acquire", AtomicOrdering::Acquire, AtomicOrdering::Acquire),
            ("acquire_relaxed", AtomicOrdering::Acquire, AtomicOrdering::Relaxed),
            ("release_relaxed", AtomicOrdering::Release, AtomicOrdering::Relaxed),
            ("relaxed_relaxed", AtomicOrdering::Relaxed, AtomicOrdering::Relaxed),
        ];
        for (suffix, exp_success, exp_failure) in &cases {
            let name = format!("core::intrinsics::atomic_cxchg_{suffix}");
            let op = parse_atomic_intrinsic(&name, &cas_args(), &default_dest(), &default_span())
                .unwrap();
            assert_eq!(op.ordering, *exp_success, "CAS {suffix} success");
            assert_eq!(op.failure_ordering, Some(*exp_failure), "CAS {suffix} failure");
        }
    }

    // --- Invalid ordering suffix returns None ---

    #[test]
    fn invalid_ordering_suffix_returns_none() {
        assert!(
            parse_atomic_intrinsic(
                "core::intrinsics::atomic_load_bogus",
                &ptr_args(),
                &default_dest(),
                &default_span(),
            )
            .is_none()
        );
    }

    #[test]
    fn invalid_cas_ordering_returns_none() {
        assert!(
            parse_atomic_intrinsic(
                "core::intrinsics::atomic_cxchg_seqcst_bogus",
                &cas_args(),
                &default_dest(),
                &default_span(),
            )
            .is_none()
        );
    }

    // --- Optimized constant aggregate return shapes ---

    #[test]
    fn optimized_const_char_return_preserves_scalar_value() {
        let rvalue = const_aggregate_return_shapes().get("char_return").unwrap();
        let Rvalue::Use(operand) = rvalue else {
            panic!("expected scalar use rvalue, got {rvalue:?}");
        };
        assert_constant_uint_operand(operand, 'A' as u128, 32);
    }

    #[test]
    fn optimized_const_tuple_char_preserves_char_and_i32_fields() {
        let rvalue = const_aggregate_return_shapes().get("tuple_char").unwrap();
        let Rvalue::Aggregate(AggregateKind::Tuple, operands) = rvalue else {
            panic!("expected tuple aggregate rvalue, got {rvalue:?}");
        };
        assert_eq!(operands.len(), 2);
        assert_constant_uint_operand(&operands[0], 'A' as u128, 32);
        assert_constant_int_operand(&operands[1], 1);
    }

    fn optimized_const_unit_return_stays_unit() {
        let rvalue = const_aggregate_return_shapes().get("unit_return").unwrap();
        assert!(matches!(rvalue, Rvalue::Use(Operand::Constant(ConstValue::Unit))));
    }

    #[test]
    fn optimized_const_tuple_preserves_unit_and_i32_fields() {
        let rvalue = const_aggregate_return_shapes().get("tuple_unit_i32").unwrap();
        let Rvalue::Aggregate(AggregateKind::Tuple, operands) = rvalue else {
            panic!("expected tuple aggregate rvalue, got {rvalue:?}");
        };
        assert_eq!(operands.len(), 2);
        assert_unit_operand(&operands[0]);
        assert_constant_int_operand(&operands[1], 1);
    }

    #[test]
    fn optimized_const_empty_enum_a_preserves_variant_shape() {
        let rvalue = const_aggregate_return_shapes().get("empty_enum_a").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::EmptyEnum");
        assert_eq!(*variant, 0);
        assert!(operands.is_empty(), "fieldless enum variant should not carry payload fields");
    }

    #[test]
    fn optimized_const_empty_enum_b_preserves_variant_shape() {
        let rvalue = const_aggregate_return_shapes().get("empty_enum_b").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::EmptyEnum");
        assert_eq!(*variant, 1);
        assert!(operands.is_empty(), "fieldless enum variant should not carry payload fields");
    }

    #[test]
    fn optimized_const_option_none_preserves_variant_shape() {
        let rvalue = const_aggregate_return_shapes().get("option_none").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::Option");
        assert_eq!(*variant, 0);
        assert!(operands.is_empty(), "Option::None should not carry payload fields");
    }

    #[test]
    fn optimized_const_option_some_preserves_payload() {
        let rvalue = const_aggregate_return_shapes().get("option_some").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::Option");
        assert_eq!(*variant, 1);
        assert_eq!(operands.len(), 1);
        assert_constant_int_operand(&operands[0], 1);
    }

    #[test]
    fn optimized_const_result_ok_preserves_payload() {
        let rvalue = const_aggregate_return_shapes().get("result_ok").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::Result");
        assert_eq!(*variant, 0);
        assert_eq!(operands.len(), 1);
        assert_constant_int_operand(&operands[0], 1);
    }

    #[test]
    fn optimized_const_result_err_preserves_payload() {
        let rvalue = const_aggregate_return_shapes().get("result_err").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::Result");
        assert_eq!(*variant, 1);
        assert_eq!(operands.len(), 1);
        assert_constant_int_operand(&operands[0], 2);
    }

    #[test]
    fn optimized_const_named_array_preserves_elements() {
        let rvalue = const_aggregate_return_shapes().get("array_from_named_const").unwrap();
        let Rvalue::Aggregate(AggregateKind::Array, operands) = rvalue else {
            panic!("expected array aggregate rvalue, got {rvalue:?}");
        };
        assert_eq!(operands.len(), 2);
        assert_constant_int_operand(&operands[0], 4);
        assert_constant_int_operand(&operands[1], 5);
    }

    #[test]
    fn optimized_const_plain_struct_preserves_fields() {
        let rvalue = const_aggregate_return_shapes().get("plain_struct").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::PlainStruct");
        assert_eq!(*variant, 0);
        assert_eq!(operands.len(), 2);
        assert_constant_int_operand(&operands[0], 3);
        assert_constant_int_operand(&operands[1], 4);
    }

    #[test]
    fn optimized_const_tuple_struct_preserves_fields() {
        let rvalue = const_aggregate_return_shapes().get("tuple_struct").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::TupleStruct");
        assert_eq!(*variant, 0);
        assert_eq!(operands.len(), 2);
        assert_constant_int_operand(&operands[0], 7);
        assert_constant_int_operand(&operands[1], 8);
    }

    #[test]
    fn optimized_const_pair_enum_preserves_multi_field_payload() {
        let rvalue = const_aggregate_return_shapes().get("pair_enum").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::PairEnum");
        assert_eq!(*variant, 0);
        assert_eq!(operands.len(), 2);
        assert_constant_int_operand(&operands[0], 9);
        assert_constant_int_operand(&operands[1], 10);
    }

    #[test]
    fn optimized_const_tagged_pair_enum_preserves_nonzero_variant_payload() {
        let rvalue = const_aggregate_return_shapes().get("tagged_pair_enum").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::TaggedPairEnum");
        assert_eq!(*variant, 1);
        assert_eq!(operands.len(), 2);
        assert_constant_int_operand(&operands[0], 11);
        assert_constant_int_operand(&operands[1], 12);
    }

    #[test]
    fn optimized_const_small_array_preserves_elements() {
        let rvalue = const_aggregate_return_shapes().get("small_array").unwrap();
        let Rvalue::Aggregate(AggregateKind::Array, operands) = rvalue else {
            panic!("expected array aggregate rvalue, got {rvalue:?}");
        };
        assert_eq!(operands.len(), 2);
        assert_constant_int_operand(&operands[0], 5);
        assert_constant_int_operand(&operands[1], 6);
    }
}
