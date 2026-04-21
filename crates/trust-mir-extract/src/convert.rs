// trust-mir-extract/convert.rs: Convert MIR structures to trust-types
//
// Handles: BasicBlock, Statement, Terminator, Rvalue, Operand, Place, BinOp
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;
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

        mir::Rvalue::Len(place) => Rvalue::Len(convert_place(place)),

        mir::Rvalue::Repeat(operand, count) => {
            // count is a ty::Const; extract the usize value or default to 0.
            let n = count
                .try_to_target_usize(tcx)
                .map(|v| v as usize)
                .unwrap_or(0);
            Rvalue::Repeat(convert_operand(tcx, operand), n)
        }

        mir::Rvalue::RawPtr(mutability, place) => {
            let mutable = mutability.is_mut();
            Rvalue::AddressOf(mutable, convert_place(place))
        }

        mir::Rvalue::CopyForDeref(place) => Rvalue::CopyForDeref(convert_place(place)),

        // For rvalues we don't handle yet, use a fallback
        _ => Rvalue::Use(Operand::Constant(ConstValue::Unit)),
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

    // Unit type
    if ty.is_unit() {
        return Operand::Constant(ConstValue::Unit);
    }

    Operand::Constant(ConstValue::Unit)
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

    /// Helper: build args with a Copy operand as the first arg (pointer place).
    fn ptr_args() -> Vec<Operand> {
        vec![Operand::Copy(Place::local(1))]
    }

    /// Helper: build args with two operands (ptr + value).
    fn ptr_val_args() -> Vec<Operand> {
        vec![
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(42, 64)),
        ]
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
            &ptr_args(), &default_dest(), &default_span(),
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
            &ptr_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn form_a_load_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_relaxed",
            &ptr_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Relaxed);
    }

    // --- Form A: store ---

    #[test]
    fn form_a_store_release() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_store_release",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert_eq!(op.ordering, AtomicOrdering::Release);
        assert!(op.dest.is_none(), "store has no return value");
    }

    #[test]
    fn form_a_store_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_store_seqcst",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
    }

    #[test]
    fn form_a_store_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_store_relaxed",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert_eq!(op.ordering, AtomicOrdering::Relaxed);
    }

    // --- Form A: exchange ---

    #[test]
    fn form_a_xchg_acqrel() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xchg_acqrel",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Exchange);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
        assert!(op.dest.is_some());
    }

    // --- Form A: compare_exchange ---

    #[test]
    fn form_a_cxchg_seqcst_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchg_seqcst_seqcst",
            &cas_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::SeqCst));
    }

    #[test]
    fn form_a_cxchg_acqrel_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchg_acqrel_acquire",
            &cas_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Acquire));
    }

    #[test]
    fn form_a_cxchg_release_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchg_release_relaxed",
            &cas_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert_eq!(op.ordering, AtomicOrdering::Release);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Relaxed));
    }

    // --- Form A: compare_exchange_weak ---

    #[test]
    fn form_a_cxchgweak_acquire_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchgweak_acquire_relaxed",
            &cas_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchangeWeak);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Relaxed));
    }

    // --- Form A: fetch operations ---

    #[test]
    fn form_a_xadd_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xadd_seqcst",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchAdd);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.dest.is_some());
    }

    #[test]
    fn form_a_xsub_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xsub_relaxed",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchSub);
        assert_eq!(op.ordering, AtomicOrdering::Relaxed);
    }

    #[test]
    fn form_a_and_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_and_acquire",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchAnd);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn form_a_or_release() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_or_release",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchOr);
        assert_eq!(op.ordering, AtomicOrdering::Release);
    }

    #[test]
    fn form_a_xor_acqrel() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xor_acqrel",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchXor);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
    }

    #[test]
    fn form_a_nand_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_nand_seqcst",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchNand);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
    }

    #[test]
    fn form_a_min_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_min_relaxed",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchMin);
    }

    #[test]
    fn form_a_max_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_max_seqcst",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchMax);
    }

    #[test]
    fn form_a_umin_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_umin_relaxed",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchMin);
    }

    #[test]
    fn form_a_umax_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_umax_seqcst",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchMax);
    }

    // --- Form A: fence ---

    #[test]
    fn form_a_fence_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_seqcst",
            &[], &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.dest.is_none(), "fence has no return value");
        assert_eq!(op.place, Place::local(0), "fence has synthetic place");
    }

    #[test]
    fn form_a_fence_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_acquire",
            &[], &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn form_a_fence_release() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_release",
            &[], &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::Release);
    }

    #[test]
    fn form_a_fence_acqrel() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_acqrel",
            &[], &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
    }

    // --- Form A: singlethreadfence (compiler_fence) ---

    #[test]
    fn form_a_singlethreadfence_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_singlethreadfence_seqcst",
            &[], &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompilerFence);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.dest.is_none());
    }

    #[test]
    fn form_a_singlethreadfence_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_singlethreadfence_acquire",
            &[], &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompilerFence);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    // --- Form A: consume ordering maps to acquire ---

    #[test]
    fn form_a_load_consume_maps_to_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_consume",
            &ptr_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Acquire, "Consume maps to Acquire");
    }

    // --- Form B: generic atomic calls ---

    #[test]
    fn form_b_atomic_load() {
        let op = parse_atomic_intrinsic(
            "std::sync::atomic::atomic::atomic_load",
            &ptr_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        // Form B defaults to SeqCst when const ordering extraction not available
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
    }

    #[test]
    fn form_b_atomic_store() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_store",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert!(op.dest.is_none());
    }

    #[test]
    fn form_b_atomic_exchange() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_exchange",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Exchange);
        assert!(op.dest.is_some());
    }

    #[test]
    fn form_b_atomic_compare_exchange() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_compare_exchange",
            &cas_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert!(op.failure_ordering.is_some());
    }

    #[test]
    fn form_b_atomic_fetch_add() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_fetch_add",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchAdd);
    }

    #[test]
    fn form_b_atomic_fence() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_fence",
            &[], &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert!(op.dest.is_none());
    }

    // --- Non-atomic function names ---

    #[test]
    fn non_atomic_returns_none() {
        assert!(parse_atomic_intrinsic(
            "std::vec::Vec::push",
            &ptr_val_args(), &default_dest(), &default_span(),
        ).is_none());
    }

    #[test]
    fn empty_name_returns_none() {
        assert!(parse_atomic_intrinsic(
            "",
            &[], &default_dest(), &default_span(),
        ).is_none());
    }

    #[test]
    fn indirect_call_returns_none() {
        assert!(parse_atomic_intrinsic(
            "<indirect>",
            &[], &default_dest(), &default_span(),
        ).is_none());
    }

    // --- Place extraction ---

    #[test]
    fn place_extracted_from_copy_arg() {
        let args = vec![Operand::Copy(Place { local: 5, projections: vec![Projection::Deref] })];
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_seqcst",
            &args, &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.place.local, 5);
        assert_eq!(op.place.projections, vec![Projection::Deref]);
    }

    #[test]
    fn place_extracted_from_move_arg() {
        let args = vec![Operand::Move(Place::local(7))];
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_relaxed",
            &args, &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.place, Place::local(7));
    }

    #[test]
    fn place_fallback_for_constant_arg() {
        let args = vec![Operand::Constant(ConstValue::Uint(0, 64))];
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_relaxed",
            &args, &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.place, Place::local(0), "falls back to Place::local(0)");
    }

    #[test]
    fn place_fallback_for_no_args() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_relaxed",
            &[], &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.place, Place::local(0));
    }

    // --- Bare fence/compiler_fence paths ---

    #[test]
    fn bare_fence_path() {
        let op = parse_atomic_intrinsic(
            "std::sync::atomic::fence",
            &[], &default_dest(), &default_span(),
        ).unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
    }

    #[test]
    fn bare_compiler_fence_path() {
        let op = parse_atomic_intrinsic(
            "std::sync::atomic::compiler_fence",
            &[], &default_dest(), &default_span(),
        ).unwrap();
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
            let op = parse_atomic_intrinsic(
                &name, &ptr_val_args(), &default_dest(), &default_span(),
            ).unwrap();
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
            let op = parse_atomic_intrinsic(
                &name, &cas_args(), &default_dest(), &default_span(),
            ).unwrap();
            assert_eq!(op.ordering, *exp_success, "CAS {suffix} success");
            assert_eq!(op.failure_ordering, Some(*exp_failure), "CAS {suffix} failure");
        }
    }

    // --- Invalid ordering suffix returns None ---

    #[test]
    fn invalid_ordering_suffix_returns_none() {
        assert!(parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_bogus",
            &ptr_args(), &default_dest(), &default_span(),
        ).is_none());
    }

    #[test]
    fn invalid_cas_ordering_returns_none() {
        assert!(parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchg_seqcst_bogus",
            &cas_args(), &default_dest(), &default_span(),
        ).is_none());
    }
}
