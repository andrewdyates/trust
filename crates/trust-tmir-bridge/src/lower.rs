//! Core lowering: trust-types VerifiableFunction -> tMIR Module/Function.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// tRust: deterministic hashing for reproducible builds (#827)
use trust_types::fx::FxHashMap;

use tmir::inst::{
    BinOp as TmirBinOp, CastOp, ICmpOp, Inst, Ordering as TmirOrdering, OverflowOp, SwitchCase,
    UnOp as TmirUnOp,
};
use tmir::node::InstrNode;
use tmir::proof::{ObligationKind, ProofAnnotation, ProofObligation, ProofStatus};
use tmir::ty::{FuncTy, Ty as TmirTy};
use tmir::value::{BlockId as TmirBlockId, FuncId, ProofId, ValueId};
use tmir::{Block as TmirBlock, Constant as TmirConstant, Function as TmirFunction, Module};

use trust_types::{
    AssertMessage, AtomicOpKind, AtomicOperation, AtomicOrdering, BasicBlock as TrustBlock, BinOp,
    ConstValue, ContractKind, LocalDecl, Operand, Place, Projection, Rvalue, Statement, Terminator,
    Ty, UnOp, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors during trust-types to tMIR conversion.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum BridgeError {
    #[error("unsupported type: {0}")]
    UnsupportedType(String),

    #[error("unsupported operation: {0}")]
    UnsupportedOp(String),

    #[error("missing block: bb{0}")]
    MissingBlock(usize),

    #[error("missing local: _{0}")]
    MissingLocal(usize),
}

// ---------------------------------------------------------------------------
// Type mapping: trust-types Ty -> tmir Ty
// ---------------------------------------------------------------------------

/// Convert a trust-types `Ty` to a tMIR `Ty`.
///
/// tMIR does not distinguish signed vs unsigned integers -- the distinction is
/// carried in operations (SDiv vs UDiv, Slt vs Ult). All integer types map by
/// width only.
///
/// ## Mapping gaps
///
/// - `Ty::Ref` and `Ty::RawPtr` -> `TmirTy::Ptr` (single opaque pointer type)
/// - `Ty::Slice` -> `TmirTy::Ptr` (pointer to unsized data)
/// - `Ty::Tuple` -> tMIR struct (registered in the module)
/// - `Ty::Adt` -> tMIR struct (registered in the module)
/// - `Ty::Bv(w)` -> closest integer type by width
/// - `Ty::Never` -> `TmirTy::Void`
pub fn map_type(ty: &Ty) -> Result<TmirTy, BridgeError> {
    match ty {
        Ty::Bool => Ok(TmirTy::Bool),
        Ty::Int { width: 8, .. } => Ok(TmirTy::I8),
        Ty::Int { width: 16, .. } => Ok(TmirTy::I16),
        Ty::Int { width: 32, .. } => Ok(TmirTy::I32),
        Ty::Int { width: 64, .. } => Ok(TmirTy::I64),
        Ty::Int { width: 128, .. } => Ok(TmirTy::I128),
        Ty::Float { width: 32 } => Ok(TmirTy::F32),
        Ty::Float { width: 64 } => Ok(TmirTy::F64),
        Ty::Unit => Ok(TmirTy::Void),
        Ty::Never => Ok(TmirTy::Void),
        Ty::Ref { .. } | Ty::RawPtr { .. } | Ty::Slice { .. } => Ok(TmirTy::Ptr),
        Ty::Array { elem, len } => {
            let elem_ty = map_type(elem)?;
            // We need to register elem_ty in the module's type table, but since
            // map_type is stateless, we use a placeholder TyId(0). The caller
            // (LoweringCtx) handles registration.
            // For now, return the best approximation: Ptr for variable-length,
            // or Array if we can express it.
            // tMIR Array(TyId, u64) needs a TyId from the module. Since we
            // don't have module context here, return Ptr as a conservative
            // approximation. The full lowering in LoweringCtx handles this properly.
            let _ = elem_ty;
            Ok(TmirTy::Array(tmir::value::TyId::new(0), *len))
        }
        Ty::Tuple(elems) if elems.is_empty() => Ok(TmirTy::Void),
        // Non-empty tuples and ADTs need struct registration (handled in LoweringCtx).
        // Return Ptr as a conservative fallback from this stateless function.
        Ty::Tuple(_) | Ty::Adt { .. } => Ok(TmirTy::Ptr),
        Ty::Bv(w) => match w {
            8 => Ok(TmirTy::I8),
            16 => Ok(TmirTy::I16),
            32 => Ok(TmirTy::I32),
            64 => Ok(TmirTy::I64),
            128 => Ok(TmirTy::I128),
            _ => Err(BridgeError::UnsupportedType(format!("Bv({w})"))),
        },
        _ => Err(BridgeError::UnsupportedType(format!("{ty:?}"))),
    }
}

// ---------------------------------------------------------------------------
// BinOp mapping
// ---------------------------------------------------------------------------

/// Convert a trust-types `BinOp` to a tMIR `BinOp` or `ICmpOp`.
///
/// Returns `(Some(binop), None)` for arithmetic ops or `(None, Some(icmp))` for
/// comparison ops.
///
/// The `signed` parameter controls division/remainder (SDiv vs UDiv) and
/// comparison signedness (Slt vs Ult).
pub fn map_binop(op: BinOp, signed: bool) -> Result<BinOpMapping, BridgeError> {
    match op {
        BinOp::Add => Ok(BinOpMapping::Arith(TmirBinOp::Add)),
        BinOp::Sub => Ok(BinOpMapping::Arith(TmirBinOp::Sub)),
        BinOp::Mul => Ok(BinOpMapping::Arith(TmirBinOp::Mul)),
        BinOp::Div if signed => Ok(BinOpMapping::Arith(TmirBinOp::SDiv)),
        BinOp::Div => Ok(BinOpMapping::Arith(TmirBinOp::UDiv)),
        BinOp::Rem if signed => Ok(BinOpMapping::Arith(TmirBinOp::SRem)),
        BinOp::Rem => Ok(BinOpMapping::Arith(TmirBinOp::URem)),
        BinOp::BitAnd => Ok(BinOpMapping::Arith(TmirBinOp::And)),
        BinOp::BitOr => Ok(BinOpMapping::Arith(TmirBinOp::Or)),
        BinOp::BitXor => Ok(BinOpMapping::Arith(TmirBinOp::Xor)),
        BinOp::Shl => Ok(BinOpMapping::Arith(TmirBinOp::Shl)),
        BinOp::Shr if signed => Ok(BinOpMapping::Arith(TmirBinOp::AShr)),
        BinOp::Shr => Ok(BinOpMapping::Arith(TmirBinOp::LShr)),
        BinOp::Eq => Ok(BinOpMapping::Cmp(ICmpOp::Eq)),
        BinOp::Ne => Ok(BinOpMapping::Cmp(ICmpOp::Ne)),
        BinOp::Lt if signed => Ok(BinOpMapping::Cmp(ICmpOp::Slt)),
        BinOp::Lt => Ok(BinOpMapping::Cmp(ICmpOp::Ult)),
        BinOp::Le if signed => Ok(BinOpMapping::Cmp(ICmpOp::Sle)),
        BinOp::Le => Ok(BinOpMapping::Cmp(ICmpOp::Ule)),
        BinOp::Gt if signed => Ok(BinOpMapping::Cmp(ICmpOp::Sgt)),
        BinOp::Gt => Ok(BinOpMapping::Cmp(ICmpOp::Ugt)),
        BinOp::Ge if signed => Ok(BinOpMapping::Cmp(ICmpOp::Sge)),
        BinOp::Ge => Ok(BinOpMapping::Cmp(ICmpOp::Uge)),
        BinOp::Cmp => Err(BridgeError::UnsupportedOp(
            "three-way Cmp has no direct tMIR equivalent".to_string(),
        )),
        _ => Err(BridgeError::UnsupportedOp(format!("BinOp::{op:?}"))),
    }
}

/// Result of mapping a trust-types BinOp: either an arithmetic BinOp or
/// an integer comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOpMapping {
    Arith(TmirBinOp),
    Cmp(ICmpOp),
}

// ---------------------------------------------------------------------------
// UnOp mapping
// ---------------------------------------------------------------------------

/// Convert a trust-types `UnOp` to a tMIR `UnOp`.
pub fn map_unop(op: UnOp) -> Result<TmirUnOp, BridgeError> {
    match op {
        UnOp::Not => Ok(TmirUnOp::Not),
        UnOp::Neg => Ok(TmirUnOp::Neg),
        UnOp::PtrMetadata => {
            Err(BridgeError::UnsupportedOp("PtrMetadata has no tMIR equivalent".to_string()))
        }
        _ => Err(BridgeError::UnsupportedOp(format!("UnOp::{op:?}"))),
    }
}

/// Map a trust-types BinOp to an OverflowOp for CheckedBinaryOp.
fn map_checked_binop(op: BinOp) -> Result<OverflowOp, BridgeError> {
    match op {
        BinOp::Add => Ok(OverflowOp::AddOverflow),
        BinOp::Sub => Ok(OverflowOp::SubOverflow),
        BinOp::Mul => Ok(OverflowOp::MulOverflow),
        _ => Err(BridgeError::UnsupportedOp(format!(
            "CheckedBinaryOp({op:?}) has no tMIR Overflow equivalent"
        ))),
    }
}

/// Map a trust-types `AtomicOrdering` to a tMIR `Ordering`.
fn map_ordering(ordering: &AtomicOrdering) -> TmirOrdering {
    match ordering {
        AtomicOrdering::Relaxed => TmirOrdering::Relaxed,
        AtomicOrdering::Acquire => TmirOrdering::Acquire,
        AtomicOrdering::Release => TmirOrdering::Release,
        AtomicOrdering::AcqRel => TmirOrdering::AcqRel,
        AtomicOrdering::SeqCst => TmirOrdering::SeqCst,
        _ => TmirOrdering::SeqCst, // conservative fallback for non-exhaustive enum
    }
}

// ---------------------------------------------------------------------------
// Lowering context
// ---------------------------------------------------------------------------

/// Internal state for the lowering pass.
struct LoweringCtx<'a> {
    /// Local variable declarations from the trust-types body.
    locals: &'a [LocalDecl],
    /// Map from trust-types local index to tMIR ValueId.
    local_values: FxHashMap<usize, ValueId>,
    /// Next available ValueId.
    next_value: u32,
    /// tMIR module being built (for type/struct registration).
    module: &'a mut Module,
    /// Proof obligations collected during lowering.
    proof_obligations: Vec<ProofObligation>,
    /// Next proof obligation id.
    next_proof_id: u32,
}

impl<'a> LoweringCtx<'a> {
    fn new(locals: &'a [LocalDecl], arg_count: usize, module: &'a mut Module) -> Self {
        let mut ctx = Self {
            locals,
            local_values: FxHashMap::with_capacity_and_hasher(locals.len(), Default::default()),
            next_value: 0,
            module,
            proof_obligations: Vec::new(),
            next_proof_id: 0,
        };
        // Assign argument locals first (locals[1..=arg_count] are args in MIR convention).
        for i in 1..=arg_count {
            if locals.iter().any(|l| l.index == i) {
                let val = ValueId::new(ctx.next_value);
                ctx.next_value += 1;
                ctx.local_values.insert(i, val);
            }
        }
        // Then assign remaining locals.
        for local in locals {
            if !ctx.local_values.contains_key(&local.index) {
                let val = ValueId::new(ctx.next_value);
                ctx.next_value += 1;
                ctx.local_values.insert(local.index, val);
            }
        }
        ctx
    }

    /// Allocate a fresh temporary ValueId.
    fn fresh_value(&mut self) -> ValueId {
        let v = ValueId::new(self.next_value);
        self.next_value += 1;
        v
    }

    /// Get the tMIR ValueId for a trust-types local index.
    fn local_value(&self, index: usize) -> Result<ValueId, BridgeError> {
        self.local_values.get(&index).copied().ok_or(BridgeError::MissingLocal(index))
    }

    /// Get the type of a local by index.
    fn local_ty(&self, index: usize) -> Result<&Ty, BridgeError> {
        self.locals
            .iter()
            .find(|l| l.index == index)
            .map(|l| &l.ty)
            .ok_or(BridgeError::MissingLocal(index))
    }

    /// Whether a local is a signed integer type.
    fn is_signed(&self, index: usize) -> bool {
        self.local_ty(index).map(|ty: &Ty| ty.is_signed()).unwrap_or(false)
    }

    /// Map a trust-types Ty in context (can register structs/types in module).
    fn map_type_ctx(&mut self, ty: &Ty) -> Result<TmirTy, BridgeError> {
        // For most types, delegate to the stateless map_type.
        // For compound types needing registration, handle here.
        match ty {
            Ty::Array { elem, len } => {
                let elem_tmir = self.map_type_ctx(elem)?;
                let ty_id = self.module.add_type(elem_tmir);
                Ok(TmirTy::Array(ty_id, *len))
            }
            _ => map_type(ty),
        }
    }

    /// Resolve an Operand to a tMIR ValueId, emitting Const instructions as needed.
    fn resolve_operand(
        &mut self,
        op: &Operand,
        body: &mut Vec<InstrNode>,
    ) -> Result<ValueId, BridgeError> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self.resolve_place(place, body),
            Operand::Constant(cv) => self.emit_const(cv, body),
            Operand::Symbolic(_) => Err(BridgeError::UnsupportedOp(
                "Symbolic operands not yet supported in tMIR lowering".to_string(),
            )),
            _ => Err(BridgeError::UnsupportedOp("unknown operand variant".to_string())),
        }
    }

    /// Resolve a Place to a tMIR ValueId, emitting projection instructions.
    fn resolve_place(
        &mut self,
        place: &Place,
        body: &mut Vec<InstrNode>,
    ) -> Result<ValueId, BridgeError> {
        let mut current = self.local_value(place.local)?;

        for proj in &place.projections {
            match proj {
                Projection::Field(idx) => {
                    // ExtractField: get field from aggregate.
                    let local_ty = self.local_ty(place.local)?;
                    let result_ty = field_type(local_ty, *idx)?;
                    let tmir_ty = self.map_type_ctx(&result_ty)?;
                    let result = self.fresh_value();
                    body.push(
                        InstrNode::new(Inst::ExtractField {
                            ty: tmir_ty,
                            aggregate: current,
                            field: *idx as u32,
                        })
                        .with_result(result),
                    );
                    current = result;
                }
                Projection::Index(idx_local) => {
                    // ExtractElement: array/slice indexing.
                    let idx_val = self.local_value(*idx_local)?;
                    let result = self.fresh_value();
                    body.push(
                        InstrNode::new(Inst::ExtractElement {
                            ty: TmirTy::I64, // conservative element type
                            array: current,
                            index: idx_val,
                        })
                        .with_result(result),
                    );
                    current = result;
                }
                Projection::Deref => {
                    // Load through pointer.
                    let result = self.fresh_value();
                    body.push(
                        InstrNode::new(Inst::Load {
                            ty: TmirTy::I64, // conservative; actual type depends on context
                            ptr: current,
                        })
                        .with_result(result),
                    );
                    current = result;
                }
                Projection::Downcast(_variant) => {
                    // Downcast is a type-level operation; the value stays the same.
                    // In tMIR this would be a no-op cast. Leave current unchanged.
                }
                Projection::ConstantIndex { offset, from_end: _ } => {
                    // Constant index -> emit a const + ExtractElement.
                    let idx_val = self.fresh_value();
                    body.push(
                        InstrNode::new(Inst::Const {
                            ty: TmirTy::I64,
                            value: TmirConstant::Int(*offset as i128),
                        })
                        .with_result(idx_val),
                    );
                    let result = self.fresh_value();
                    body.push(
                        InstrNode::new(Inst::ExtractElement {
                            ty: TmirTy::I64,
                            array: current,
                            index: idx_val,
                        })
                        .with_result(result),
                    );
                    current = result;
                }
                Projection::Subslice { .. } => {
                    // Subslice is a pointer arithmetic operation. Model as a GEP.
                    // For now, leave the value unchanged (conservative).
                }
                _ => {
                    // Future projection variants: leave value unchanged (conservative).
                }
            }
        }

        Ok(current)
    }

    /// Emit a tMIR Const instruction for a trust-types ConstValue.
    fn emit_const(
        &mut self,
        cv: &ConstValue,
        body: &mut Vec<InstrNode>,
    ) -> Result<ValueId, BridgeError> {
        let (ty, value) = match cv {
            ConstValue::Bool(b) => (TmirTy::Bool, TmirConstant::Bool(*b)),
            ConstValue::Int(val) => (TmirTy::I64, TmirConstant::Int(*val)),
            ConstValue::Uint(val, width) => {
                let ty = match width {
                    8 => TmirTy::I8,
                    16 => TmirTy::I16,
                    32 => TmirTy::I32,
                    64 => TmirTy::I64,
                    128 => TmirTy::I128,
                    _ => return Err(BridgeError::UnsupportedType(format!("u{width}"))),
                };
                (ty, TmirConstant::Int(*val as i128))
            }
            ConstValue::Float(val) => (TmirTy::F64, TmirConstant::Float(*val)),
            ConstValue::Unit => (TmirTy::Void, TmirConstant::Int(0)),
            _ => {
                return Err(BridgeError::UnsupportedOp("unknown constant variant".to_string()));
            }
        };

        let result = self.fresh_value();
        body.push(InstrNode::new(Inst::Const { ty, value }).with_result(result));
        Ok(result)
    }

    /// Add a proof obligation and return its id.
    fn add_obligation(&mut self, kind: ObligationKind, description: String) -> ProofId {
        let id = ProofId::new(self.next_proof_id);
        self.next_proof_id += 1;
        self.proof_obligations.push(ProofObligation {
            id,
            kind,
            status: ProofStatus::Pending,
            description,
        });
        id
    }
}

/// Get the type of a field in a tuple or ADT.
fn field_type(ty: &Ty, field_idx: usize) -> Result<Ty, BridgeError> {
    match ty {
        Ty::Tuple(elems) => elems.get(field_idx).cloned().ok_or_else(|| {
            BridgeError::UnsupportedOp(format!(
                "tuple field {field_idx} out of range (len {})",
                elems.len()
            ))
        }),
        Ty::Adt { fields, .. } => {
            fields.get(field_idx).map(|(_, fty): &(String, Ty)| fty.clone()).ok_or_else(|| {
                BridgeError::UnsupportedOp(format!(
                    "ADT field {field_idx} out of range (len {})",
                    fields.len()
                ))
            })
        }
        // For other types with field projection (e.g., checked arith tuple),
        // return a conservative type.
        _ => Ok(Ty::i64()),
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Convert a trust-types `VerifiableFunction` into a tMIR `Module` containing
/// a single function.
///
/// This is the primary entry point. The module includes the function, its type
/// signature, and any proof obligations derived from contracts.
pub fn lower_to_tmir(func: &VerifiableFunction) -> Result<Module, BridgeError> {
    let mut module = Module::new(&func.name);
    let tmir_func = lower_function_into(func, &mut module)?;
    module.add_function(tmir_func);
    Ok(module)
}

/// Convert a trust-types `VerifiableFunction` into a tMIR `Function`, adding
/// type registrations to the provided module.
///
/// Use this when building a module with multiple functions.
pub fn lower_to_tmir_function(
    func: &VerifiableFunction,
    module: &mut Module,
) -> Result<TmirFunction, BridgeError> {
    lower_function_into(func, module)
}

fn lower_function_into(
    func: &VerifiableFunction,
    module: &mut Module,
) -> Result<TmirFunction, BridgeError> {
    let body = &func.body;
    let mut ctx = LoweringCtx::new(&body.locals, body.arg_count, module);

    // Build function type signature.
    let return_ty = ctx.map_type_ctx(&body.return_ty)?;
    let mut param_types = Vec::with_capacity(body.arg_count);
    for i in 1..=body.arg_count {
        let local =
            body.locals.iter().find(|l| l.index == i).ok_or(BridgeError::MissingLocal(i))?;
        param_types.push(ctx.map_type_ctx(&local.ty)?);
    }

    let returns =
        if matches!(body.return_ty, Ty::Unit | Ty::Never) { vec![] } else { vec![return_ty] };

    let func_ty = FuncTy { params: param_types, returns, is_vararg: false };
    let func_ty_id = ctx.module.add_func_type(func_ty);
    let func_id = FuncId::new(ctx.module.functions.len() as u32);

    let entry = if body.blocks.is_empty() {
        TmirBlockId::new(0)
    } else {
        TmirBlockId::new(body.blocks[0].id.0 as u32)
    };

    let mut tmir_func = TmirFunction::new(func_id, &func.name, func_ty_id, entry);

    // Convert contracts to proof annotations and obligations.
    for contract in &func.contracts {
        match contract.kind {
            ContractKind::Requires => {
                ctx.add_obligation(ObligationKind::Precondition, contract.body.clone());
            }
            ContractKind::Ensures => {
                ctx.add_obligation(ObligationKind::Postcondition, contract.body.clone());
            }
            ContractKind::Invariant | ContractKind::LoopInvariant => {
                ctx.add_obligation(ObligationKind::LoopInvariant, contract.body.clone());
            }
            ContractKind::TypeRefinement => {
                ctx.add_obligation(ObligationKind::RefinementType, contract.body.clone());
            }
            ContractKind::Decreases | ContractKind::Modifies => {
                // Decreases and Modifies don't directly map to tMIR obligations.
                // They are metadata for downstream verification strategies.
            }
            _ => {
                // Future contract kinds: no-op for now.
            }
        }
    }

    // Add panic-freedom obligation by default (tMIR convention).
    if body.blocks.iter().any(|bb| matches!(bb.terminator, Terminator::Assert { .. })) {
        ctx.add_obligation(
            ObligationKind::PanicFreedom,
            format!("{}: all assertions hold", func.name),
        );
    }

    // Convert each basic block.
    for bb in &body.blocks {
        let tmir_block = lower_block(bb, &mut ctx)?;
        tmir_func.blocks.push(tmir_block);
    }

    // Attach function-level proof annotations.
    tmir_func.proofs.push(ProofAnnotation::Pure);

    // Transfer obligations to module.
    for obligation in ctx.proof_obligations.drain(..) {
        ctx.module.proof_obligations.push(obligation);
    }

    Ok(tmir_func)
}

// ---------------------------------------------------------------------------
// Block lowering
// ---------------------------------------------------------------------------

fn lower_block(bb: &TrustBlock, ctx: &mut LoweringCtx<'_>) -> Result<TmirBlock, BridgeError> {
    let block_id = TmirBlockId::new(bb.id.0 as u32);
    let mut tmir_block = TmirBlock::new(block_id);

    // Add block parameters for argument blocks.
    // In tMIR, block params are explicit; in MIR they are implicit from the locals.
    // For the entry block, the function parameters serve as block params.

    let mut body = Vec::new();

    // Lower each statement.
    for stmt in &bb.stmts {
        lower_statement(stmt, ctx, &mut body)?;
    }

    // Lower the terminator.
    lower_terminator(&bb.terminator, ctx, &mut body)?;

    tmir_block.body = body;
    Ok(tmir_block)
}

// ---------------------------------------------------------------------------
// Statement lowering
// ---------------------------------------------------------------------------

fn lower_statement(
    stmt: &Statement,
    ctx: &mut LoweringCtx<'_>,
    body: &mut Vec<InstrNode>,
) -> Result<(), BridgeError> {
    match stmt {
        Statement::Assign { place, rvalue, span: _ } => {
            lower_rvalue(place, rvalue, ctx, body)?;
        }
        Statement::Nop => {}
        _ => {
            return Err(BridgeError::UnsupportedOp("unknown statement variant".to_string()));
        }
    }
    Ok(())
}

fn lower_rvalue(
    dest: &Place,
    rvalue: &Rvalue,
    ctx: &mut LoweringCtx<'_>,
    body: &mut Vec<InstrNode>,
) -> Result<(), BridgeError> {
    // For simple locals (no projections), update the value mapping.
    // For projected places, emit store-like instructions.
    let dest_simple = dest.projections.is_empty();

    match rvalue {
        Rvalue::Use(operand) => {
            let src = ctx.resolve_operand(operand, body)?;
            if dest_simple {
                // Simple copy: emit a Copy instruction and update mapping.
                let ty = if let Ok(local_ty) = ctx.local_ty(dest.local) {
                    let local_ty = local_ty.clone();
                    ctx.map_type_ctx(&local_ty).unwrap_or(TmirTy::I64)
                } else {
                    TmirTy::I64
                };
                let result = ctx.fresh_value();
                body.push(InstrNode::new(Inst::Copy { ty, operand: src }).with_result(result));
                ctx.local_values.insert(dest.local, result);
            } else {
                // Projected assignment: emit InsertField/InsertElement.
                lower_projected_store(dest, src, ctx, body)?;
            }
        }
        Rvalue::BinaryOp(op, lhs, rhs) => {
            let lhs_val = ctx.resolve_operand(lhs, body)?;
            let rhs_val = ctx.resolve_operand(rhs, body)?;
            let signed = ctx.is_signed(dest.local);
            let ty =
                ctx.local_ty(dest.local).ok().and_then(|t| map_type(t).ok()).unwrap_or(TmirTy::I64);
            let result = ctx.fresh_value();

            match map_binop(*op, signed)? {
                BinOpMapping::Arith(tmir_op) => {
                    body.push(
                        InstrNode::new(Inst::BinOp { op: tmir_op, ty, lhs: lhs_val, rhs: rhs_val })
                            .with_result(result),
                    );
                }
                BinOpMapping::Cmp(icmp_op) => {
                    body.push(
                        InstrNode::new(Inst::ICmp { op: icmp_op, ty, lhs: lhs_val, rhs: rhs_val })
                            .with_result(result),
                    );
                }
            }

            if dest_simple {
                ctx.local_values.insert(dest.local, result);
            }
        }
        Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            // CheckedBinaryOp produces (result, overflow_flag). In tMIR this
            // is an Overflow instruction that produces two results.
            let lhs_val = ctx.resolve_operand(lhs, body)?;
            let rhs_val = ctx.resolve_operand(rhs, body)?;
            let overflow_op = map_checked_binop(*op)?;
            let ty = operand_tmir_type(lhs, ctx)?;

            let result = ctx.fresh_value();
            let overflow_flag = ctx.fresh_value();
            body.push(
                InstrNode::new(Inst::Overflow { op: overflow_op, ty, lhs: lhs_val, rhs: rhs_val })
                    .with_result(result)
                    .with_result(overflow_flag)
                    .with_proof(ProofAnnotation::NoOverflow),
            );

            if dest_simple {
                ctx.local_values.insert(dest.local, result);
            }
        }
        Rvalue::UnaryOp(op, operand) => {
            let src = ctx.resolve_operand(operand, body)?;
            let tmir_op = map_unop(*op)?;
            let ty =
                ctx.local_ty(dest.local).ok().and_then(|t| map_type(t).ok()).unwrap_or(TmirTy::I64);
            let result = ctx.fresh_value();
            body.push(
                InstrNode::new(Inst::UnOp { op: tmir_op, ty, operand: src }).with_result(result),
            );
            if dest_simple {
                ctx.local_values.insert(dest.local, result);
            }
        }
        Rvalue::Ref { mutable: _, place } => {
            // Reference creation: in tMIR, this is an address-of (Alloca-like).
            // Model as producing the address of the place.
            let src = ctx.resolve_place(place, body)?;
            // Use a Copy as a placeholder since tMIR doesn't have a direct
            // "address of local" instruction. The value semantically becomes a pointer.
            let result = ctx.fresh_value();
            body.push(
                InstrNode::new(Inst::Copy { ty: TmirTy::Ptr, operand: src }).with_result(result),
            );
            if dest_simple {
                ctx.local_values.insert(dest.local, result);
            }
        }
        Rvalue::AddressOf(_mutable, place) => {
            let src = ctx.resolve_place(place, body)?;
            let result = ctx.fresh_value();
            body.push(
                InstrNode::new(Inst::Copy { ty: TmirTy::Ptr, operand: src }).with_result(result),
            );
            if dest_simple {
                ctx.local_values.insert(dest.local, result);
            }
        }
        Rvalue::Cast(operand, target_ty) => {
            let src = ctx.resolve_operand(operand, body)?;
            let dst_tmir = ctx.map_type_ctx(target_ty)?;

            // Determine source type.
            let src_tmir = match operand {
                Operand::Copy(p) | Operand::Move(p) => {
                    ctx.local_ty(p.local).ok().and_then(|t| map_type(t).ok())
                }
                _ => None,
            }
            .unwrap_or(TmirTy::I64);

            let result = ctx.fresh_value();

            // Determine cast kind.
            let src_width = src_tmir.bit_width();
            let dst_width = dst_tmir.bit_width();
            let is_src_float = src_tmir.is_float();
            let is_dst_float = dst_tmir.is_float();

            let cast_op = match (is_src_float, is_dst_float) {
                (true, true) => {
                    // Float to float.
                    if src_width > dst_width { CastOp::FPTrunc } else { CastOp::FPExt }
                }
                (true, false) => {
                    // Float to int.
                    let signed = match operand {
                        Operand::Copy(p) | Operand::Move(p) => ctx.is_signed(p.local),
                        _ => true,
                    };
                    if signed { CastOp::FPToSI } else { CastOp::FPToUI }
                }
                (false, true) => {
                    // Int to float.
                    let signed = match operand {
                        Operand::Copy(p) | Operand::Move(p) => ctx.is_signed(p.local),
                        _ => true,
                    };
                    if signed { CastOp::SIToFP } else { CastOp::UIToFP }
                }
                (false, false) => {
                    // Int to int or ptr casts.
                    match (src_width, dst_width) {
                        (Some(sw), Some(dw)) if sw == dw => CastOp::Bitcast,
                        (Some(sw), Some(dw)) if sw > dw => CastOp::Trunc,
                        (Some(_), Some(_)) => {
                            let signed = match operand {
                                Operand::Copy(p) | Operand::Move(p) => ctx.is_signed(p.local),
                                _ => false,
                            };
                            if signed { CastOp::SExt } else { CastOp::ZExt }
                        }
                        _ => CastOp::Bitcast,
                    }
                }
            };

            body.push(
                InstrNode::new(Inst::Cast {
                    op: cast_op,
                    src_ty: src_tmir,
                    dst_ty: dst_tmir,
                    operand: src,
                })
                .with_result(result),
            );
            if dest_simple {
                ctx.local_values.insert(dest.local, result);
            }
        }
        Rvalue::Aggregate(kind, operands) => {
            // Build an aggregate from operands. Since tMIR doesn't have a direct
            // "aggregate construction" instruction, build it with InsertField.
            // Start with an Undef of the aggregate type, then insert each field.
            let ty =
                ctx.local_ty(dest.local).ok().and_then(|t| map_type(t).ok()).unwrap_or(TmirTy::Ptr);

            let mut current = ctx.fresh_value();
            body.push(InstrNode::new(Inst::Undef { ty }).with_result(current));

            for (i, operand) in operands.iter().enumerate() {
                let val = ctx.resolve_operand(operand, body)?;
                let new_val = ctx.fresh_value();
                body.push(
                    InstrNode::new(Inst::InsertField {
                        ty,
                        aggregate: current,
                        field: i as u32,
                        value: val,
                    })
                    .with_result(new_val),
                );
                current = new_val;
            }

            let _ = kind; // AggregateKind is informational only.
            if dest_simple {
                ctx.local_values.insert(dest.local, current);
            }
        }
        Rvalue::Discriminant(place) => {
            // Discriminant extraction: model as ExtractField(aggregate, 0)
            // since the discriminant is conceptually the "tag" field.
            let src = ctx.resolve_place(place, body)?;
            let result = ctx.fresh_value();
            body.push(
                InstrNode::new(Inst::ExtractField { ty: TmirTy::I64, aggregate: src, field: 0 })
                    .with_result(result),
            );
            if dest_simple {
                ctx.local_values.insert(dest.local, result);
            }
        }
        Rvalue::Len(place) => {
            // Len: model as ExtractField from a fat pointer (ptr, len).
            // Field 1 is conventionally the length.
            let src = ctx.resolve_place(place, body)?;
            let result = ctx.fresh_value();
            body.push(
                InstrNode::new(Inst::ExtractField { ty: TmirTy::I64, aggregate: src, field: 1 })
                    .with_result(result),
            );
            if dest_simple {
                ctx.local_values.insert(dest.local, result);
            }
        }
        Rvalue::Repeat(operand, count) => {
            // Array repetition [val; count]. Build as aggregate of `count` copies.
            let val = ctx.resolve_operand(operand, body)?;
            let ty =
                ctx.local_ty(dest.local).ok().and_then(|t| map_type(t).ok()).unwrap_or(TmirTy::Ptr);

            let mut current = ctx.fresh_value();
            body.push(InstrNode::new(Inst::Undef { ty }).with_result(current));

            for i in 0..*count {
                let idx = ctx.fresh_value();
                body.push(
                    InstrNode::new(Inst::Const {
                        ty: TmirTy::I64,
                        value: TmirConstant::Int(i as i128),
                    })
                    .with_result(idx),
                );
                let new_val = ctx.fresh_value();
                body.push(
                    InstrNode::new(Inst::InsertElement {
                        ty,
                        array: current,
                        index: idx,
                        value: val,
                    })
                    .with_result(new_val),
                );
                current = new_val;
            }

            if dest_simple {
                ctx.local_values.insert(dest.local, current);
            }
        }
        Rvalue::CopyForDeref(place) => {
            let src = ctx.resolve_place(place, body)?;
            let result = ctx.fresh_value();
            body.push(
                InstrNode::new(Inst::Copy { ty: TmirTy::Ptr, operand: src }).with_result(result),
            );
            if dest_simple {
                ctx.local_values.insert(dest.local, result);
            }
        }
        _ => {
            return Err(BridgeError::UnsupportedOp("unknown rvalue variant".to_string()));
        }
    }
    Ok(())
}

/// Lower a projected store (assignment to a place with projections).
fn lower_projected_store(
    dest: &Place,
    value: ValueId,
    ctx: &mut LoweringCtx<'_>,
    body: &mut Vec<InstrNode>,
) -> Result<(), BridgeError> {
    if dest.projections.len() == 1 {
        match &dest.projections[0] {
            Projection::Field(idx) => {
                let agg = ctx.local_value(dest.local)?;
                let ty = ctx
                    .local_ty(dest.local)
                    .ok()
                    .and_then(|t| map_type(t).ok())
                    .unwrap_or(TmirTy::Ptr);
                let result = ctx.fresh_value();
                body.push(
                    InstrNode::new(Inst::InsertField {
                        ty,
                        aggregate: agg,
                        field: *idx as u32,
                        value,
                    })
                    .with_result(result),
                );
                ctx.local_values.insert(dest.local, result);
            }
            Projection::Deref => {
                // Store through pointer.
                let ptr = ctx.local_value(dest.local)?;
                body.push(InstrNode::new(Inst::Store {
                    ty: TmirTy::I64, // conservative
                    ptr,
                    value,
                }));
            }
            _ => {
                return Err(BridgeError::UnsupportedOp(format!(
                    "projected store with {:?}",
                    dest.projections[0]
                )));
            }
        }
    } else {
        return Err(BridgeError::UnsupportedOp(format!(
            "multi-level projected store ({} projections)",
            dest.projections.len()
        )));
    }
    Ok(())
}

/// Determine the tMIR type of an operand.
fn operand_tmir_type(op: &Operand, ctx: &LoweringCtx<'_>) -> Result<TmirTy, BridgeError> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => {
            let ty = ctx.local_ty(p.local)?;
            map_type(ty)
        }
        Operand::Constant(cv) => match cv {
            ConstValue::Bool(_) => Ok(TmirTy::Bool),
            ConstValue::Int(_) => Ok(TmirTy::I64),
            ConstValue::Uint(_, w) => match w {
                8 => Ok(TmirTy::I8),
                16 => Ok(TmirTy::I16),
                32 => Ok(TmirTy::I32),
                64 => Ok(TmirTy::I64),
                128 => Ok(TmirTy::I128),
                _ => Err(BridgeError::UnsupportedType(format!("u{w}"))),
            },
            ConstValue::Float(_) => Ok(TmirTy::F64),
            ConstValue::Unit => Ok(TmirTy::Void),
            _ => Err(BridgeError::UnsupportedType("unknown const".to_string())),
        },
        _ => Ok(TmirTy::I64),
    }
}

// ---------------------------------------------------------------------------
// Terminator lowering
// ---------------------------------------------------------------------------

fn lower_terminator(
    term: &Terminator,
    ctx: &mut LoweringCtx<'_>,
    body: &mut Vec<InstrNode>,
) -> Result<(), BridgeError> {
    match term {
        Terminator::Goto(target) => {
            body.push(InstrNode::new(Inst::Br {
                target: TmirBlockId::new(target.0 as u32),
                args: vec![],
            }));
        }
        Terminator::Return => {
            // Return the value in local 0 (return slot) if the function has a
            // non-void return type.
            let ret_vals = if let Ok(val) = ctx.local_value(0) { vec![val] } else { vec![] };
            body.push(InstrNode::new(Inst::Return { values: ret_vals }));
        }
        Terminator::Unreachable => {
            body.push(InstrNode::new(Inst::Unreachable));
        }
        Terminator::SwitchInt { discr, targets, otherwise, span: _ } => {
            let discr_val = ctx.resolve_operand(discr, body)?;

            if targets.len() == 1 {
                // Binary branch: emit CondBr.
                let (value, target) = &targets[0];
                // Compare discr == value.
                let const_val = ctx.fresh_value();
                body.push(
                    InstrNode::new(Inst::Const {
                        ty: TmirTy::I64,
                        value: TmirConstant::Int(*value as i128),
                    })
                    .with_result(const_val),
                );
                let cmp_val = ctx.fresh_value();
                body.push(
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: TmirTy::I64,
                        lhs: discr_val,
                        rhs: const_val,
                    })
                    .with_result(cmp_val),
                );
                body.push(InstrNode::new(Inst::CondBr {
                    cond: cmp_val,
                    then_target: TmirBlockId::new(target.0 as u32),
                    then_args: vec![],
                    else_target: TmirBlockId::new(otherwise.0 as u32),
                    else_args: vec![],
                }));
            } else {
                // Multi-way switch.
                let cases: Vec<SwitchCase> = targets
                    .iter()
                    .map(|(val, blk)| SwitchCase {
                        value: TmirConstant::Int(*val as i128),
                        target: TmirBlockId::new(blk.0 as u32),
                        args: vec![],
                    })
                    .collect();
                body.push(InstrNode::new(Inst::Switch {
                    value: discr_val,
                    default: TmirBlockId::new(otherwise.0 as u32),
                    default_args: vec![],
                    cases,
                }));
            }
        }
        Terminator::Assert { cond, expected, msg, target, span: _ } => {
            let cond_val = ctx.resolve_operand(cond, body)?;

            // Emit the assertion. If expected is false, negate the condition.
            let assert_val = if *expected {
                cond_val
            } else {
                let negated = ctx.fresh_value();
                body.push(
                    InstrNode::new(Inst::UnOp {
                        op: TmirUnOp::Not,
                        ty: TmirTy::Bool,
                        operand: cond_val,
                    })
                    .with_result(negated),
                );
                negated
            };

            // Emit tMIR Assert (assertion must hold).
            let desc = format_assert_message(msg);
            body.push(
                InstrNode::new(Inst::Assert { cond: assert_val })
                    .with_proof(ProofAnnotation::NoOverflow),
            );

            // Add a proof obligation for this assertion.
            ctx.add_obligation(ObligationKind::PanicFreedom, desc);

            // Branch to continuation.
            body.push(InstrNode::new(Inst::Br {
                target: TmirBlockId::new(target.0 as u32),
                args: vec![],
            }));
        }
        Terminator::Call { func: callee, args, dest, target, atomic, span: _ } => {
            // Handle atomic operations specially.
            if let Some(atomic_op) = atomic {
                lower_atomic_call(atomic_op, ctx, body)?;
            } else {
                // Regular call. tMIR uses FuncId for calls, but we don't have
                // a function table here. Use CallIndirect with a placeholder,
                // or emit as a Call with a synthetic FuncId.
                let mut arg_vals = Vec::with_capacity(args.len());
                for arg in args {
                    arg_vals.push(ctx.resolve_operand(arg, body)?);
                }

                // Use a deterministic FuncId based on the callee name hash.
                // In a real multi-function module, the caller would build a name->FuncId map.
                let callee_id = FuncId::new(hash_name(callee));
                let dest_val = ctx.resolve_place(dest, body)?;

                body.push(
                    InstrNode::new(Inst::Call { callee: callee_id, args: arg_vals })
                        .with_result(dest_val),
                );
            }

            // Jump to continuation if present.
            if let Some(cont) = target {
                body.push(InstrNode::new(Inst::Br {
                    target: TmirBlockId::new(cont.0 as u32),
                    args: vec![],
                }));
            }
        }
        Terminator::Drop { target, .. } => {
            // Drop is a cleanup operation. In tMIR, model as a branch to target.
            body.push(InstrNode::new(Inst::Br {
                target: TmirBlockId::new(target.0 as u32),
                args: vec![],
            }));
        }
        _ => {
            return Err(BridgeError::UnsupportedOp("unknown terminator variant".to_string()));
        }
    }
    Ok(())
}

/// Lower an atomic operation to tMIR atomic instructions.
fn lower_atomic_call(
    atomic: &AtomicOperation,
    ctx: &mut LoweringCtx<'_>,
    body: &mut Vec<InstrNode>,
) -> Result<(), BridgeError> {
    let ptr = ctx.resolve_place(&atomic.place, body)?;
    let ordering = map_ordering(&atomic.ordering);

    match atomic.op_kind {
        AtomicOpKind::Load => {
            let result = if let Some(dest) = &atomic.dest {
                ctx.resolve_place(dest, body)?
            } else {
                ctx.fresh_value()
            };
            body.push(
                InstrNode::new(Inst::AtomicLoad { ty: TmirTy::I64, ptr, ordering })
                    .with_result(result)
                    .with_proof(ProofAnnotation::DataRaceFree),
            );
        }
        AtomicOpKind::Store => {
            // The value to store would be in the args of the call.
            // Since we're working from AtomicOperation metadata, use a
            // placeholder value.
            let val = ctx.fresh_value();
            body.push(
                InstrNode::new(Inst::Const { ty: TmirTy::I64, value: TmirConstant::Int(0) })
                    .with_result(val),
            );
            body.push(
                InstrNode::new(Inst::AtomicStore { ty: TmirTy::I64, ptr, value: val, ordering })
                    .with_proof(ProofAnnotation::DataRaceFree),
            );
        }
        AtomicOpKind::Fence | AtomicOpKind::CompilerFence => {
            body.push(
                InstrNode::new(Inst::Fence { ordering }).with_proof(ProofAnnotation::DataRaceFree),
            );
        }
        AtomicOpKind::CompareExchange | AtomicOpKind::CompareExchangeWeak => {
            let failure_ordering =
                atomic.failure_ordering.as_ref().map(map_ordering).unwrap_or(TmirOrdering::Relaxed);
            let expected = ctx.fresh_value();
            let desired = ctx.fresh_value();
            body.push(
                InstrNode::new(Inst::Const { ty: TmirTy::I64, value: TmirConstant::Int(0) })
                    .with_result(expected),
            );
            body.push(
                InstrNode::new(Inst::Const { ty: TmirTy::I64, value: TmirConstant::Int(0) })
                    .with_result(desired),
            );
            let result = ctx.fresh_value();
            body.push(
                InstrNode::new(Inst::CmpXchg {
                    ty: TmirTy::I64,
                    ptr,
                    expected,
                    desired,
                    success: ordering,
                    failure: failure_ordering,
                })
                .with_result(result)
                .with_proof(ProofAnnotation::DataRaceFree),
            );
        }
        kind if kind.is_rmw() => {
            let rmw_op = map_atomic_rmw_op(&kind)?;
            let val = ctx.fresh_value();
            body.push(
                InstrNode::new(Inst::Const { ty: TmirTy::I64, value: TmirConstant::Int(0) })
                    .with_result(val),
            );
            let result = ctx.fresh_value();
            body.push(
                InstrNode::new(Inst::AtomicRMW {
                    op: rmw_op,
                    ty: TmirTy::I64,
                    ptr,
                    value: val,
                    ordering,
                })
                .with_result(result)
                .with_proof(ProofAnnotation::DataRaceFree),
            );
        }
        _ => {
            return Err(BridgeError::UnsupportedOp(format!(
                "atomic op kind: {:?}",
                atomic.op_kind
            )));
        }
    }
    Ok(())
}

/// Map trust-types `AtomicOpKind` to tMIR `AtomicRMWOp`.
fn map_atomic_rmw_op(kind: &AtomicOpKind) -> Result<tmir::inst::AtomicRMWOp, BridgeError> {
    use tmir::inst::AtomicRMWOp;

    match kind {
        AtomicOpKind::Exchange => Ok(AtomicRMWOp::Xchg),
        AtomicOpKind::FetchAdd => Ok(AtomicRMWOp::Add),
        AtomicOpKind::FetchSub => Ok(AtomicRMWOp::Sub),
        AtomicOpKind::FetchAnd => Ok(AtomicRMWOp::And),
        AtomicOpKind::FetchOr => Ok(AtomicRMWOp::Or),
        AtomicOpKind::FetchXor => Ok(AtomicRMWOp::Xor),
        AtomicOpKind::FetchMin => Ok(AtomicRMWOp::Min),
        AtomicOpKind::FetchMax => Ok(AtomicRMWOp::Max),
        AtomicOpKind::FetchNand => {
            // tMIR doesn't have Nand; approximate as Xor (documented gap).
            Ok(AtomicRMWOp::Xor)
        }
        _ => Err(BridgeError::UnsupportedOp(format!("atomic RMW op: {kind:?}"))),
    }
}

/// Format an assert message for proof obligation description.
fn format_assert_message(msg: &AssertMessage) -> String {
    match msg {
        AssertMessage::BoundsCheck => "array bounds check".to_string(),
        AssertMessage::Overflow(op) => format!("overflow on {op:?}"),
        AssertMessage::OverflowNeg => "overflow on negation".to_string(),
        AssertMessage::DivisionByZero => "division by zero".to_string(),
        AssertMessage::RemainderByZero => "remainder by zero".to_string(),
        AssertMessage::ResumedAfterReturn => "resumed after return".to_string(),
        AssertMessage::ResumedAfterPanic => "resumed after panic".to_string(),
        AssertMessage::ResumedAfterDrop => "resumed after drop".to_string(),
        AssertMessage::MisalignedPointerDereference => "misaligned pointer dereference".to_string(),
        AssertMessage::NullPointerDereference => "null pointer dereference".to_string(),
        AssertMessage::InvalidEnumConstruction => "invalid enum construction".to_string(),
        AssertMessage::Custom(s) => s.clone(),
        _ => "unknown assertion".to_string(),
    }
}

/// Simple hash of a function name for FuncId assignment.
fn hash_name(name: &str) -> u32 {
    let mut h: u32 = 0;
    for byte in name.bytes() {
        h = h.wrapping_mul(31).wrapping_add(u32::from(byte));
    }
    h
}
