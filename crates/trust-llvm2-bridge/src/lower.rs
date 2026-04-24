//! Lowering from trust-types IR to LLVM2 LIR.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::BridgeError;
use crate::mapping::{
    deref_type, downcast_type, element_type, field_type, is_trivially_copy_ty, map_atomic_ordering,
    map_atomic_rmw_op, map_binop, map_float_binop, map_type, map_unop,
};
use llvm2_lower::function::{
    BasicBlock as LirBlock, Function as LirFunction, Signature, StackSlotInfo,
};
use llvm2_lower::instructions::{Block, Instruction, IntCC, Opcode, Value};
use llvm2_lower::types::Type as LirType;
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    AggregateKind, AtomicOpKind, BasicBlock as TrustBlock, BinOp, ConstValue, LocalDecl, Operand,
    Place, Projection, Rvalue, Statement, Terminator, Ty, UnOp, VerifiableBody, VerifiableFunction,
};

const ABORT_SYMBOL: &str = "abort";

#[derive(Clone, Debug)]
struct BlockParam {
    local: usize,
    value: Value,
    ty: LirType,
}

/// Internal state for the lowering pass.
struct LoweringCtx<'a> {
    /// Local variable declarations from the trust-types body.
    locals: &'a [LocalDecl],
    /// Map from trust-types local index to LIR Value.
    local_values: FxHashMap<usize, Value>,
    /// Type hints for Values whose producing opcode omits result type metadata.
    value_types: std::collections::HashMap<Value, LirType>,
    /// Next available Value id.
    next_value: u32,
    /// Stack slots allocated for memory operations (aggregates, address-of, etc.).
    stack_slots: Vec<StackSlotInfo>,
    /// Map from trust-types local index to stack slot index (for locals that
    /// need an address, e.g., aggregates or locals whose address is taken).
    local_stack_slots: FxHashMap<usize, u32>,
    /// Lazily-allocated panic block ID for Assert terminators.
    /// Set on first use; the block is inserted into the function after lowering.
    panic_block: Option<Block>,
    /// Synthetic edge blocks used to materialize block-param copies on
    /// conditional control-flow edges.
    pending_blocks: Vec<(Block, LirBlock)>,
    /// Next available block ID (tracks the highest block ID seen + 1).
    next_block_id: u32,
}

impl<'a> LoweringCtx<'a> {
    fn new(locals: &'a [LocalDecl], arg_count: usize, max_block_id: u32) -> Self {
        let mut ctx = Self {
            locals,
            local_values: FxHashMap::with_capacity_and_hasher(locals.len(), Default::default()),
            value_types: std::collections::HashMap::new(),
            next_value: 0,
            stack_slots: Vec::new(),
            local_stack_slots: FxHashMap::default(),
            panic_block: None,
            pending_blocks: Vec::new(),
            next_block_id: max_block_id + 1,
        };
        // LLVM2 ISel convention: Value(0)..Value(arg_count-1) are formal arguments.
        // Trust-types convention: local 0 is the return slot, locals 1..=arg_count are args.
        // Assign argument locals first to match ISel expectations.
        for i in 1..=arg_count {
            if let Some(local) = locals.iter().find(|l| l.index == i) {
                let val = Value(ctx.next_value);
                ctx.next_value += 1;
                ctx.local_values.insert(local.index, val);
            }
        }
        // Then assign remaining locals (return slot at index 0, and any others).
        for local in locals {
            if !ctx.local_values.contains_key(&local.index) {
                let val = Value(ctx.next_value);
                ctx.next_value += 1;
                ctx.local_values.insert(local.index, val);
            }
        }
        ctx
    }

    /// Allocate a fresh temporary Value.
    fn fresh_value(&mut self) -> Value {
        let v = Value(self.next_value);
        self.next_value += 1;
        v
    }

    /// Get the LIR Value for a trust-types local index.
    fn local_value(&self, index: usize) -> Result<Value, BridgeError> {
        self.local_values.get(&index).copied().ok_or(BridgeError::MissingLocal(index))
    }

    /// Record a type hint for a Value whose opcode omits typed results.
    fn record_value_type(&mut self, value: Value, ty: LirType) {
        self.value_types.insert(value, ty);
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
        self.local_ty(index).map(|ty| ty.is_signed()).unwrap_or(false)
    }

    /// Get the fully-projected type of a place.
    fn place_ty(&self, place: &Place) -> Result<Ty, BridgeError> {
        let mut current_ty = self.local_ty(place.local)?.clone();

        for proj in &place.projections {
            current_ty = match proj {
                Projection::Field(field_idx) => field_type(&current_ty, *field_idx)?,
                Projection::Deref => deref_type(&current_ty)?,
                Projection::Index(_) | Projection::ConstantIndex { .. } => {
                    element_type(&current_ty)?
                }
                Projection::Downcast(variant_idx) => downcast_type(&current_ty, *variant_idx)?,
                Projection::Subslice { .. } => {
                    Ty::Slice { elem: Box::new(element_type(&current_ty)?) }
                }
                other => {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "unsupported projection in place_ty: {other:?}"
                    )));
                }
            };
        }

        Ok(current_ty)
    }

    /// Get the LIR pointee type for an atomic pointer operand.
    fn atomic_lir_ty(&self, place: &Place) -> Result<LirType, BridgeError> {
        let ptr_ty = self.place_ty(place)?;
        let pointee_ty = ptr_ty.pointee_ty().ok_or_else(|| {
            BridgeError::UnsupportedOp(format!(
                "atomic pointer operand is not pointer-like: {ptr_ty:?}"
            ))
        })?;
        map_type(pointee_ty)
    }

    /// Get the bit width of a type (for cast width comparisons).
    fn ty_bit_width(ty: &Ty) -> Option<u32> {
        match ty {
            Ty::Bool => Some(1),
            Ty::Int { width, .. } => Some(*width),
            Ty::Bv(w) => Some(*w),
            _ => None,
        }
    }

    fn next_wider_int_lir_ty(ty: &Ty) -> Option<LirType> {
        match ty.int_width()? {
            8 => Some(LirType::I16),
            16 => Some(LirType::I32),
            32 => Some(LirType::I64),
            64 => Some(LirType::I128),
            _ => None,
        }
    }

    /// Allocate a stack slot and return its index.
    fn alloc_stack_slot(&mut self, ty: &LirType) -> u32 {
        let slot = self.stack_slots.len() as u32;
        self.stack_slots.push(StackSlotInfo { size: ty.bytes(), align: ty.align() });
        slot
    }

    /// Ensure a local has an associated stack slot, returning the slot index.
    fn ensure_local_stack_slot(&mut self, local_idx: usize) -> Result<u32, BridgeError> {
        if let Some(&slot) = self.local_stack_slots.get(&local_idx) {
            return Ok(slot);
        }
        let ty = self.local_ty(local_idx)?;
        let lir_ty = map_lowering_type(ty)?;
        let slot = self.alloc_stack_slot(&lir_ty);
        self.local_stack_slots.insert(local_idx, slot);
        Ok(slot)
    }

    /// Get or create the panic block used by Assert terminators.
    ///
    /// Returns the Block id. The actual block (containing just an abort call) is
    /// inserted into the function's block map by `lower_body_to_lir` after
    /// all blocks are lowered.
    fn get_or_create_panic_block(&mut self) -> Block {
        if let Some(blk) = self.panic_block {
            return blk;
        }
        let blk = Block(self.next_block_id);
        self.next_block_id += 1;
        self.panic_block = Some(blk);
        blk
    }

    /// Allocate a fresh synthetic block ID.
    fn fresh_block(&mut self) -> Block {
        let blk = Block(self.next_block_id);
        self.next_block_id += 1;
        blk
    }

    /// Emit a StackAddr instruction for a stack slot and return the pointer Value.
    fn emit_stack_addr(&mut self, slot: u32, instructions: &mut Vec<Instruction>) -> Value {
        let ptr = self.fresh_value();
        instructions.push(Instruction {
            opcode: Opcode::StackAddr { slot },
            args: vec![],
            results: vec![ptr],
        });
        ptr
    }

    /// Resolve an Operand to a LIR Value, emitting Iconst/Fconst as needed.
    fn resolve_operand(
        &mut self,
        op: &Operand,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self.resolve_place(place, instructions),
            Operand::Constant(cv) => self.emit_const(cv, instructions),
            Operand::Symbolic(_) => Err(BridgeError::UnsupportedOp(
                "Symbolic operands not supported in LIR lowering".to_string(),
            )),
            _ => Err(BridgeError::UnsupportedOp("unknown operand variant".to_string())),
        }
    }

    /// Resolve a Place to a LIR Value.
    ///
    /// For simple locals (no projections), returns the Value directly.
    /// For projected places (Field, Deref, Index), emits StructGep/Load
    /// instructions to compute the final value.
    fn resolve_place(
        &mut self,
        place: &Place,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        if place.projections.is_empty() {
            return self.local_value(place.local);
        }

        // Start with the base local's address. If it's an aggregate with a
        // stack slot, use StackAddr; otherwise treat the local value as a pointer.
        let mut current_val = if let Some(&slot) = self.local_stack_slots.get(&place.local) {
            self.emit_stack_addr(slot, instructions)
        } else {
            self.local_value(place.local)?
        };

        // Track the current type through projections so we know field types.
        let base_ty = self.local_ty(place.local)?.clone();
        let mut current_ty = base_ty;

        for proj in &place.projections {
            match proj {
                Projection::Field(field_idx) => {
                    let lir_struct_ty = map_type(&current_ty)?;
                    let result = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::StructGep {
                            struct_ty: lir_struct_ty,
                            field_index: *field_idx as u32,
                        },
                        args: vec![current_val],
                        results: vec![result],
                    });
                    // Load the field value.
                    let field_ty = field_type(&current_ty, *field_idx)?;
                    let lir_field_ty = map_type(&field_ty)?;
                    let loaded = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Load { ty: lir_field_ty },
                        args: vec![result],
                        results: vec![loaded],
                    });
                    current_val = loaded;
                    current_ty = field_ty;
                }
                Projection::Deref => {
                    // Dereference a pointer/reference: emit a Load.
                    let pointee_ty = deref_type(&current_ty)?;
                    let lir_pointee = map_type(&pointee_ty)?;
                    let loaded = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Load { ty: lir_pointee },
                        args: vec![current_val],
                        results: vec![loaded],
                    });
                    current_val = loaded;
                    current_ty = pointee_ty;
                }
                Projection::Index(idx_local) => {
                    // Index into an array/slice: ptr + idx * elem_size.
                    let elem_ty = element_type(&current_ty)?;
                    let lir_elem = map_type(&elem_ty)?;
                    let elem_size = lir_elem.bytes();

                    let idx_val = self.local_value(*idx_local)?;
                    // Emit: offset = idx * elem_size
                    let size_const = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(elem_size) },
                        args: vec![],
                        results: vec![size_const],
                    });
                    let offset = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Imul,
                        args: vec![idx_val, size_const],
                        results: vec![offset],
                    });
                    // Emit: addr = base + offset
                    let addr = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![current_val, offset],
                        results: vec![addr],
                    });
                    // Load the element.
                    let loaded = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Load { ty: lir_elem },
                        args: vec![addr],
                        results: vec![loaded],
                    });
                    current_val = loaded;
                    current_ty = elem_ty;
                }
                Projection::Downcast(variant_idx) => {
                    // Downcast: select a variant of an enum. At the MIR level this
                    // is just a type-level marker. The actual data pointer is the same.
                    // We update the type tracking but don't emit instructions.
                    current_ty = downcast_type(&current_ty, *variant_idx)?;
                }
                Projection::ConstantIndex { offset, from_end } => {
                    let elem_ty = element_type(&current_ty)?;
                    let lir_elem = map_type(&elem_ty)?;
                    let elem_size = lir_elem.bytes();

                    // tRust: #828 — support ConstantIndex from_end for fixed-size arrays.
                    let byte_offset = if *from_end {
                        match &current_ty {
                            Ty::Array { len, .. } => (*len - *offset as u64) as u32 * elem_size,
                            _ => {
                                return Err(BridgeError::UnsupportedOp(
                                    "ConstantIndex from_end not yet supported".to_string(),
                                ));
                            }
                        }
                    } else {
                        (*offset as u32) * elem_size
                    };
                    let offset_const = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(byte_offset) },
                        args: vec![],
                        results: vec![offset_const],
                    });
                    let addr = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![current_val, offset_const],
                        results: vec![addr],
                    });
                    let loaded = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Load { ty: lir_elem },
                        args: vec![addr],
                        results: vec![loaded],
                    });
                    current_val = loaded;
                    current_ty = elem_ty;
                }
                Projection::Subslice { from, to: _, from_end: _ } => {
                    // tRust: #828 — lower subslice by advancing the base pointer and
                    // tracking the projected type as a slice.
                    let elem_ty = element_type(&current_ty)?;
                    let lir_elem = map_type(&elem_ty)?;
                    let elem_size = lir_elem.bytes();
                    let byte_offset = (*from as u32) * elem_size;
                    let offset_const = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(byte_offset) },
                        args: vec![],
                        results: vec![offset_const],
                    });
                    let start_addr = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![current_val, offset_const],
                        results: vec![start_addr],
                    });
                    current_val = start_addr;
                    current_ty = Ty::Slice { elem: Box::new(elem_ty) };
                }
                other => {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "unsupported projection: {other:?}"
                    )));
                }
            }
        }
        Ok(current_val)
    }

    /// Resolve a Place to a pointer Value (address) rather than loading.
    ///
    /// Used by Ref and AddressOf rvalues that need the address of a place.
    fn resolve_place_addr(
        &mut self,
        place: &Place,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        // Ensure the base local has a stack slot.
        let slot = self.ensure_local_stack_slot(place.local)?;
        let mut current_val = self.emit_stack_addr(slot, instructions);

        if place.projections.is_empty() {
            return Ok(current_val);
        }

        let base_ty = self.local_ty(place.local)?.clone();
        let mut current_ty = base_ty;

        for proj in &place.projections {
            match proj {
                Projection::Field(field_idx) => {
                    let lir_struct_ty = map_type(&current_ty)?;
                    let result = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::StructGep {
                            struct_ty: lir_struct_ty,
                            field_index: *field_idx as u32,
                        },
                        args: vec![current_val],
                        results: vec![result],
                    });
                    current_val = result;
                    current_ty = field_type(&current_ty, *field_idx)?;
                }
                Projection::Deref => {
                    // Load the pointer, then the result is the address.
                    let pointee_ty = deref_type(&current_ty)?;
                    let loaded = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Load { ty: LirType::I64 },
                        args: vec![current_val],
                        results: vec![loaded],
                    });
                    current_val = loaded;
                    current_ty = pointee_ty;
                }
                Projection::Index(idx_local) => {
                    let elem_ty = element_type(&current_ty)?;
                    let lir_elem = map_type(&elem_ty)?;
                    let elem_size = lir_elem.bytes();

                    let idx_val = self.local_value(*idx_local)?;
                    let size_const = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(elem_size) },
                        args: vec![],
                        results: vec![size_const],
                    });
                    let offset = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Imul,
                        args: vec![idx_val, size_const],
                        results: vec![offset],
                    });
                    let addr = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![current_val, offset],
                        results: vec![addr],
                    });
                    current_val = addr;
                    current_ty = elem_ty;
                }
                Projection::Downcast(variant_idx) => {
                    current_ty = downcast_type(&current_ty, *variant_idx)?;
                }
                // tRust: #828 — support ConstantIndex in address-of lowering too.
                Projection::ConstantIndex { offset, from_end } => {
                    let elem_ty = element_type(&current_ty)?;
                    let lir_elem = map_type(&elem_ty)?;
                    let elem_size = lir_elem.bytes();
                    let actual_offset = if *from_end {
                        match &current_ty {
                            Ty::Array { len, .. } => (*len - *offset as u64) as u32 * elem_size,
                            _ => {
                                return Err(BridgeError::UnsupportedOp(
                                    "ConstantIndex from_end on non-array in addr context"
                                        .to_string(),
                                ));
                            }
                        }
                    } else {
                        (*offset as u32) * elem_size
                    };
                    let offset_const = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(actual_offset) },
                        args: vec![],
                        results: vec![offset_const],
                    });
                    let addr = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![current_val, offset_const],
                        results: vec![addr],
                    });
                    current_val = addr;
                    current_ty = elem_ty;
                }
                // tRust: #828 — allow address-of on subslices by advancing to the
                // projected start and preserving slice typing.
                Projection::Subslice { from, to: _, from_end: _ } => {
                    let elem_ty = element_type(&current_ty)?;
                    let lir_elem = map_type(&elem_ty)?;
                    let elem_size = lir_elem.bytes();
                    let byte_offset = (*from as u32) * elem_size;
                    let offset_const = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(byte_offset) },
                        args: vec![],
                        results: vec![offset_const],
                    });
                    let addr = self.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![current_val, offset_const],
                        results: vec![addr],
                    });
                    current_val = addr;
                    current_ty = Ty::Slice { elem: Box::new(elem_ty) };
                }
                other => {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "address-of projection not supported: {other:?}"
                    )));
                }
            }
        }
        Ok(current_val)
    }

    /// Emit an Iconst or Fconst instruction and return its result Value.
    fn emit_const(
        &mut self,
        cv: &ConstValue,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        let (opcode, result) = match cv {
            ConstValue::Bool(b) => {
                let v = self.fresh_value();
                let opcode = Opcode::Iconst { ty: LirType::B1, imm: i64::from(*b) };
                (opcode, v)
            }
            ConstValue::Int(val) => {
                let v = self.fresh_value();
                // tRust: #826 — infer the narrowest signed LIR type from value range.
                let ty = match *val {
                    -128..=127 => LirType::I8,
                    -32_768..=32_767 => LirType::I16,
                    -2_147_483_648..=2_147_483_647 => LirType::I32,
                    _ => LirType::I64,
                };
                let opcode = Opcode::Iconst { ty, imm: *val as i64 };
                (opcode, v)
            }
            ConstValue::Uint(val, width) => {
                let v = self.fresh_value();
                let ty = match width {
                    8 => LirType::I8,
                    16 => LirType::I16,
                    32 => LirType::I32,
                    64 => LirType::I64,
                    128 => LirType::I128,
                    _ => return Err(BridgeError::UnsupportedType(format!("u{width}"))),
                };
                let opcode = Opcode::Iconst { ty, imm: *val as i64 };
                (opcode, v)
            }
            ConstValue::Float(val) => {
                let v = self.fresh_value();
                let opcode = Opcode::Fconst { ty: LirType::F64, imm: *val };
                (opcode, v)
            }
            ConstValue::Unit => {
                // Unit is zero-sized; emit a B1 const 0 as placeholder.
                let v = self.fresh_value();
                let opcode = Opcode::Iconst { ty: LirType::B1, imm: 0 };
                (opcode, v)
            }
            _ => {
                return Err(BridgeError::UnsupportedOp("unknown constant variant".to_string()));
            }
        };
        instructions.push(Instruction { opcode, args: vec![], results: vec![result] });
        Ok(result)
    }
}

fn return_args(ctx: &LoweringCtx<'_>, has_return_value: bool) -> Result<Vec<Value>, BridgeError> {
    if has_return_value { Ok(vec![ctx.local_value(0)?]) } else { Ok(vec![]) }
}

fn abort_call_instruction() -> Instruction {
    Instruction {
        opcode: Opcode::Call { name: ABORT_SYMBOL.to_string() },
        args: vec![],
        results: vec![],
    }
}

fn is_fieldless_adt(ty: &Ty) -> bool {
    matches!(ty, Ty::Adt { fields, .. } if fields.is_empty())
}

fn map_lowering_type(ty: &Ty) -> Result<LirType, BridgeError> {
    if is_fieldless_adt(ty) { Ok(LirType::I64) } else { map_type(ty) }
}

fn infer_int_const_ty(val: i128) -> Ty {
    match val {
        -128..=127 => Ty::i8(),
        -32_768..=32_767 => Ty::i16(),
        -2_147_483_648..=2_147_483_647 => Ty::i32(),
        -9_223_372_036_854_775_808..=9_223_372_036_854_775_807 => Ty::i64(),
        _ => Ty::i128(),
    }
}

fn operand_ty(ctx: &LoweringCtx<'_>, operand: &Operand) -> Result<Ty, BridgeError> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => ctx.place_ty(place),
        Operand::Constant(ConstValue::Bool(_)) => Ok(Ty::Bool),
        Operand::Constant(ConstValue::Int(val)) => Ok(infer_int_const_ty(*val)),
        Operand::Constant(ConstValue::Uint(_, width)) => {
            Ok(Ty::Int { width: *width, signed: false })
        }
        Operand::Constant(ConstValue::Float(_)) => Ok(Ty::f64_ty()),
        Operand::Constant(ConstValue::Unit) => Ok(Ty::Unit),
        Operand::Symbolic(_) => Err(BridgeError::UnsupportedOp(
            "symbolic operand type inference not supported".to_string(),
        )),
        _ => Err(BridgeError::UnsupportedOp("unknown operand variant".to_string())),
    }
}

fn checked_binary_value_ty(ctx: &LoweringCtx<'_>, dest: &Place) -> Result<Ty, BridgeError> {
    match ctx.place_ty(dest)? {
        Ty::Tuple(fields) if fields.len() == 2 && fields[1] == Ty::Bool => Ok(fields[0].clone()),
        other => Err(BridgeError::InvalidMir(format!(
            "CheckedBinaryOp destination must be a 2-field tuple ending in bool, got place type {other:?}"
        ))),
    }
}

fn next_wider_int_type(ty: &LirType) -> Option<LirType> {
    match ty {
        LirType::I8 => Some(LirType::I16),
        LirType::I16 => Some(LirType::I32),
        LirType::I32 => Some(LirType::I64),
        LirType::I64 => Some(LirType::I128),
        _ => None,
    }
}

fn integer_type_for_bits(bits: u32) -> Result<LirType, BridgeError> {
    match bits {
        1 => Ok(LirType::B1),
        8 => Ok(LirType::I8),
        16 => Ok(LirType::I16),
        32 => Ok(LirType::I32),
        64 => Ok(LirType::I64),
        128 => Ok(LirType::I128),
        _ => Err(BridgeError::UnsupportedType(format!("integer width {bits}"))),
    }
}

fn emit_iconst(
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
    ty: LirType,
    imm: i64,
) -> Value {
    let value = ctx.fresh_value();
    instructions.push(Instruction {
        opcode: Opcode::Iconst { ty, imm },
        args: vec![],
        results: vec![value],
    });
    value
}

fn emit_binary_inst(
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
    opcode: Opcode,
    lhs: Value,
    rhs: Value,
) -> Value {
    let result = ctx.fresh_value();
    instructions.push(Instruction { opcode, args: vec![lhs, rhs], results: vec![result] });
    result
}

fn emit_int_cast(
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
    value: Value,
    from_ty: &LirType,
    to_ty: &LirType,
    signed: bool,
) -> Result<Value, BridgeError> {
    if from_ty == to_ty {
        return Ok(value);
    }

    let opcode = if to_ty.bits() > from_ty.bits() {
        if signed {
            Opcode::Sextend { from_ty: from_ty.clone(), to_ty: to_ty.clone() }
        } else {
            Opcode::Uextend { from_ty: from_ty.clone(), to_ty: to_ty.clone() }
        }
    } else {
        Opcode::Trunc { to_ty: to_ty.clone() }
    };

    let result = ctx.fresh_value();
    instructions.push(Instruction { opcode, args: vec![value], results: vec![result] });
    Ok(result)
}

fn lower_checked_overflow_flag(
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
    op: BinOp,
    rhs: &Operand,
    lhs_val: Value,
    rhs_val: Value,
    arith_result: Value,
    value_ty: &Ty,
    value_lir_ty: &LirType,
) -> Result<Value, BridgeError> {
    let signed = value_ty.is_signed();

    match op {
        BinOp::Add if signed => {
            let lhs_xor_result =
                emit_binary_inst(ctx, instructions, Opcode::Bxor, lhs_val, arith_result);
            let rhs_xor_result =
                emit_binary_inst(ctx, instructions, Opcode::Bxor, rhs_val, arith_result);
            let sign_conflict =
                emit_binary_inst(ctx, instructions, Opcode::Band, lhs_xor_result, rhs_xor_result);
            let zero = emit_iconst(ctx, instructions, value_lir_ty.clone(), 0);
            Ok(emit_binary_inst(
                ctx,
                instructions,
                Opcode::Icmp { cond: IntCC::SignedLessThan },
                sign_conflict,
                zero,
            ))
        }
        BinOp::Add => Ok(emit_binary_inst(
            ctx,
            instructions,
            Opcode::Icmp { cond: IntCC::UnsignedLessThan },
            arith_result,
            lhs_val,
        )),
        BinOp::Sub if signed => {
            let lhs_xor_rhs = emit_binary_inst(ctx, instructions, Opcode::Bxor, lhs_val, rhs_val);
            let lhs_xor_result =
                emit_binary_inst(ctx, instructions, Opcode::Bxor, lhs_val, arith_result);
            let sign_conflict =
                emit_binary_inst(ctx, instructions, Opcode::Band, lhs_xor_rhs, lhs_xor_result);
            let zero = emit_iconst(ctx, instructions, value_lir_ty.clone(), 0);
            Ok(emit_binary_inst(
                ctx,
                instructions,
                Opcode::Icmp { cond: IntCC::SignedLessThan },
                sign_conflict,
                zero,
            ))
        }
        BinOp::Sub => Ok(emit_binary_inst(
            ctx,
            instructions,
            Opcode::Icmp { cond: IntCC::UnsignedLessThan },
            lhs_val,
            rhs_val,
        )),
        BinOp::Mul => {
            let wide_ty = next_wider_int_type(value_lir_ty).ok_or_else(|| {
                BridgeError::UnsupportedOp(format!(
                    "checked multiply overflow flag not yet supported for {value_ty:?}"
                ))
            })?;
            let lhs_wide =
                emit_int_cast(ctx, instructions, lhs_val, value_lir_ty, &wide_ty, signed)?;
            let rhs_wide =
                emit_int_cast(ctx, instructions, rhs_val, value_lir_ty, &wide_ty, signed)?;
            let result_wide =
                emit_int_cast(ctx, instructions, arith_result, value_lir_ty, &wide_ty, signed)?;
            let full_product =
                emit_binary_inst(ctx, instructions, Opcode::Imul, lhs_wide, rhs_wide);
            Ok(emit_binary_inst(
                ctx,
                instructions,
                Opcode::Icmp { cond: IntCC::NotEqual },
                result_wide,
                full_product,
            ))
        }
        BinOp::Shl | BinOp::Shr => {
            let rhs_ty = operand_ty(ctx, rhs)?;
            let rhs_lir_ty = map_type(&rhs_ty)?;
            let compare_bits = rhs_lir_ty.bits().max(value_lir_ty.bits()).max(8);
            let compare_ty = integer_type_for_bits(compare_bits)?;
            let normalized_rhs = emit_int_cast(
                ctx,
                instructions,
                rhs_val,
                &rhs_lir_ty,
                &compare_ty,
                rhs_ty.is_signed(),
            )?;
            let bitwidth =
                emit_iconst(ctx, instructions, compare_ty.clone(), i64::from(value_lir_ty.bits()));
            Ok(emit_binary_inst(
                ctx,
                instructions,
                Opcode::Icmp { cond: IntCC::UnsignedGreaterThanOrEqual },
                normalized_rhs,
                bitwidth,
            ))
        }
        BinOp::Div | BinOp::Rem => Err(BridgeError::UnsupportedOp(format!(
            "checked {:?} overflow flag lowering not yet supported",
            op
        ))),
        _ => Ok(emit_iconst(ctx, instructions, LirType::B1, 0)),
    }
}

fn materialize_aggregate_value(
    ctx: &mut LoweringCtx<'_>,
    base_ptr: Value,
    lir_ty: &LirType,
    instructions: &mut Vec<Instruction>,
) -> Value {
    let value = ctx.fresh_value();
    instructions.push(Instruction {
        opcode: Opcode::Load { ty: lir_ty.clone() },
        args: vec![base_ptr],
        results: vec![value],
    });
    value
}

fn terminator_successors(term: &Terminator) -> Vec<usize> {
    match term {
        Terminator::Goto(target) => vec![target.0],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs = Vec::with_capacity(targets.len() + 1);
            for (_, target) in targets {
                if !succs.contains(&target.0) {
                    succs.push(target.0);
                }
            }
            if !succs.contains(&otherwise.0) {
                succs.push(otherwise.0);
            }
            succs
        }
        Terminator::Assert { target, .. } => vec![target.0],
        Terminator::Call { target: Some(target), .. } => vec![target.0],
        Terminator::Drop { target, .. } => vec![target.0],
        _ => vec![],
    }
}

fn terminator_supports_block_param_copies(term: &Terminator) -> bool {
    matches!(
        term,
        Terminator::Goto(_)
            | Terminator::Assert { .. }
            | Terminator::SwitchInt { .. }
            | Terminator::Call { target: Some(_), .. }
            | Terminator::Drop { .. }
    )
}

fn conditional_edge_dest(
    target: usize,
    ctx: &mut LoweringCtx<'_>,
    block_params: &FxHashMap<usize, Vec<BlockParam>>,
) -> Result<Block, BridgeError> {
    if !block_params.contains_key(&target) {
        return Ok(Block(target as u32));
    }

    let edge_block = ctx.fresh_block();
    let mut instructions = Vec::new();
    emit_block_param_copies(target, ctx, &mut instructions, block_params)?;
    instructions.push(Instruction {
        opcode: Opcode::Jump { dest: Block(target as u32) },
        args: vec![],
        results: vec![],
    });
    ctx.pending_blocks
        .push((edge_block, LirBlock { params: vec![], instructions, source_locs: vec![] }));
    Ok(edge_block)
}

fn note_live_in(
    local: usize,
    written: &FxHashSet<usize>,
    seen: &mut FxHashSet<usize>,
    live_ins: &mut Vec<usize>,
) {
    if !written.contains(&local) && seen.insert(local) {
        live_ins.push(local);
    }
}

fn collect_place_live_ins(
    place: &Place,
    written: &FxHashSet<usize>,
    seen: &mut FxHashSet<usize>,
    live_ins: &mut Vec<usize>,
) {
    note_live_in(place.local, written, seen, live_ins);
    for projection in &place.projections {
        if let Projection::Index(index_local) = projection {
            note_live_in(*index_local, written, seen, live_ins);
        }
    }
}

fn collect_operand_live_ins(
    operand: &Operand,
    written: &FxHashSet<usize>,
    seen: &mut FxHashSet<usize>,
    live_ins: &mut Vec<usize>,
) {
    if let Operand::Copy(place) | Operand::Move(place) = operand {
        collect_place_live_ins(place, written, seen, live_ins);
    }
}

fn collect_rvalue_live_ins(
    rvalue: &Rvalue,
    written: &FxHashSet<usize>,
    seen: &mut FxHashSet<usize>,
    live_ins: &mut Vec<usize>,
) {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Cast(operand, _)
        | Rvalue::Repeat(operand, _) => {
            collect_operand_live_ins(operand, written, seen, live_ins);
        }
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            collect_operand_live_ins(lhs, written, seen, live_ins);
            collect_operand_live_ins(rhs, written, seen, live_ins);
        }
        Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place)
        | Rvalue::AddressOf(_, place) => {
            collect_place_live_ins(place, written, seen, live_ins);
        }
        Rvalue::Ref { place, .. } => {
            collect_place_live_ins(place, written, seen, live_ins);
        }
        Rvalue::Aggregate(_, operands) => {
            for operand in operands {
                collect_operand_live_ins(operand, written, seen, live_ins);
            }
        }
        _ => {}
    }
}

fn collect_block_live_ins(bb: &TrustBlock) -> Vec<usize> {
    let mut written = FxHashSet::default();
    let mut seen = FxHashSet::default();
    let mut live_ins = Vec::new();

    for stmt in &bb.stmts {
        if let Statement::Assign { place, rvalue, .. } = stmt {
            collect_rvalue_live_ins(rvalue, &written, &mut seen, &mut live_ins);
            if place.projections.is_empty() {
                written.insert(place.local);
            } else {
                collect_place_live_ins(place, &written, &mut seen, &mut live_ins);
            }
        }
    }

    match &bb.terminator {
        Terminator::SwitchInt { discr, .. } | Terminator::Assert { cond: discr, .. } => {
            collect_operand_live_ins(discr, &written, &mut seen, &mut live_ins);
        }
        Terminator::Call { args, dest, atomic, .. } => {
            for arg in args {
                collect_operand_live_ins(arg, &written, &mut seen, &mut live_ins);
            }
            if let Some(atomic) = atomic {
                collect_place_live_ins(&atomic.place, &written, &mut seen, &mut live_ins);
                let result_dest = atomic.dest.as_ref().unwrap_or(dest);
                if !result_dest.projections.is_empty() {
                    collect_place_live_ins(result_dest, &written, &mut seen, &mut live_ins);
                }
            } else if !dest.projections.is_empty() {
                collect_place_live_ins(dest, &written, &mut seen, &mut live_ins);
            }
        }
        Terminator::Drop { place, .. } => {
            collect_place_live_ins(place, &written, &mut seen, &mut live_ins);
        }
        _ => {}
    }

    live_ins
}

fn collect_predecessors(body: &VerifiableBody) -> FxHashMap<usize, Vec<usize>> {
    let mut predecessors =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());

    for bb in &body.blocks {
        for successor in terminator_successors(&bb.terminator) {
            let preds: &mut Vec<usize> = predecessors.entry(successor).or_default();
            if !preds.contains(&bb.id.0) {
                preds.push(bb.id.0);
            }
        }
    }

    predecessors
}

fn collect_assigned_locals(body: &VerifiableBody) -> FxHashSet<usize> {
    let mut assigned = FxHashSet::default();

    for bb in &body.blocks {
        for stmt in &bb.stmts {
            if let Statement::Assign { place, .. } = stmt {
                if place.projections.is_empty() {
                    assigned.insert(place.local);
                }
            }
        }
        if let Some(local) = terminator_written_local(&bb.terminator) {
            assigned.insert(local);
        }
    }

    assigned
}

fn terminator_written_local(term: &Terminator) -> Option<usize> {
    match term {
        Terminator::Call { dest, atomic: None, .. } => {
            dest.projections.is_empty().then_some(dest.local)
        }
        Terminator::Call { dest, atomic: Some(atomic), .. } => {
            if atomic.op_kind.is_store() || atomic.op_kind.is_fence() {
                return None;
            }

            atomic
                .dest
                .as_ref()
                .or(Some(dest))
                .and_then(|place| place.projections.is_empty().then_some(place.local))
        }
        _ => None,
    }
}

fn collect_block_written_locals(bb: &TrustBlock) -> FxHashSet<usize> {
    let mut written = FxHashSet::default();

    for stmt in &bb.stmts {
        if let Statement::Assign { place, .. } = stmt {
            if place.projections.is_empty() {
                written.insert(place.local);
            }
        }
    }

    if let Some(local) = terminator_written_local(&bb.terminator) {
        written.insert(local);
    }

    written
}

fn compute_required_locals(body: &VerifiableBody) -> FxHashMap<usize, Vec<usize>> {
    let mut required_locals =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
    let mut required_seen =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
    let mut written_locals =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());

    for bb in &body.blocks {
        let live_ins = collect_block_live_ins(bb);
        let seen: FxHashSet<usize> = live_ins.iter().copied().collect();
        required_locals.insert(bb.id.0, live_ins);
        required_seen.insert(bb.id.0, seen);
        written_locals.insert(bb.id.0, collect_block_written_locals(bb));
    }

    loop {
        let mut changed = false;

        for bb in body.blocks.iter().rev() {
            if !terminator_supports_block_param_copies(&bb.terminator) {
                continue;
            }

            let successors = terminator_successors(&bb.terminator);
            let written =
                written_locals.get(&bb.id.0).expect("written locals exist for every block");
            let mut propagated = Vec::new();

            for successor in successors {
                let Some(successor_required) = required_locals.get(&successor).cloned() else {
                    continue;
                };

                for local in successor_required {
                    if written.contains(&local) {
                        continue;
                    }
                    propagated.push(local);
                }
            }

            let block_required =
                required_locals.get_mut(&bb.id.0).expect("required locals exist for every block");
            let block_seen =
                required_seen.get_mut(&bb.id.0).expect("required-local set exists for every block");

            for local in propagated {
                if block_seen.insert(local) {
                    block_required.push(local);
                    changed = true;
                }
            }
        }

        if !changed {
            break;
        }
    }

    required_locals
}

fn plan_block_params(
    body: &VerifiableBody,
    ctx: &mut LoweringCtx<'_>,
    predecessors: &FxHashMap<usize, Vec<usize>>,
) -> Result<FxHashMap<usize, Vec<BlockParam>>, BridgeError> {
    let blocks_by_id: FxHashMap<usize, &TrustBlock> =
        body.blocks.iter().map(|bb| (bb.id.0, bb)).collect();
    let assigned_locals = collect_assigned_locals(body);
    let required_locals = compute_required_locals(body);
    let mut block_params =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());

    for bb in &body.blocks {
        let Some(preds) = predecessors.get(&bb.id.0) else {
            continue;
        };
        if preds.len() <= 1 {
            continue;
        }
        if preds.iter().any(|pred_id| {
            blocks_by_id
                .get(pred_id)
                .is_none_or(|pred| !terminator_supports_block_param_copies(&pred.terminator))
        }) {
            continue;
        }

        let live_ins: Vec<usize> = required_locals
            .get(&bb.id.0)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .filter(|local| assigned_locals.contains(local))
            .collect();
        if live_ins.is_empty() {
            continue;
        }

        let mut params = Vec::with_capacity(live_ins.len());
        for local in live_ins {
            params.push(BlockParam {
                local,
                value: ctx.fresh_value(),
                ty: map_lowering_type(ctx.local_ty(local)?)?,
            });
        }
        block_params.insert(bb.id.0, params);
    }

    Ok(block_params)
}

fn emit_block_param_copies(
    target: usize,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
    block_params: &FxHashMap<usize, Vec<BlockParam>>,
) -> Result<(), BridgeError> {
    let Some(params) = block_params.get(&target) else {
        return Ok(());
    };

    let mut pending_copies = Vec::with_capacity(params.len());
    for param in params {
        let src = ctx.local_value(param.local)?;
        if src == param.value {
            continue;
        }
        pending_copies.push((src, param.value));
    }

    while !pending_copies.is_empty() {
        if let Some(idx) = pending_copies.iter().enumerate().find_map(|(idx, (_, dest))| {
            (!pending_copies
                .iter()
                .enumerate()
                .any(|(other_idx, (other_src, _))| other_idx != idx && *other_src == *dest))
            .then_some(idx)
        }) {
            let (src, dest) = pending_copies.swap_remove(idx);
            instructions.push(Instruction {
                opcode: Opcode::Copy,
                args: vec![src],
                results: vec![dest],
            });
            continue;
        }

        let temp = ctx.fresh_value();
        let (src, _) = pending_copies[0];
        instructions.push(Instruction {
            opcode: Opcode::Copy,
            args: vec![src],
            results: vec![temp],
        });
        pending_copies[0].0 = temp;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Public API: lower_to_lir
// ---------------------------------------------------------------------------

// tRust: #828 — refresh supported MIR constructs in lower_to_lir docs.
/// Convert a trust-types `VerifiableFunction` to an LLVM2 LIR `Function`.
///
/// This is the primary entry point for the bridge. It maps the function
/// signature, basic blocks, statements, and terminators to LIR equivalents.
///
/// # Supported MIR constructs
///
/// - Scalar and aggregate types (tuples, ADTs, arrays, slices, references)
/// - Place projections (field, deref, index, downcast, constant-index, subslice)
/// - Memory operations (load, store, stack slots, address-of)
/// - Function calls (direct) and drop elaboration
/// - All terminators (goto, return, switch, assert, call, drop, unreachable)
/// - Casts (int-int, float-int, int-float, float-float, ptr-ptr)
#[must_use = "returns the lowered LIR function"]
pub fn lower_to_lir(func: &VerifiableFunction) -> Result<LirFunction, BridgeError> {
    lower_body_to_lir(&func.name, &func.body)
}

/// Convert a trust-types `VerifiableBody` to an LLVM2 LIR `Function`.
///
/// Separated from `lower_to_lir` to allow testing with bodies directly.
pub fn lower_body_to_lir(name: &str, body: &VerifiableBody) -> Result<LirFunction, BridgeError> {
    // tRust: Validate that the function body is not empty.
    if body.blocks.is_empty() {
        return Err(BridgeError::EmptyBody);
    }

    // tRust: Detect duplicate block IDs which indicate malformed MIR.
    {
        let mut seen_ids =
            FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
        for bb in &body.blocks {
            if let Some(()) = seen_ids.insert(bb.id.0, ()) {
                return Err(BridgeError::InvalidMir(format!("duplicate block ID: bb{}", bb.id.0)));
            }
        }
    }

    // Compute the maximum block ID so the context can allocate new blocks
    // (e.g., the panic block for Assert) without collisions.
    let max_block_id = body.blocks.iter().map(|bb| bb.id.0 as u32).max().unwrap_or(0);
    let mut ctx = LoweringCtx::new(&body.locals, body.arg_count, max_block_id);
    let initial_local_values = ctx.local_values.clone();
    let predecessors = collect_predecessors(body);
    let block_params = plan_block_params(body, &mut ctx, &predecessors)?;

    // Build signature from locals: args are locals[1..=arg_count], return is locals[0].
    let return_ty = map_lowering_type(&body.return_ty)?;
    let mut param_types = Vec::with_capacity(body.arg_count);
    for i in 1..=body.arg_count {
        let local =
            body.locals.iter().find(|l| l.index == i).ok_or(BridgeError::MissingLocal(i))?;
        param_types.push(map_lowering_type(&local.ty)?);
    }
    let returns =
        if matches!(body.return_ty, Ty::Unit | Ty::Never) { vec![] } else { vec![return_ty] };
    let has_return_value = !matches!(body.return_ty, Ty::Unit | Ty::Never);
    let signature = Signature { params: param_types, returns };

    // Convert each basic block.
    // tRust: std HashMap required by LirFunction API contract (llvm2-lower).
    // Keys are Block(u32) — deterministic hash. Iteration order does not affect
    // LLVM2 codegen (blocks are selected by entry_block + successors). (#827)
    let mut blocks = std::collections::HashMap::with_capacity(body.blocks.len());
    let mut block_entry_values =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
    block_entry_values.insert(body.blocks[0].id.0, initial_local_values.clone());
    for bb in &body.blocks {
        let block = Block(bb.id.0 as u32);
        let mut entry_values = block_entry_values
            .get(&bb.id.0)
            .cloned()
            .unwrap_or_else(|| initial_local_values.clone());
        if let Some(params) = block_params.get(&bb.id.0) {
            for param in params {
                entry_values.insert(param.local, param.value);
            }
        }
        let params = block_params.get(&bb.id.0).map_or(&[][..], Vec::as_slice);
        let lir_block =
            lower_block(bb, &mut ctx, has_return_value, &entry_values, params, &block_params)?;
        let exit_values = ctx.local_values.clone();
        for successor in terminator_successors(&bb.terminator) {
            if block_params.contains_key(&successor) {
                continue;
            }
            if predecessors.get(&successor).is_some_and(|preds| preds.len() == 1) {
                block_entry_values.insert(successor, exit_values.clone());
            }
        }
        blocks.insert(block, lir_block);
    }

    for (block, lir_block) in std::mem::take(&mut ctx.pending_blocks) {
        blocks.insert(block, lir_block);
    }

    // tRust: If any Assert terminator needed a panic block, insert it now.
    // The panic block contains a single abort call so failure cannot
    // silently fall through as a fabricated return.
    if let Some(panic_blk) = ctx.panic_block {
        blocks.insert(
            panic_blk,
            LirBlock {
                params: vec![],
                instructions: vec![abort_call_instruction()],
                source_locs: vec![],
            },
        );
    }

    // SAFETY: body.blocks is non-empty (validated above).
    let entry_block = Block(body.blocks[0].id.0 as u32);

    Ok(LirFunction {
        name: name.to_string(),
        signature,
        blocks,
        entry_block,
        stack_slots: ctx.stack_slots,
        // tRust: #986 — preserve call-result types for ISel when the
        // producing opcode omits result type metadata.
        value_types: ctx.value_types,
        pure_callees: std::collections::HashSet::new(),
    })
}

// ---------------------------------------------------------------------------
// Block lowering
// ---------------------------------------------------------------------------

fn lower_block(
    bb: &TrustBlock,
    ctx: &mut LoweringCtx<'_>,
    has_return_value: bool,
    entry_values: &FxHashMap<usize, Value>,
    params: &[BlockParam],
    block_params: &FxHashMap<usize, Vec<BlockParam>>,
) -> Result<LirBlock, BridgeError> {
    ctx.local_values = entry_values.clone();
    let mut instructions = Vec::new();

    // Lower each statement.
    for stmt in &bb.stmts {
        lower_statement(stmt, ctx, &mut instructions)?;
    }

    // Lower the terminator.
    lower_terminator(&bb.terminator, ctx, &mut instructions, has_return_value, block_params)?;

    Ok(LirBlock {
        params: params.iter().map(|param| (param.value, param.ty.clone())).collect(),
        instructions,
        source_locs: vec![],
    })
}

// ---------------------------------------------------------------------------
// Statement lowering
// ---------------------------------------------------------------------------

fn lower_statement(
    stmt: &Statement,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), BridgeError> {
    match stmt {
        Statement::Assign { place, rvalue, span: _ } => {
            lower_rvalue(place, rvalue, ctx, instructions)?;
        }
        // tRust: #966 — no-op metadata/lifetime statements produce no LIR instructions.
        Statement::Nop
        | Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::PlaceMention(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Retag { .. } => {}
        // tRust: #966 — SetDiscriminant/Deinit/Intrinsic don't yet produce LIR;
        // once the backend matures these may need real lowering.
        Statement::SetDiscriminant { .. }
        | Statement::Deinit { .. }
        | Statement::Intrinsic { .. } => {}
        // tRust: #966 — Statement is #[non_exhaustive]; future variants are no-ops
        // until explicit lowering is added.
        _ => {}
    }
    Ok(())
}

/// Helper: assign a computed value to a destination place.
///
/// For simple locals, updates the local_values map. For projected places,
/// computes the address and emits a Store instruction.
fn assign_to_place(
    dest: &Place,
    value: Value,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), BridgeError> {
    if dest.projections.is_empty() {
        ctx.local_values.insert(dest.local, value);
    } else {
        let addr = ctx.resolve_place_addr(dest, instructions)?;
        instructions.push(Instruction {
            opcode: Opcode::Store,
            args: vec![value, addr],
            results: vec![],
        });
    }
    Ok(())
}

fn lower_rvalue(
    dest: &Place,
    rvalue: &Rvalue,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), BridgeError> {
    let dest_val = ctx.fresh_value();

    match rvalue {
        Rvalue::Use(operand) => {
            let src = ctx.resolve_operand(operand, instructions)?;
            assign_to_place(dest, src, ctx, instructions)?;
        }
        Rvalue::BinaryOp(op, lhs, rhs) => {
            let lhs_val = ctx.resolve_operand(lhs, instructions)?;
            let rhs_val = ctx.resolve_operand(rhs, instructions)?;

            // tRust: #828 — lower three-way compare as nested selects over lt/gt tests.
            if *op == BinOp::Cmp {
                let lt_cmp = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Icmp { cond: IntCC::SignedLessThan },
                    args: vec![lhs_val, rhs_val],
                    results: vec![lt_cmp],
                });
                let neg_one = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::I32, imm: -1 },
                    args: vec![],
                    results: vec![neg_one],
                });
                let gt_cmp = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Icmp { cond: IntCC::SignedGreaterThan },
                    args: vec![lhs_val, rhs_val],
                    results: vec![gt_cmp],
                });
                let one = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::I32, imm: 1 },
                    args: vec![],
                    results: vec![one],
                });
                let zero = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::I32, imm: 0 },
                    args: vec![],
                    results: vec![zero],
                });
                let step1 = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Select { cond: IntCC::NotEqual },
                    args: vec![gt_cmp, one, zero],
                    results: vec![step1],
                });
                let result = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Select { cond: IntCC::NotEqual },
                    args: vec![lt_cmp, neg_one, step1],
                    results: vec![result],
                });
                assign_to_place(dest, result, ctx, instructions)?;
                return Ok(());
            }

            let lhs_is_float = match lhs {
                Operand::Copy(place) | Operand::Move(place) => {
                    ctx.local_ty(place.local)?.is_float()
                }
                Operand::Constant(ConstValue::Float(_)) => true,
                _ => false,
            };
            let rhs_is_float = match rhs {
                Operand::Copy(place) | Operand::Move(place) => {
                    ctx.local_ty(place.local)?.is_float()
                }
                Operand::Constant(ConstValue::Float(_)) => true,
                _ => false,
            };
            if lhs_is_float || rhs_is_float {
                let opcode = map_float_binop(*op)?;
                instructions.push(Instruction {
                    opcode,
                    args: vec![lhs_val, rhs_val],
                    results: vec![dest_val],
                });
                assign_to_place(dest, dest_val, ctx, instructions)?;
                return Ok(());
            }

            let signed = ctx.is_signed(dest.local);
            let opcode = map_binop(*op, signed)?;

            instructions.push(Instruction {
                opcode,
                args: vec![lhs_val, rhs_val],
                results: vec![dest_val],
            });
            assign_to_place(dest, dest_val, ctx, instructions)?;
        }
        // tRust: #828 — CheckedBinaryOp produces a (result, overflow_flag) tuple.
        // Compute the narrow wrapping result, then derive the overflow flag
        // with a sound per-op check on the checked value type.
        Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let lhs_val = ctx.resolve_operand(lhs, instructions)?;
            let rhs_val = ctx.resolve_operand(rhs, instructions)?;
            let value_ty = checked_binary_value_ty(ctx, dest)?;
            if value_ty.is_float() {
                return Err(BridgeError::UnsupportedOp(format!(
                    "checked floating-point binary op not supported: {op:?}"
                )));
            }
            let value_lir_ty = map_type(&value_ty)?;
            let signed = value_ty.is_signed();
            let opcode = map_binop(*op, signed)?;
            let arith_result = ctx.fresh_value();
            instructions.push(Instruction {
                opcode,
                args: vec![lhs_val, rhs_val],
                results: vec![arith_result],
            });
            let overflow_val = lower_checked_overflow_flag(
                ctx,
                instructions,
                *op,
                rhs,
                lhs_val,
                rhs_val,
                arith_result,
                &value_ty,
                &value_lir_ty,
            )?;

            let overflow_val = lower_checked_overflow_flag(
                ctx,
                instructions,
                *op,
                rhs,
                lhs_val,
                rhs_val,
                arith_result,
                &value_ty,
                &value_lir_ty,
            )?;

            // Build the (result, overflow) tuple in a stack slot.
            let dest_ty = ctx.local_ty(dest.local)?.clone();
            let lir_ty = map_type(&dest_ty)?;
            let slot = ctx.alloc_stack_slot(&lir_ty);
            let base_ptr = ctx.emit_stack_addr(slot, instructions);

            // Store field 0: arithmetic result.
            let field0_ptr = ctx.fresh_value();
            instructions.push(Instruction {
                opcode: Opcode::StructGep { struct_ty: lir_ty.clone(), field_index: 0 },
                args: vec![base_ptr],
                results: vec![field0_ptr],
            });
            instructions.push(Instruction {
                opcode: Opcode::Store,
                args: vec![arith_result, field0_ptr],
                results: vec![],
            });

            // Store field 1: overflow flag.
            let field1_ptr = ctx.fresh_value();
            instructions.push(Instruction {
                opcode: Opcode::StructGep { struct_ty: lir_ty.clone(), field_index: 1 },
                args: vec![base_ptr],
                results: vec![field1_ptr],
            });
            instructions.push(Instruction {
                opcode: Opcode::Store,
                args: vec![overflow_val, field1_ptr],
                results: vec![],
            });

            ctx.local_stack_slots.insert(dest.local, slot);
            let tuple_value = materialize_aggregate_value(ctx, base_ptr, &lir_ty, instructions);
            ctx.local_values.insert(dest.local, tuple_value);
        }
        Rvalue::UnaryOp(op, operand) => {
            // tRust: #828 — PtrMetadata extracts the metadata lane from fat pointers.
            if *op == UnOp::PtrMetadata {
                let _src = ctx.resolve_operand(operand, instructions)?;
                let src_ty = match operand {
                    Operand::Copy(place) | Operand::Move(place) => {
                        Some(ctx.local_ty(place.local)?.clone())
                    }
                    _ => None,
                };

                let is_fat_ptr = matches!(&src_ty, Some(Ty::Slice { .. }))
                    || matches!(
                        &src_ty,
                        Some(Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. })
                            if matches!(inner.as_ref(), Ty::Slice { .. })
                    );

                if is_fat_ptr {
                    let place = match operand {
                        Operand::Copy(place) | Operand::Move(place) => place,
                        _ => unreachable!("fat-pointer PtrMetadata operand must be a place"),
                    };
                    let slot = ctx.ensure_local_stack_slot(place.local)?;
                    let base_addr = ctx.emit_stack_addr(slot, instructions);
                    let metadata_ptr = ctx.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::StructGep {
                            struct_ty: LirType::Struct(vec![LirType::I64, LirType::I64]),
                            field_index: 1,
                        },
                        args: vec![base_addr],
                        results: vec![metadata_ptr],
                    });
                    let loaded = ctx.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Load { ty: LirType::I64 },
                        args: vec![metadata_ptr],
                        results: vec![loaded],
                    });
                    assign_to_place(dest, loaded, ctx, instructions)?;
                } else {
                    let zero = ctx.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: 0 },
                        args: vec![],
                        results: vec![zero],
                    });
                    assign_to_place(dest, zero, ctx, instructions)?;
                }

                return Ok(());
            }

            let src = ctx.resolve_operand(operand, instructions)?;
            let opcode = map_unop(*op)?;
            instructions.push(Instruction { opcode, args: vec![src], results: vec![dest_val] });
            assign_to_place(dest, dest_val, ctx, instructions)?;
        }
        // tRust: #828 — Cast handles int-to-int, float-to-int, int-to-float,
        // float-to-float, and pointer-to-pointer conversions.
        Rvalue::Cast(operand, target_ty) => {
            let src = ctx.resolve_operand(operand, instructions)?;

            let src_ty = match operand {
                Operand::Copy(p) | Operand::Move(p) => ctx.local_ty(p.local).ok(),
                _ => None,
            };

            let src_is_float = src_ty.is_some_and(|t| t.is_float());
            let dst_is_float = target_ty.is_float();
            let src_is_ptr = src_ty.is_some_and(|t| t.is_pointer_like());
            let dst_is_ptr = target_ty.is_pointer_like();

            if src_is_float && !dst_is_float {
                // tRust: Float-to-Int conversion (FcvtToInt / FcvtToUint).
                let dst_ty = map_type(target_ty)?;
                let signed = target_ty.is_signed();
                let opcode = if signed {
                    Opcode::FcvtToInt { dst_ty }
                } else {
                    Opcode::FcvtToUint { dst_ty }
                };
                instructions.push(Instruction { opcode, args: vec![src], results: vec![dest_val] });
                assign_to_place(dest, dest_val, ctx, instructions)?;
            } else if !src_is_float && dst_is_float {
                // tRust: Int-to-Float conversion (FcvtFromInt / FcvtFromUint).
                let src_lir_ty = src_ty.map(map_type).transpose()?.unwrap_or(LirType::I32);
                let signed = src_ty.is_some_and(|t| t.is_signed());
                let opcode = if signed {
                    Opcode::FcvtFromInt { src_ty: src_lir_ty }
                } else {
                    Opcode::FcvtFromUint { src_ty: src_lir_ty }
                };
                instructions.push(Instruction { opcode, args: vec![src], results: vec![dest_val] });
                assign_to_place(dest, dest_val, ctx, instructions)?;
            } else if src_is_float && dst_is_float {
                // tRust: Float-to-Float conversion (FPExt / FPTrunc).
                let src_width = src_ty.and_then(|t| match t {
                    Ty::Float { width } => Some(*width),
                    _ => None,
                });
                let dst_width = match target_ty {
                    Ty::Float { width } => Some(*width),
                    _ => None,
                };
                match (src_width, dst_width) {
                    (Some(sw), Some(dw)) if sw < dw => {
                        // Widen: f32 -> f64
                        instructions.push(Instruction {
                            opcode: Opcode::FPExt,
                            args: vec![src],
                            results: vec![dest_val],
                        });
                        assign_to_place(dest, dest_val, ctx, instructions)?;
                    }
                    (Some(sw), Some(dw)) if sw > dw => {
                        // Narrow: f64 -> f32
                        instructions.push(Instruction {
                            opcode: Opcode::FPTrunc,
                            args: vec![src],
                            results: vec![dest_val],
                        });
                        assign_to_place(dest, dest_val, ctx, instructions)?;
                    }
                    _ => {
                        // Same width or unknown: passthrough.
                        assign_to_place(dest, src, ctx, instructions)?;
                    }
                }
            } else if src_is_ptr && dst_is_ptr {
                // tRust: Ptr-to-Ptr cast. Both are I64 in our representation,
                // so this is a no-op bitcast.
                assign_to_place(dest, src, ctx, instructions)?;
            } else {
                // Int-to-Int cast (original logic).
                let src_width = src_ty.and_then(LoweringCtx::ty_bit_width);
                let dst_width = LoweringCtx::ty_bit_width(target_ty);

                match (src_width, dst_width) {
                    (Some(sw), Some(dw)) if sw == dw => {
                        assign_to_place(dest, src, ctx, instructions)?;
                    }
                    (Some(sw), Some(dw)) if sw > dw => {
                        let to_ty = map_type(target_ty)?;
                        instructions.push(Instruction {
                            opcode: Opcode::Trunc { to_ty },
                            args: vec![src],
                            results: vec![dest_val],
                        });
                        assign_to_place(dest, dest_val, ctx, instructions)?;
                    }
                    (Some(_), Some(_)) => {
                        let from_ty = src_ty.map(map_type).transpose()?.unwrap_or(LirType::I32);
                        let to_ty = map_type(target_ty)?;
                        let signed = src_ty.is_some_and(|t| t.is_signed());
                        let opcode = if signed {
                            Opcode::Sextend { from_ty, to_ty }
                        } else {
                            Opcode::Uextend { from_ty, to_ty }
                        };
                        instructions.push(Instruction {
                            opcode,
                            args: vec![src],
                            results: vec![dest_val],
                        });
                        assign_to_place(dest, dest_val, ctx, instructions)?;
                    }
                    _ => {
                        assign_to_place(dest, src, ctx, instructions)?;
                    }
                }
            }
        }
        Rvalue::Discriminant(place) => {
            let local_ty = ctx.local_ty(place.local)?.clone();
            if is_fieldless_adt(&local_ty) {
                // trust-types currently drops enum field layout for some ADTs
                // like `Option<T>`. In that case we preserve only the opaque
                // discriminant value and cannot project a tag field.
                let discr = ctx.resolve_place(place, instructions)?;
                assign_to_place(dest, discr, ctx, instructions)?;
            } else {
                // Discriminant: extract the tag field from an ADT.
                // By convention the discriminant is field 0 of the struct layout,
                // stored as an integer. We emit StructGep(0) + Load(I64).
                let base_val = if let Some(&slot) = ctx.local_stack_slots.get(&place.local) {
                    ctx.emit_stack_addr(slot, instructions)
                } else {
                    // If the local doesn't have a stack slot, allocate one.
                    let slot = ctx.ensure_local_stack_slot(place.local)?;
                    ctx.emit_stack_addr(slot, instructions)
                };
                let lir_ty = map_type(&local_ty)?;
                let gep_result = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::StructGep { struct_ty: lir_ty, field_index: 0 },
                    args: vec![base_val],
                    results: vec![gep_result],
                });
                let loaded = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Load { ty: LirType::I64 },
                    args: vec![gep_result],
                    results: vec![loaded],
                });
                assign_to_place(dest, loaded, ctx, instructions)?;
            }
        }
        Rvalue::Len(place) => {
            // Len: for slices, load the length field (field 1 of the fat pointer).
            // For arrays, emit a constant with the known length.
            let place_ty = ctx.local_ty(place.local)?.clone();
            match &place_ty {
                Ty::Array { len, .. } => {
                    let len_val = ctx.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: *len as i64 },
                        args: vec![],
                        results: vec![len_val],
                    });
                    assign_to_place(dest, len_val, ctx, instructions)?;
                }
                Ty::Slice { .. } => {
                    // Slice is { ptr, len }. Load field 1 (len).
                    let base_val = if let Some(&slot) = ctx.local_stack_slots.get(&place.local) {
                        ctx.emit_stack_addr(slot, instructions)
                    } else {
                        let slot = ctx.ensure_local_stack_slot(place.local)?;
                        ctx.emit_stack_addr(slot, instructions)
                    };
                    let lir_ty = map_type(&place_ty)?;
                    let gep_result = ctx.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::StructGep { struct_ty: lir_ty, field_index: 1 },
                        args: vec![base_val],
                        results: vec![gep_result],
                    });
                    let loaded = ctx.fresh_value();
                    instructions.push(Instruction {
                        opcode: Opcode::Load { ty: LirType::I64 },
                        args: vec![gep_result],
                        results: vec![loaded],
                    });
                    assign_to_place(dest, loaded, ctx, instructions)?;
                }
                other => {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "Len on non-array/slice type: {other:?}"
                    )));
                }
            }
        }
        Rvalue::Ref { place, .. } => {
            // Create a reference: compute the address of the place.
            let addr = ctx.resolve_place_addr(place, instructions)?;
            assign_to_place(dest, addr, ctx, instructions)?;
        }
        Rvalue::AddressOf(_mutable, place) => {
            // Raw address-of: compute the address of the place.
            let addr = ctx.resolve_place_addr(place, instructions)?;
            assign_to_place(dest, addr, ctx, instructions)?;
        }
        Rvalue::Aggregate(kind, operands) => {
            // Aggregate construction: allocate a stack slot, store each field.
            let dest_ty = ctx.local_ty(dest.local)?.clone();
            let lir_ty = map_lowering_type(&dest_ty)?;

            let slot = ctx.alloc_stack_slot(&lir_ty);
            let base_ptr = ctx.emit_stack_addr(slot, instructions);

            match kind {
                AggregateKind::Tuple | AggregateKind::Array => {
                    for (i, operand) in operands.iter().enumerate() {
                        let val = ctx.resolve_operand(operand, instructions)?;
                        let field_ptr = ctx.fresh_value();
                        instructions.push(Instruction {
                            opcode: Opcode::StructGep {
                                struct_ty: lir_ty.clone(),
                                field_index: i as u32,
                            },
                            args: vec![base_ptr],
                            results: vec![field_ptr],
                        });
                        instructions.push(Instruction {
                            opcode: Opcode::Store,
                            args: vec![val, field_ptr],
                            results: vec![],
                        });
                    }
                }
                AggregateKind::Adt { variant, .. } => {
                    if is_fieldless_adt(&dest_ty) {
                        // Enums extracted as fieldless ADTs (e.g., Option<T>) do not
                        // carry layout metadata through trust-types. Preserve only
                        // the discriminant as an opaque I64 so later passes do not
                        // see invalid StructGep instructions against `Struct([])`.
                        if operands.len() > 1 {
                            return Err(BridgeError::UnsupportedOp(
                                "fieldless ADT aggregate with multiple payload operands"
                                    .to_string(),
                            ));
                        }
                        if let Some(payload) = operands.first() {
                            let _ = ctx.resolve_operand(payload, instructions)?;
                        }
                        let discr = ctx.fresh_value();
                        instructions.push(Instruction {
                            opcode: Opcode::Iconst { ty: LirType::I64, imm: *variant as i64 },
                            args: vec![],
                            results: vec![discr],
                        });
                        instructions.push(Instruction {
                            opcode: Opcode::Store,
                            args: vec![discr, base_ptr],
                            results: vec![],
                        });
                    } else {
                        // tRust: #828 — enum variant construction must write the
                        // discriminant tag. Convention: if field 0 of the ADT is
                        // named "tag", it is the discriminant and operands map to
                        // fields starting at index 1. For plain structs (no "tag"
                        // field) operands map 1:1 to fields.
                        let has_discriminant = matches!(
                            &dest_ty,
                            Ty::Adt { fields, .. }
                                if fields.first().map(|(n, _)| n.as_str()) == Some("tag")
                        );

                        let field_offset: u32 = if has_discriminant {
                            // Store the variant index as the discriminant at field 0.
                            let tag_ptr = ctx.fresh_value();
                            instructions.push(Instruction {
                                opcode: Opcode::StructGep {
                                    struct_ty: lir_ty.clone(),
                                    field_index: 0,
                                },
                                args: vec![base_ptr],
                                results: vec![tag_ptr],
                            });
                            let tag_val = ctx.fresh_value();
                            instructions.push(Instruction {
                                opcode: Opcode::Iconst { ty: LirType::I64, imm: *variant as i64 },
                                args: vec![],
                                results: vec![tag_val],
                            });
                            instructions.push(Instruction {
                                opcode: Opcode::Store,
                                args: vec![tag_val, tag_ptr],
                                results: vec![],
                            });
                            1 // data fields start after the discriminant
                        } else {
                            0
                        };

                        for (i, operand) in operands.iter().enumerate() {
                            let val = ctx.resolve_operand(operand, instructions)?;
                            let field_ptr = ctx.fresh_value();
                            instructions.push(Instruction {
                                opcode: Opcode::StructGep {
                                    struct_ty: lir_ty.clone(),
                                    field_index: i as u32 + field_offset,
                                },
                                args: vec![base_ptr],
                                results: vec![field_ptr],
                            });
                            instructions.push(Instruction {
                                opcode: Opcode::Store,
                                args: vec![val, field_ptr],
                                results: vec![],
                            });
                        }
                    }
                }
                other => {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "unsupported aggregate kind: {other:?}"
                    )));
                }
            }

            // Track this local's stack slot so future projections can find it.
            ctx.local_stack_slots.insert(dest.local, slot);
            let aggregate_value = materialize_aggregate_value(ctx, base_ptr, &lir_ty, instructions);
            ctx.local_values.insert(dest.local, aggregate_value);
        }
        Rvalue::Repeat(operand, count) => {
            // Array repeat: [operand; count]. Allocate stack slot and store
            // the same value `count` times.
            let dest_ty = ctx.local_ty(dest.local)?.clone();
            let lir_ty = map_type(&dest_ty)?;
            let elem_ty = match &dest_ty {
                Ty::Array { elem, .. } => map_type(elem)?,
                _ => {
                    return Err(BridgeError::UnsupportedOp("Repeat on non-array type".to_string()));
                }
            };

            let slot = ctx.alloc_stack_slot(&lir_ty);
            let base_ptr = ctx.emit_stack_addr(slot, instructions);
            let val = ctx.resolve_operand(operand, instructions)?;

            let elem_size = elem_ty.bytes();
            for i in 0..*count {
                let offset_const = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::I64, imm: (i as u32 * elem_size) as i64 },
                    args: vec![],
                    results: vec![offset_const],
                });
                let elem_ptr = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iadd,
                    args: vec![base_ptr, offset_const],
                    results: vec![elem_ptr],
                });
                instructions.push(Instruction {
                    opcode: Opcode::Store,
                    args: vec![val, elem_ptr],
                    results: vec![],
                });
            }

            ctx.local_stack_slots.insert(dest.local, slot);
            let array_value = materialize_aggregate_value(ctx, base_ptr, &lir_ty, instructions);
            ctx.local_values.insert(dest.local, array_value);
        }
        Rvalue::CopyForDeref(place) => {
            let src = ctx.resolve_place(place, instructions)?;
            assign_to_place(dest, src, ctx, instructions)?;
        }
        _ => {
            return Err(BridgeError::UnsupportedOp("unknown rvalue variant".to_string()));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Terminator lowering
// ---------------------------------------------------------------------------

fn lower_terminator(
    term: &Terminator,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
    has_return_value: bool,
    block_params: &FxHashMap<usize, Vec<BlockParam>>,
) -> Result<(), BridgeError> {
    match term {
        Terminator::Goto(target) => {
            emit_block_param_copies(target.0, ctx, instructions, block_params)?;
            instructions.push(Instruction {
                opcode: Opcode::Jump { dest: Block(target.0 as u32) },
                args: vec![],
                results: vec![],
            });
        }
        Terminator::Return => {
            let args = return_args(ctx, has_return_value)?;
            instructions.push(Instruction { opcode: Opcode::Return, args, results: vec![] });
        }
        Terminator::Unreachable => {
            // Model unreachable as a diverging abort call instead of
            // fabricating a normal return path.
            instructions.push(abort_call_instruction());
        }
        Terminator::SwitchInt { discr, targets, otherwise, span: _ } => {
            let discr_val = ctx.resolve_operand(discr, instructions)?;

            if targets.len() == 1 {
                // Binary branch: if discr == value then target else otherwise.
                let (value, target) = &targets[0];
                let then_dest = conditional_edge_dest(target.0, ctx, block_params)?;
                let else_dest = conditional_edge_dest(otherwise.0, ctx, block_params)?;
                // Emit: cmp = icmp eq(discr, value)
                let const_val = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::I64, imm: *value as i64 },
                    args: vec![],
                    results: vec![const_val],
                });
                let cmp_val = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Icmp { cond: IntCC::Equal },
                    args: vec![discr_val, const_val],
                    results: vec![cmp_val],
                });
                instructions.push(Instruction {
                    opcode: Opcode::Brif { cond: cmp_val, then_dest, else_dest },
                    args: vec![cmp_val],
                    results: vec![],
                });
            } else {
                // Multi-way: emit a Switch instruction.
                let mut cases = Vec::with_capacity(targets.len());
                for (val, blk) in targets {
                    cases.push((*val as i64, conditional_edge_dest(blk.0, ctx, block_params)?));
                }
                let default = conditional_edge_dest(otherwise.0, ctx, block_params)?;
                instructions.push(Instruction {
                    opcode: Opcode::Switch { cases, default },
                    args: vec![discr_val],
                    results: vec![],
                });
            }
        }
        Terminator::Assert { cond, expected, msg: _, target, span: _ } => {
            // Assert: branch to target if cond == expected, else panic block.
            // The panic block is a dedicated block containing an abort call,
            // lazily allocated and inserted by lower_body_to_lir.
            let cond_val = ctx.resolve_operand(cond, instructions)?;
            let panic_blk = ctx.get_or_create_panic_block();
            let target_dest = conditional_edge_dest(target.0, ctx, block_params)?;

            if *expected {
                // assert(cond == true) -> brif cond, target, panic
                instructions.push(Instruction {
                    opcode: Opcode::Brif {
                        cond: cond_val,
                        then_dest: target_dest,
                        else_dest: panic_blk,
                    },
                    args: vec![cond_val],
                    results: vec![],
                });
            } else {
                // assert(cond == false) -> brif cond, panic, target
                instructions.push(Instruction {
                    opcode: Opcode::Brif {
                        cond: cond_val,
                        then_dest: panic_blk,
                        else_dest: target_dest,
                    },
                    args: vec![cond_val],
                    results: vec![],
                });
            }
        }
        Terminator::Call { func: callee, args, dest, target, atomic, .. } => {
            if let Some(atomic) = atomic {
                let result_dest = atomic.dest.as_ref().unwrap_or(dest);
                let ordering = map_atomic_ordering(&atomic.ordering);

                match atomic.op_kind {
                    AtomicOpKind::Load => {
                        let ptr = ctx.resolve_place(&atomic.place, instructions)?;
                        let ty = ctx.atomic_lir_ty(&atomic.place)?;
                        let result = ctx.fresh_value();
                        instructions.push(Instruction {
                            opcode: Opcode::AtomicLoad { ty, ordering },
                            args: vec![ptr],
                            results: vec![result],
                        });
                        assign_to_place(result_dest, result, ctx, instructions)?;
                    }
                    AtomicOpKind::Store => {
                        let value_operand = args.get(1).ok_or_else(|| {
                            BridgeError::InvalidMir(
                                "atomic store requires value operand at args[1]".to_string(),
                            )
                        })?;
                        let value = ctx.resolve_operand(value_operand, instructions)?;
                        let ptr = ctx.resolve_place(&atomic.place, instructions)?;
                        instructions.push(Instruction {
                            opcode: Opcode::AtomicStore { ordering },
                            args: vec![value, ptr],
                            results: vec![],
                        });
                    }
                    AtomicOpKind::Fence | AtomicOpKind::CompilerFence => {
                        instructions.push(Instruction {
                            opcode: Opcode::Fence { ordering },
                            args: vec![],
                            results: vec![],
                        });
                    }
                    AtomicOpKind::FetchAdd
                    | AtomicOpKind::FetchSub
                    | AtomicOpKind::FetchAnd
                    | AtomicOpKind::FetchOr
                    | AtomicOpKind::FetchXor
                    | AtomicOpKind::Exchange => {
                        let value_operand = args.get(1).ok_or_else(|| {
                            BridgeError::InvalidMir(format!(
                                "atomic {:?} requires value operand at args[1]",
                                atomic.op_kind
                            ))
                        })?;
                        let value = ctx.resolve_operand(value_operand, instructions)?;
                        let ptr = ctx.resolve_place(&atomic.place, instructions)?;
                        let ty = ctx.atomic_lir_ty(&atomic.place)?;
                        let op = map_atomic_rmw_op(atomic.op_kind)?;
                        let result = ctx.fresh_value();
                        instructions.push(Instruction {
                            opcode: Opcode::AtomicRmw { op, ty, ordering },
                            args: vec![value, ptr],
                            results: vec![result],
                        });
                        assign_to_place(result_dest, result, ctx, instructions)?;
                    }
                    AtomicOpKind::CompareExchange | AtomicOpKind::CompareExchangeWeak => {
                        let expected_operand = args.get(1).ok_or_else(|| {
                            BridgeError::InvalidMir(
                                "atomic compare_exchange requires expected operand at args[1]"
                                    .to_string(),
                            )
                        })?;
                        let desired_operand = args.get(2).ok_or_else(|| {
                            BridgeError::InvalidMir(
                                "atomic compare_exchange requires desired operand at args[2]"
                                    .to_string(),
                            )
                        })?;
                        let expected = ctx.resolve_operand(expected_operand, instructions)?;
                        let desired = ctx.resolve_operand(desired_operand, instructions)?;
                        let ptr = ctx.resolve_place(&atomic.place, instructions)?;
                        let ty = ctx.atomic_lir_ty(&atomic.place)?;
                        let result = ctx.fresh_value();
                        instructions.push(Instruction {
                            opcode: Opcode::CmpXchg { ty, ordering },
                            args: vec![expected, desired, ptr],
                            results: vec![result],
                        });
                        assign_to_place(result_dest, result, ctx, instructions)?;
                    }
                    AtomicOpKind::FetchNand | AtomicOpKind::FetchMin | AtomicOpKind::FetchMax => {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "atomic op kind has no LIR equivalent: {:?}",
                            atomic.op_kind
                        )));
                    }
                    // tRust: non-exhaustive fallback for future AtomicOpKind variants
                    _ => {
                        return Err(BridgeError::UnsupportedOp(format!(
                            "unknown atomic op kind: {:?}",
                            atomic.op_kind
                        )));
                    }
                }

                if let Some(cont) = target {
                    emit_block_param_copies(cont.0, ctx, instructions, block_params)?;
                    instructions.push(Instruction {
                        opcode: Opcode::Jump { dest: Block(cont.0 as u32) },
                        args: vec![],
                        results: vec![],
                    });
                }

                return Ok(());
            }

            // Resolve call arguments.
            let mut arg_vals = Vec::with_capacity(args.len());
            for arg in args {
                arg_vals.push(ctx.resolve_operand(arg, instructions)?);
            }

            // Determine result value for the call destination.
            let call_result = ctx.fresh_value();
            let call_result_ty = map_lowering_type(&ctx.place_ty(dest)?)?;
            ctx.record_value_type(call_result, call_result_ty);

            instructions.push(Instruction {
                opcode: Opcode::Call { name: callee.clone() },
                args: arg_vals,
                results: vec![call_result],
            });

            // Assign the call result to the destination place.
            if dest.projections.is_empty() {
                ctx.local_values.insert(dest.local, call_result);
            } else {
                // For projected destinations, compute the address and store.
                let addr = ctx.resolve_place_addr(dest, instructions)?;
                instructions.push(Instruction {
                    opcode: Opcode::Store,
                    args: vec![call_result, addr],
                    results: vec![],
                });
            }

            // If there is a continuation block, emit a jump to it.
            if let Some(cont) = target {
                emit_block_param_copies(cont.0, ctx, instructions, block_params)?;
                instructions.push(Instruction {
                    opcode: Opcode::Jump { dest: Block(cont.0 as u32) },
                    args: vec![],
                    results: vec![],
                });
            }
        }
        // tRust: #828 — elaborate drops for non-trivially-Copy values.
        Terminator::Drop { place, target, .. } => {
            let place_ty = ctx.local_ty(place.local)?.clone();
            if !is_trivially_copy_ty(&place_ty) {
                let addr = if place.projections.is_empty() {
                    let slot = ctx.ensure_local_stack_slot(place.local)?;
                    ctx.emit_stack_addr(slot, instructions)
                } else {
                    ctx.resolve_place_addr(place, instructions)?
                };
                let drop_result = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Call {
                        name: format!("core::ptr::drop_in_place::<{:?}>", place_ty),
                    },
                    args: vec![addr],
                    results: vec![drop_result],
                });
            }

            emit_block_param_copies(target.0, ctx, instructions, block_params)?;
            instructions.push(Instruction {
                opcode: Opcode::Jump { dest: Block(target.0 as u32) },
                args: vec![],
                results: vec![],
            });
        }
        _ => {
            return Err(BridgeError::UnsupportedOp("unknown terminator variant".to_string()));
        }
    }
    Ok(())
}
