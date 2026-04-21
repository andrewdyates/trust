//! trust-llvm2-bridge: Bridge between trust-types VerifiableFunction and LLVM2 LIR
//!
//! Converts trust-types IR (VerifiableFunction, BasicBlock, Statement, Terminator)
//! into LLVM2 LIR (Function, BasicBlock, Instruction) for verified code generation.
//!
//! Scope: scalar functions with calls and integer casts. Memory operations
//! return `BridgeError::UnsupportedOp` for now.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// tRust: Allow std HashMap — not in compiler context.
#![allow(clippy::module_name_repetitions)]

use trust_types::fx::FxHashMap;

use llvm2_lower::function::{BasicBlock as LirBlock, Function as LirFunction, Signature};
use llvm2_lower::instructions::{Block, Instruction, IntCC, Opcode, Value};
use llvm2_lower::types::Type as LirType;
use trust_types::{
    BasicBlock as TrustBlock, BinOp, ConstValue, LocalDecl, Operand, Place, Rvalue,
    Statement, Terminator, Ty, UnOp, VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors during trust-types to LLVM2 LIR conversion.
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
// Type mapping: trust-types Ty -> llvm2-lower Type
// ---------------------------------------------------------------------------

/// Convert a trust-types `Ty` to an LLVM2 LIR `Type`.
///
/// Only scalar types are supported. References, raw pointers, slices, arrays,
/// tuples, and ADTs return `BridgeError::UnsupportedType` for now.
pub fn map_type(ty: &Ty) -> Result<LirType, BridgeError> {
    match ty {
        Ty::Bool => Ok(LirType::B1),
        Ty::Int { width: 8, .. } => Ok(LirType::I8),
        Ty::Int { width: 16, .. } => Ok(LirType::I16),
        Ty::Int { width: 32, .. } => Ok(LirType::I32),
        Ty::Int { width: 64, .. } => Ok(LirType::I64),
        Ty::Int { width: 128, .. } => Ok(LirType::I128),
        Ty::Float { width: 32 } => Ok(LirType::F32),
        Ty::Float { width: 64 } => Ok(LirType::F64),
        Ty::Unit => Ok(LirType::B1), // Unit is zero-sized; use B1 as placeholder
        Ty::Bv(w) => match w {
            8 => Ok(LirType::I8),
            16 => Ok(LirType::I16),
            32 => Ok(LirType::I32),
            64 => Ok(LirType::I64),
            128 => Ok(LirType::I128),
            _ => Err(BridgeError::UnsupportedType(format!("Bv({w})"))),
        },
        other => Err(BridgeError::UnsupportedType(format!("{other:?}"))),
    }
}

// ---------------------------------------------------------------------------
// BinOp mapping: trust-types BinOp -> Opcode
// ---------------------------------------------------------------------------

/// Convert a trust-types `BinOp` to an LLVM2 LIR `Opcode`.
///
/// The `signed` parameter controls whether division/remainder use signed
/// or unsigned variants. For comparisons, it controls signed vs unsigned
/// condition codes.
pub fn map_binop(op: BinOp, signed: bool) -> Result<Opcode, BridgeError> {
    match op {
        BinOp::Add => Ok(Opcode::Iadd),
        BinOp::Sub => Ok(Opcode::Isub),
        BinOp::Mul => Ok(Opcode::Imul),
        BinOp::Div if signed => Ok(Opcode::Sdiv),
        BinOp::Div => Ok(Opcode::Udiv),
        BinOp::Rem if signed => Ok(Opcode::Srem),
        BinOp::Rem => Ok(Opcode::Urem),
        BinOp::Eq => Ok(Opcode::Icmp { cond: IntCC::Equal }),
        BinOp::Ne => Ok(Opcode::Icmp { cond: IntCC::NotEqual }),
        BinOp::Lt if signed => Ok(Opcode::Icmp { cond: IntCC::SignedLessThan }),
        BinOp::Lt => Ok(Opcode::Icmp { cond: IntCC::UnsignedLessThan }),
        BinOp::Le if signed => Ok(Opcode::Icmp { cond: IntCC::SignedLessThanOrEqual }),
        BinOp::Le => Ok(Opcode::Icmp { cond: IntCC::UnsignedLessThanOrEqual }),
        BinOp::Gt if signed => Ok(Opcode::Icmp { cond: IntCC::SignedGreaterThan }),
        BinOp::Gt => Ok(Opcode::Icmp { cond: IntCC::UnsignedGreaterThan }),
        BinOp::Ge if signed => Ok(Opcode::Icmp { cond: IntCC::SignedGreaterThanOrEqual }),
        BinOp::Ge => Ok(Opcode::Icmp { cond: IntCC::UnsignedGreaterThanOrEqual }),
        BinOp::BitAnd => Ok(Opcode::Band),
        BinOp::BitOr => Ok(Opcode::Bor),
        BinOp::BitXor => Ok(Opcode::Bxor),
        BinOp::Shl => Ok(Opcode::Ishl),
        BinOp::Shr if signed => Ok(Opcode::Sshr),
        BinOp::Shr => Ok(Opcode::Ushr),
        BinOp::Cmp => Err(BridgeError::UnsupportedOp(
            "three-way Cmp not yet supported in LIR".to_string(),
        )),
        _ => Err(BridgeError::UnsupportedOp(format!("{op:?}"))),
    }
}

/// Convert a trust-types `UnOp` to an LLVM2 LIR `Opcode`.
pub fn map_unop(op: UnOp) -> Result<Opcode, BridgeError> {
    match op {
        UnOp::Not => Ok(Opcode::Bnot),
        UnOp::Neg => Ok(Opcode::Ineg),
        UnOp::PtrMetadata => Err(BridgeError::UnsupportedOp(
            "PtrMetadata not yet supported in LIR".to_string(),
        )),
        _ => Err(BridgeError::UnsupportedOp(format!("{op:?}"))),
    }
}

// ---------------------------------------------------------------------------
// Lowering state
// ---------------------------------------------------------------------------

/// Internal state for the lowering pass.
struct LoweringCtx<'a> {
    /// Local variable declarations from the trust-types body.
    locals: &'a [LocalDecl],
    /// Map from trust-types local index to LIR Value.
    local_values: FxHashMap<usize, Value>,
    /// Next available Value id.
    next_value: u32,
}

impl<'a> LoweringCtx<'a> {
    fn new(locals: &'a [LocalDecl], arg_count: usize) -> Self {
        let mut ctx = Self {
            locals,
            local_values: FxHashMap::with_capacity_and_hasher(locals.len(), Default::default()),
            next_value: 0,
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
        self.local_values
            .get(&index)
            .copied()
            .ok_or(BridgeError::MissingLocal(index))
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
        self.local_ty(index)
            .map(|ty| ty.is_signed())
            .unwrap_or(false)
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

    /// Resolve an Operand to a LIR Value, emitting Iconst/Fconst as needed.
    fn resolve_operand(
        &mut self,
        op: &Operand,
        instructions: &mut Vec<Instruction>,
    ) -> Result<Value, BridgeError> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                self.resolve_place(place)
            }
            Operand::Constant(cv) => self.emit_const(cv, instructions),
            Operand::Symbolic(_) => Err(BridgeError::UnsupportedOp(
                "Symbolic operands not supported in LIR lowering".to_string(),
            )),
            _ => Err(BridgeError::UnsupportedOp(
                "unknown operand variant".to_string(),
            )),
        }
    }

    /// Resolve a Place to a LIR Value.
    ///
    /// Only simple locals (no projections) are supported for now.
    fn resolve_place(&self, place: &Place) -> Result<Value, BridgeError> {
        if !place.projections.is_empty() {
            return Err(BridgeError::UnsupportedOp(format!(
                "place projections not yet supported: _{} with {} projections",
                place.local,
                place.projections.len()
            )));
        }
        self.local_value(place.local)
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
                let opcode = Opcode::Iconst {
                    ty: LirType::B1,
                    imm: i64::from(*b),
                };
                (opcode, v)
            }
            ConstValue::Int(val) => {
                let v = self.fresh_value();
                // Default to I64 for signed constants; the actual width
                // depends on context but I64 is safe for all values.
                let opcode = Opcode::Iconst {
                    ty: LirType::I64,
                    imm: *val as i64,
                };
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
                let opcode = Opcode::Iconst {
                    ty,
                    imm: *val as i64,
                };
                (opcode, v)
            }
            ConstValue::Float(val) => {
                let v = self.fresh_value();
                let opcode = Opcode::Fconst {
                    ty: LirType::F64,
                    imm: *val,
                };
                (opcode, v)
            }
            ConstValue::Unit => {
                // Unit is zero-sized; emit a B1 const 0 as placeholder.
                let v = self.fresh_value();
                let opcode = Opcode::Iconst {
                    ty: LirType::B1,
                    imm: 0,
                };
                (opcode, v)
            }
            _ => {
                return Err(BridgeError::UnsupportedOp(
                    "unknown constant variant".to_string(),
                ));
            }
        };
        instructions.push(Instruction {
            opcode,
            args: vec![],
            results: vec![result],
        });
        Ok(result)
    }
}

// ---------------------------------------------------------------------------
// Public API: lower_to_lir
// ---------------------------------------------------------------------------

/// Convert a trust-types `VerifiableFunction` to an LLVM2 LIR `Function`.
///
/// This is the primary entry point for the bridge. It maps the function
/// signature, basic blocks, statements, and terminators to LIR equivalents.
///
/// # Limitations
///
/// - Only scalar types are supported (no references, pointers, tuples, ADTs).
/// - Place projections (field access, deref, index) are not supported.
/// - Memory operations (Load/Store) return `BridgeError::UnsupportedOp`.
/// - Symbolic operands are not supported.
#[must_use = "returns the lowered LIR function"]
pub fn lower_to_lir(func: &VerifiableFunction) -> Result<LirFunction, BridgeError> {
    lower_body_to_lir(&func.name, &func.body)
}

/// Convert a trust-types `VerifiableBody` to an LLVM2 LIR `Function`.
///
/// Separated from `lower_to_lir` to allow testing with bodies directly.
pub fn lower_body_to_lir(name: &str, body: &VerifiableBody) -> Result<LirFunction, BridgeError> {
    let mut ctx = LoweringCtx::new(&body.locals, body.arg_count);

    // Build signature from locals: args are locals[1..=arg_count], return is locals[0].
    let return_ty = map_type(&body.return_ty)?;
    let mut param_types = Vec::with_capacity(body.arg_count);
    for i in 1..=body.arg_count {
        let local = body
            .locals
            .iter()
            .find(|l| l.index == i)
            .ok_or(BridgeError::MissingLocal(i))?;
        param_types.push(map_type(&local.ty)?);
    }
    let returns = if matches!(body.return_ty, Ty::Unit | Ty::Never) {
        vec![]
    } else {
        vec![return_ty]
    };
    let signature = Signature {
        params: param_types,
        returns,
    };

    // Convert each basic block.
    let mut blocks = std::collections::HashMap::with_capacity(body.blocks.len());
    for bb in &body.blocks {
        let block = Block(bb.id.0 as u32);
        let lir_block = lower_block(bb, &mut ctx)?;
        blocks.insert(block, lir_block);
    }

    let entry_block = if body.blocks.is_empty() {
        Block(0)
    } else {
        Block(body.blocks[0].id.0 as u32)
    };

    Ok(LirFunction {
        name: name.to_string(),
        signature,
        blocks,
        entry_block,
    })
}

// ---------------------------------------------------------------------------
// Block lowering
// ---------------------------------------------------------------------------

fn lower_block(bb: &TrustBlock, ctx: &mut LoweringCtx<'_>) -> Result<LirBlock, BridgeError> {
    let mut instructions = Vec::new();

    // Lower each statement.
    for stmt in &bb.stmts {
        lower_statement(stmt, ctx, &mut instructions)?;
    }

    // Lower the terminator.
    lower_terminator(&bb.terminator, ctx, &mut instructions)?;

    Ok(LirBlock {
        params: vec![],
        instructions,
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
        Statement::Assign {
            place,
            rvalue,
            span: _,
        } => {
            lower_rvalue(place, rvalue, ctx, instructions)?;
        }
        Statement::Nop => {}
        _ => {
            return Err(BridgeError::UnsupportedOp(
                "unknown statement variant".to_string(),
            ));
        }
    }
    Ok(())
}

fn lower_rvalue(
    dest: &Place,
    rvalue: &Rvalue,
    ctx: &mut LoweringCtx<'_>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), BridgeError> {
    // For simple locals, we can assign to the pre-allocated value.
    // For projections, we need to emit a store — not yet supported.
    if !dest.projections.is_empty() {
        return Err(BridgeError::UnsupportedOp(format!(
            "assignment to projected place _{} not supported",
            dest.local
        )));
    }

    let dest_val = ctx.local_value(dest.local)?;

    match rvalue {
        Rvalue::Use(operand) => {
            // Simple copy/move: the dest takes the value of the operand.
            // In SSA form this is just a value alias. We emit a copy via
            // Iconst(0) + Iadd to maintain SSA discipline.
            let src = ctx.resolve_operand(operand, instructions)?;
            // Emit: dest = iadd(src, 0) as a copy.
            // Actually, we can just emit the source directly as the result
            // by updating the local_values map.
            ctx.local_values.insert(dest.local, src);
        }
        Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let lhs_val = ctx.resolve_operand(lhs, instructions)?;
            let rhs_val = ctx.resolve_operand(rhs, instructions)?;

            // Determine signedness from the destination local's type.
            let signed = ctx.is_signed(dest.local);
            let opcode = map_binop(*op, signed)?;

            instructions.push(Instruction {
                opcode,
                args: vec![lhs_val, rhs_val],
                results: vec![dest_val],
            });
            // Ensure the dest maps to this value.
            ctx.local_values.insert(dest.local, dest_val);
        }
        Rvalue::UnaryOp(op, operand) => {
            let src = ctx.resolve_operand(operand, instructions)?;
            let opcode = map_unop(*op)?;
            instructions.push(Instruction {
                opcode,
                args: vec![src],
                results: vec![dest_val],
            });
            ctx.local_values.insert(dest.local, dest_val);
        }
        Rvalue::Cast(operand, target_ty) => {
            let src = ctx.resolve_operand(operand, instructions)?;

            // Determine source type from the operand.
            let src_ty = match operand {
                Operand::Copy(p) | Operand::Move(p) => ctx.local_ty(p.local).ok(),
                _ => None,
            };

            let src_width = src_ty.and_then(LoweringCtx::ty_bit_width);
            let dst_width = LoweringCtx::ty_bit_width(target_ty);

            match (src_width, dst_width) {
                (Some(sw), Some(dw)) if sw == dw => {
                    // Same width: treat as copy.
                    ctx.local_values.insert(dest.local, src);
                }
                (Some(_), Some(dw)) if src_width.unwrap_or(0) > dw => {
                    // Narrowing: emit Trunc.
                    let to_ty = map_type(target_ty)?;
                    instructions.push(Instruction {
                        opcode: Opcode::Trunc { to_ty },
                        args: vec![src],
                        results: vec![dest_val],
                    });
                    ctx.local_values.insert(dest.local, dest_val);
                }
                (Some(_), Some(_)) => {
                    // Widening: emit Sextend or Uextend based on source signedness.
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
                    ctx.local_values.insert(dest.local, dest_val);
                }
                _ => {
                    // Unknown widths (e.g., float casts, pointer casts) — copy for now.
                    ctx.local_values.insert(dest.local, src);
                }
            }
        }
        Rvalue::Discriminant(_place) => {
            // Discriminant is an integer load from an enum — treat as UnsupportedOp.
            return Err(BridgeError::UnsupportedOp(
                "Discriminant rvalue not yet supported".to_string(),
            ));
        }
        Rvalue::Len(_place) => {
            return Err(BridgeError::UnsupportedOp(
                "Len rvalue not yet supported".to_string(),
            ));
        }
        Rvalue::Ref { .. } | Rvalue::AddressOf(..) => {
            return Err(BridgeError::UnsupportedOp(
                "reference/address-of not yet supported in LIR".to_string(),
            ));
        }
        Rvalue::Aggregate(..) => {
            return Err(BridgeError::UnsupportedOp(
                "aggregate construction not yet supported in LIR".to_string(),
            ));
        }
        Rvalue::Repeat(..) => {
            return Err(BridgeError::UnsupportedOp(
                "array repeat not yet supported in LIR".to_string(),
            ));
        }
        Rvalue::CopyForDeref(place) => {
            let src = ctx.resolve_place(place)?;
            ctx.local_values.insert(dest.local, src);
        }
        _ => {
            return Err(BridgeError::UnsupportedOp(
                "unknown rvalue variant".to_string(),
            ));
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
) -> Result<(), BridgeError> {
    match term {
        Terminator::Goto(target) => {
            instructions.push(Instruction {
                opcode: Opcode::Jump {
                    dest: Block(target.0 as u32),
                },
                args: vec![],
                results: vec![],
            });
        }
        Terminator::Return => {
            instructions.push(Instruction {
                opcode: Opcode::Return,
                args: vec![],
                results: vec![],
            });
        }
        Terminator::Unreachable => {
            // Emit as a return (unreachable code should never execute).
            instructions.push(Instruction {
                opcode: Opcode::Return,
                args: vec![],
                results: vec![],
            });
        }
        Terminator::SwitchInt {
            discr,
            targets,
            otherwise,
            span: _,
        } => {
            let discr_val = ctx.resolve_operand(discr, instructions)?;

            if targets.len() == 1 {
                // Binary branch: if discr == value then target else otherwise.
                let (value, target) = &targets[0];
                // Emit: cmp = icmp eq(discr, value)
                let const_val = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Iconst {
                        ty: LirType::I64,
                        imm: *value as i64,
                    },
                    args: vec![],
                    results: vec![const_val],
                });
                let cmp_val = ctx.fresh_value();
                instructions.push(Instruction {
                    opcode: Opcode::Icmp {
                        cond: IntCC::Equal,
                    },
                    args: vec![discr_val, const_val],
                    results: vec![cmp_val],
                });
                instructions.push(Instruction {
                    opcode: Opcode::Brif {
                        cond: cmp_val,
                        then_dest: Block(target.0 as u32),
                        else_dest: Block(otherwise.0 as u32),
                    },
                    args: vec![cmp_val],
                    results: vec![],
                });
            } else {
                // Multi-way: emit a Switch instruction.
                let cases: Vec<(i64, Block)> = targets
                    .iter()
                    .map(|(val, blk)| (*val as i64, Block(blk.0 as u32)))
                    .collect();
                instructions.push(Instruction {
                    opcode: Opcode::Switch {
                        cases,
                        default: Block(otherwise.0 as u32),
                    },
                    args: vec![discr_val],
                    results: vec![],
                });
            }
        }
        Terminator::Assert {
            cond,
            expected,
            msg: _,
            target,
            span: _,
        } => {
            // Assert: branch to target if cond == expected, else unreachable.
            // We model this as a conditional branch. The "failure" path is
            // a return (representing a panic/abort).
            let cond_val = ctx.resolve_operand(cond, instructions)?;

            if *expected {
                // assert(cond == true) -> brif cond, target, unreachable
                // Create an implicit "panic" block that returns.
                // For now, branch to target on true, return on false.
                let panic_block = ctx.fresh_value(); // dummy, not used
                let _ = panic_block;
                instructions.push(Instruction {
                    opcode: Opcode::Brif {
                        cond: cond_val,
                        then_dest: Block(target.0 as u32),
                        // For the false branch, we'd need a panic block.
                        // Use an invalid block that gets handled by the caller.
                        else_dest: Block(u32::MAX),
                    },
                    args: vec![cond_val],
                    results: vec![],
                });
            } else {
                // assert(cond == false) -> brif cond, unreachable, target
                instructions.push(Instruction {
                    opcode: Opcode::Brif {
                        cond: cond_val,
                        then_dest: Block(u32::MAX), // panic path
                        else_dest: Block(target.0 as u32),
                    },
                    args: vec![cond_val],
                    results: vec![],
                });
            }
        }
        Terminator::Call {
            func: callee,
            args,
            dest,
            target,
            ..
        } => {
            // Resolve call arguments.
            let mut arg_vals = Vec::with_capacity(args.len());
            for arg in args {
                arg_vals.push(ctx.resolve_operand(arg, instructions)?);
            }

            // Determine result value for the call destination.
            let dest_val = ctx.resolve_place(dest)?;

            instructions.push(Instruction {
                opcode: Opcode::Call {
                    name: callee.clone(),
                },
                args: arg_vals,
                results: vec![dest_val],
            });

            // If there is a continuation block, emit a jump to it.
            if let Some(cont) = target {
                instructions.push(Instruction {
                    opcode: Opcode::Jump {
                        dest: Block(cont.0 as u32),
                    },
                    args: vec![],
                    results: vec![],
                });
            }
        }
        Terminator::Drop { target, .. } => {
            // Drop is a no-op for scalar types; just jump to target.
            instructions.push(Instruction {
                opcode: Opcode::Jump {
                    dest: Block(target.0 as u32),
                },
                args: vec![],
                results: vec![],
            });
        }
        _ => {
            return Err(BridgeError::UnsupportedOp(
                "unknown terminator variant".to_string(),
            ));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Lift: LIR -> VerifiableFunction (inverse of lower_to_lir)
// ---------------------------------------------------------------------------

/// Reverse mapping: LLVM2 LIR `Type` -> trust-types `Ty`.
fn unmap_type(ty: &LirType) -> Ty {
    match ty {
        LirType::B1 => Ty::Bool,
        LirType::I8 => Ty::i8(),
        LirType::I16 => Ty::i16(),
        LirType::I32 => Ty::i32(),
        LirType::I64 => Ty::i64(),
        LirType::I128 => Ty::i128(),
        LirType::F32 => Ty::f32_ty(),
        LirType::F64 => Ty::f64_ty(),
        // V128/Struct/Array are not representable in trust-types; use Bv(128) as placeholder.
        _ => Ty::Bv(128),
    }
}

/// Reverse mapping: LIR `Opcode` (arithmetic) -> trust-types `BinOp`.
fn unmap_binop(opcode: &Opcode) -> Option<BinOp> {
    match opcode {
        Opcode::Iadd => Some(BinOp::Add),
        Opcode::Isub => Some(BinOp::Sub),
        Opcode::Imul => Some(BinOp::Mul),
        Opcode::Sdiv | Opcode::Udiv => Some(BinOp::Div),
        Opcode::Srem | Opcode::Urem => Some(BinOp::Rem),
        Opcode::Band => Some(BinOp::BitAnd),
        Opcode::Bor => Some(BinOp::BitOr),
        Opcode::Bxor => Some(BinOp::BitXor),
        Opcode::Ishl => Some(BinOp::Shl),
        Opcode::Ushr | Opcode::Sshr => Some(BinOp::Shr),
        Opcode::Icmp { cond } => match cond {
            IntCC::Equal => Some(BinOp::Eq),
            IntCC::NotEqual => Some(BinOp::Ne),
            IntCC::SignedLessThan | IntCC::UnsignedLessThan => Some(BinOp::Lt),
            IntCC::SignedLessThanOrEqual | IntCC::UnsignedLessThanOrEqual => Some(BinOp::Le),
            IntCC::SignedGreaterThan | IntCC::UnsignedGreaterThan => Some(BinOp::Gt),
            IntCC::SignedGreaterThanOrEqual | IntCC::UnsignedGreaterThanOrEqual => Some(BinOp::Ge),
        },
        _ => None,
    }
}

/// Reverse mapping: LIR unary `Opcode` -> trust-types `UnOp`.
fn unmap_unop(opcode: &Opcode) -> Option<UnOp> {
    match opcode {
        Opcode::Bnot => Some(UnOp::Not),
        Opcode::Ineg => Some(UnOp::Neg),
        _ => None,
    }
}

/// Reconstruct a `VerifiableFunction` from an LLVM2 LIR `Function`.
///
/// This is the inverse of `lower_to_lir`, used for translation validation:
/// the original MIR (source) is compared against the lifted LIR (target)
/// to prove semantics are preserved across the lowering transformation.
///
/// # Limitations
///
/// Same scope as `lower_to_lir`: scalar leaf functions only.
/// Unsupported LIR opcodes produce `BridgeError::UnsupportedOp`.
pub fn lift_from_lir(lir: &LirFunction) -> Result<VerifiableFunction, BridgeError> {
    // Build locals: return slot (index 0), then args (1..=param_count).
    let return_ty = lir
        .signature
        .returns
        .first()
        .map(unmap_type)
        .unwrap_or(Ty::Unit);
    let arg_count = lir.signature.params.len();

    let mut locals = Vec::with_capacity(1 + arg_count);
    locals.push(LocalDecl { index: 0, ty: return_ty.clone(), name: None });
    for (i, param_ty) in lir.signature.params.iter().enumerate() {
        locals.push(LocalDecl {
            index: i + 1,
            ty: unmap_type(param_ty),
            name: Some(format!("arg{}", i + 1)),
        });
    }

    // Track Value -> local index mapping.
    // Convention from lower_to_lir: Value(0)..Value(arg_count-1) are args,
    // Value(arg_count) is the return slot.
    let mut value_to_local: FxHashMap<Value, usize> = FxHashMap::default();
    for i in 0..arg_count {
        value_to_local.insert(Value(i as u32), i + 1); // arg locals start at 1
    }
    value_to_local.insert(Value(arg_count as u32), 0); // return slot

    // Sort blocks by id for deterministic output.
    let mut block_ids: Vec<Block> = lir.blocks.keys().copied().collect();
    block_ids.sort_by_key(|b| b.0);

    let mut trust_blocks = Vec::with_capacity(block_ids.len());
    let mut next_local = 1 + arg_count; // next local index for temporaries

    for block_id in &block_ids {
        let lir_block = &lir.blocks[block_id];
        let mut stmts = Vec::new();
        let mut terminator = Terminator::Return; // default, overridden below

        for instr in &lir_block.instructions {
            match &instr.opcode {
                Opcode::Iconst { ty: _, imm } => {
                    // Allocate a local for the constant result.
                    if let Some(&result_val) = instr.results.first() {
                        let local_idx = next_local;
                        next_local += 1;
                        locals.push(LocalDecl {
                            index: local_idx,
                            ty: return_ty.clone(), // approximate
                            name: None,
                        });
                        value_to_local.insert(result_val, local_idx);
                        stmts.push(Statement::Assign {
                            place: Place::local(local_idx),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(*imm as i128))),
                            span: trust_types::SourceSpan::default(),
                        });
                    }
                }
                Opcode::Fconst { ty: _, imm } => {
                    if let Some(&result_val) = instr.results.first() {
                        let local_idx = next_local;
                        next_local += 1;
                        locals.push(LocalDecl {
                            index: local_idx,
                            ty: Ty::f64_ty(),
                            name: None,
                        });
                        value_to_local.insert(result_val, local_idx);
                        stmts.push(Statement::Assign {
                            place: Place::local(local_idx),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Float(*imm))),
                            span: trust_types::SourceSpan::default(),
                        });
                    }
                }
                Opcode::Return => {
                    terminator = Terminator::Return;
                }
                Opcode::Jump { dest } => {
                    terminator = Terminator::Goto(trust_types::BlockId(dest.0 as usize));
                }
                Opcode::Brif { cond: _, then_dest, else_dest } => {
                    // Reconstruct as SwitchInt on the condition value.
                    // We don't track the condition value perfectly here,
                    // so use a symbolic approach.
                    let discr_local = instr
                        .args
                        .first()
                        .and_then(|v| value_to_local.get(v).copied())
                        .unwrap_or(0);
                    terminator = Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(discr_local)),
                        targets: vec![(1, trust_types::BlockId(then_dest.0 as usize))],
                        otherwise: trust_types::BlockId(else_dest.0 as usize),
                        span: trust_types::SourceSpan::default(),
                    };
                }
                opcode if unmap_binop(opcode).is_some() => {
                    let binop = unmap_binop(opcode).expect("checked above");
                    if instr.args.len() == 2 {
                        let lhs_local = value_to_local
                            .get(&instr.args[0])
                            .copied()
                            .ok_or_else(|| {
                                BridgeError::MissingLocal(instr.args[0].0 as usize)
                            })?;
                        let rhs_local = value_to_local
                            .get(&instr.args[1])
                            .copied()
                            .ok_or_else(|| {
                                BridgeError::MissingLocal(instr.args[1].0 as usize)
                            })?;

                        let dest_local = if let Some(&result_val) = instr.results.first() {
                            if let Some(&existing) = value_to_local.get(&result_val) {
                                existing
                            } else {
                                let idx = next_local;
                                next_local += 1;
                                locals.push(LocalDecl {
                                    index: idx,
                                    ty: return_ty.clone(),
                                    name: None,
                                });
                                value_to_local.insert(result_val, idx);
                                idx
                            }
                        } else {
                            return Err(BridgeError::UnsupportedOp(
                                "binary op with no result".to_string(),
                            ));
                        };

                        stmts.push(Statement::Assign {
                            place: Place::local(dest_local),
                            rvalue: Rvalue::BinaryOp(
                                binop,
                                Operand::Copy(Place::local(lhs_local)),
                                Operand::Copy(Place::local(rhs_local)),
                            ),
                            span: trust_types::SourceSpan::default(),
                        });
                    }
                }
                opcode if unmap_unop(opcode).is_some() => {
                    let unop = unmap_unop(opcode).expect("checked above");
                    if let Some(&arg_val) = instr.args.first() {
                        let src_local = value_to_local
                            .get(&arg_val)
                            .copied()
                            .ok_or(BridgeError::MissingLocal(arg_val.0 as usize))?;

                        let dest_local = if let Some(&result_val) = instr.results.first() {
                            if let Some(&existing) = value_to_local.get(&result_val) {
                                existing
                            } else {
                                let idx = next_local;
                                next_local += 1;
                                locals.push(LocalDecl {
                                    index: idx,
                                    ty: return_ty.clone(),
                                    name: None,
                                });
                                value_to_local.insert(result_val, idx);
                                idx
                            }
                        } else {
                            return Err(BridgeError::UnsupportedOp(
                                "unary op with no result".to_string(),
                            ));
                        };

                        stmts.push(Statement::Assign {
                            place: Place::local(dest_local),
                            rvalue: Rvalue::UnaryOp(unop, Operand::Copy(Place::local(src_local))),
                            span: trust_types::SourceSpan::default(),
                        });
                    }
                }
                Opcode::Sextend { .. } | Opcode::Uextend { .. } => {
                    // Treat extensions as copies for validation purposes.
                    if let (Some(&src_val), Some(&result_val)) =
                        (instr.args.first(), instr.results.first())
                    {
                        let src_local = value_to_local
                            .get(&src_val)
                            .copied()
                            .ok_or(BridgeError::MissingLocal(src_val.0 as usize))?;
                        value_to_local.insert(result_val, src_local);
                    }
                }
                Opcode::Switch { cases, default } => {
                    let discr_local = instr
                        .args
                        .first()
                        .and_then(|v| value_to_local.get(v).copied())
                        .unwrap_or(0);
                    let targets = cases
                        .iter()
                        .map(|(val, blk)| (*val as u128, trust_types::BlockId(blk.0 as usize)))
                        .collect();
                    terminator = Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(discr_local)),
                        targets,
                        otherwise: trust_types::BlockId(default.0 as usize),
                        span: trust_types::SourceSpan::default(),
                    };
                }
                other => {
                    return Err(BridgeError::UnsupportedOp(format!(
                        "cannot lift LIR opcode: {other:?}"
                    )));
                }
            }
        }

        trust_blocks.push(trust_types::BasicBlock {
            id: trust_types::BlockId(block_id.0 as usize),
            stmts,
            terminator,
        });
    }

    Ok(VerifiableFunction {
        name: format!("{}_lir", lir.name),
        def_path: format!("lir::{}", lir.name),
        span: trust_types::SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: trust_blocks,
            arg_count,
            return_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{
        BasicBlock as TrustBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
        SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
    };

    // -- Type mapping tests --

    #[test]
    fn test_map_type_bool() {
        assert_eq!(map_type(&Ty::Bool).unwrap(), LirType::B1);
    }

    #[test]
    fn test_map_type_integers() {
        assert_eq!(map_type(&Ty::i8()).unwrap(), LirType::I8);
        assert_eq!(map_type(&Ty::u8()).unwrap(), LirType::I8);
        assert_eq!(map_type(&Ty::i16()).unwrap(), LirType::I16);
        assert_eq!(map_type(&Ty::u16()).unwrap(), LirType::I16);
        assert_eq!(map_type(&Ty::i32()).unwrap(), LirType::I32);
        assert_eq!(map_type(&Ty::u32()).unwrap(), LirType::I32);
        assert_eq!(map_type(&Ty::i64()).unwrap(), LirType::I64);
        assert_eq!(map_type(&Ty::u64()).unwrap(), LirType::I64);
        assert_eq!(map_type(&Ty::i128()).unwrap(), LirType::I128);
        assert_eq!(map_type(&Ty::u128()).unwrap(), LirType::I128);
    }

    #[test]
    fn test_map_type_floats() {
        assert_eq!(map_type(&Ty::f32_ty()).unwrap(), LirType::F32);
        assert_eq!(map_type(&Ty::f64_ty()).unwrap(), LirType::F64);
    }

    #[test]
    fn test_map_type_unit() {
        // Unit maps to B1 as a placeholder.
        assert_eq!(map_type(&Ty::Unit).unwrap(), LirType::B1);
    }

    #[test]
    fn test_map_type_bv() {
        assert_eq!(map_type(&Ty::Bv(32)).unwrap(), LirType::I32);
        assert_eq!(map_type(&Ty::Bv(64)).unwrap(), LirType::I64);
    }

    #[test]
    fn test_map_type_unsupported() {
        assert!(map_type(&Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::i32())
        })
        .is_err());
        assert!(map_type(&Ty::Slice {
            elem: Box::new(Ty::i32())
        })
        .is_err());
    }

    // -- BinOp mapping tests --

    #[test]
    fn test_map_binop_arithmetic() {
        assert_eq!(map_binop(BinOp::Add, false).unwrap(), Opcode::Iadd);
        assert_eq!(map_binop(BinOp::Sub, false).unwrap(), Opcode::Isub);
        assert_eq!(map_binop(BinOp::Mul, false).unwrap(), Opcode::Imul);
        assert_eq!(map_binop(BinOp::Div, false).unwrap(), Opcode::Udiv);
        assert_eq!(map_binop(BinOp::Div, true).unwrap(), Opcode::Sdiv);
        assert_eq!(map_binop(BinOp::Rem, false).unwrap(), Opcode::Urem);
        assert_eq!(map_binop(BinOp::Rem, true).unwrap(), Opcode::Srem);
    }

    #[test]
    fn test_map_binop_comparison() {
        assert_eq!(
            map_binop(BinOp::Eq, false).unwrap(),
            Opcode::Icmp {
                cond: IntCC::Equal
            }
        );
        assert_eq!(
            map_binop(BinOp::Ne, false).unwrap(),
            Opcode::Icmp {
                cond: IntCC::NotEqual
            }
        );
        assert_eq!(
            map_binop(BinOp::Lt, true).unwrap(),
            Opcode::Icmp {
                cond: IntCC::SignedLessThan
            }
        );
        assert_eq!(
            map_binop(BinOp::Lt, false).unwrap(),
            Opcode::Icmp {
                cond: IntCC::UnsignedLessThan
            }
        );
    }

    #[test]
    fn test_map_binop_bitwise() {
        assert_eq!(map_binop(BinOp::BitAnd, false).unwrap(), Opcode::Band);
        assert_eq!(map_binop(BinOp::BitOr, false).unwrap(), Opcode::Bor);
        assert_eq!(map_binop(BinOp::BitXor, false).unwrap(), Opcode::Bxor);
        assert_eq!(map_binop(BinOp::Shl, false).unwrap(), Opcode::Ishl);
        assert_eq!(map_binop(BinOp::Shr, false).unwrap(), Opcode::Ushr);
        assert_eq!(map_binop(BinOp::Shr, true).unwrap(), Opcode::Sshr);
    }

    #[test]
    fn test_map_binop_cmp_unsupported() {
        assert!(map_binop(BinOp::Cmp, false).is_err());
    }

    // -- UnOp mapping tests --

    #[test]
    fn test_map_unop() {
        assert_eq!(map_unop(UnOp::Not).unwrap(), Opcode::Bnot);
        assert_eq!(map_unop(UnOp::Neg).unwrap(), Opcode::Ineg);
        assert!(map_unop(UnOp::PtrMetadata).is_err());
    }

    // -- Full function lowering tests --

    /// Helper: build the MIR for `fn add(a: i32, b: i32) -> i32 { a + b }`
    fn make_add_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "add".to_string(),
            def_path: "test::add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::i32(),
                        name: None,
                    }, // return
                    LocalDecl {
                        index: 1,
                        ty: Ty::i32(),
                        name: Some("a".into()),
                    },
                    LocalDecl {
                        index: 2,
                        ty: Ty::i32(),
                        name: Some("b".into()),
                    },
                ],
                blocks: vec![TrustBlock {
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
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_lower_add_function() {
        let func = make_add_function();
        let lir = lower_to_lir(&func).expect("should lower successfully");

        assert_eq!(lir.name, "add");
        assert_eq!(lir.signature.params.len(), 2);
        assert_eq!(lir.signature.params[0], LirType::I32);
        assert_eq!(lir.signature.params[1], LirType::I32);
        assert_eq!(lir.signature.returns.len(), 1);
        assert_eq!(lir.signature.returns[0], LirType::I32);
        assert_eq!(lir.blocks.len(), 1);
        assert_eq!(lir.entry_block, Block(0));

        let bb0 = &lir.blocks[&Block(0)];
        // Should have: iadd instruction + return
        assert!(bb0.instructions.len() >= 2);
        assert!(matches!(bb0.instructions.last().unwrap().opcode, Opcode::Return));
        // The add instruction should be an Iadd.
        let add_inst = bb0
            .instructions
            .iter()
            .find(|i| matches!(i.opcode, Opcode::Iadd))
            .expect("should have Iadd instruction");
        assert_eq!(add_inst.args.len(), 2);
        assert_eq!(add_inst.results.len(), 1);
    }

    #[test]
    fn test_lower_unit_return_function() {
        // fn noop() -> ()
        let func = VerifiableFunction {
            name: "noop".to_string(),
            def_path: "test::noop".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl {
                    index: 0,
                    ty: Ty::Unit,
                    name: None,
                }],
                blocks: vec![TrustBlock {
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

        let lir = lower_to_lir(&func).expect("should lower successfully");
        assert_eq!(lir.signature.params.len(), 0);
        assert!(lir.signature.returns.is_empty()); // Unit returns nothing
    }

    #[test]
    fn test_lower_constant_use() {
        // fn const_fn() -> i32 { 42 }
        let func = VerifiableFunction {
            name: "const_fn".to_string(),
            def_path: "test::const_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl {
                    index: 0,
                    ty: Ty::i32(),
                    name: None,
                }],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("should lower");
        let bb0 = &lir.blocks[&Block(0)];
        // Should have Iconst + Return
        assert!(bb0
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Iconst { .. })));
    }

    #[test]
    fn test_lower_goto_terminator() {
        let func = VerifiableFunction {
            name: "goto_fn".to_string(),
            def_path: "test::goto_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl {
                    index: 0,
                    ty: Ty::Unit,
                    name: None,
                }],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    TrustBlock {
                        id: BlockId(1),
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

        let lir = lower_to_lir(&func).expect("should lower");
        assert_eq!(lir.blocks.len(), 2);
        let bb0 = &lir.blocks[&Block(0)];
        assert!(matches!(
            bb0.instructions.last().unwrap().opcode,
            Opcode::Jump { dest: Block(1) }
        ));
    }

    #[test]
    fn test_lower_switch_int_binary() {
        // SwitchInt with one target = Brif
        let func = VerifiableFunction {
            name: "branch_fn".to_string(),
            def_path: "test::branch_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::Unit,
                        name: None,
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Bool,
                        name: Some("cond".into()),
                    },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    TrustBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                    TrustBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("should lower");
        let bb0 = &lir.blocks[&Block(0)];
        assert!(bb0.instructions.iter().any(|i| matches!(
            i.opcode,
            Opcode::Brif {
                then_dest: Block(1),
                else_dest: Block(2),
                ..
            }
        )));
    }

    #[test]
    fn test_lower_call_basic() {
        // Basic call lowering: call with no args and a continuation block.
        let func = VerifiableFunction {
            name: "call_fn".to_string(),
            def_path: "test::call_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl {
                    index: 0,
                    ty: Ty::i32(),
                    name: None,
                }],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "other_fn".to_string(),
                        args: vec![],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                }],
                arg_count: 0,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let result = lower_to_lir(&func);
        assert!(result.is_ok(), "call lowering should succeed");
        let lir = result.unwrap();
        let bb0 = &lir.blocks[&Block(0)];
        assert!(bb0
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Call { .. })));
    }

    #[test]
    fn test_lower_midpoint_function() {
        // The standard midpoint test: fn get_midpoint(a: u64, b: u64) -> u64 { (a + b) / 2 }
        // Uses CheckedBinaryOp for the add, and BinaryOp for the div.
        let func = VerifiableFunction {
            name: "get_midpoint".to_string(),
            def_path: "midpoint::get_midpoint".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::u64(),
                        name: None,
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::u64(),
                        name: Some("a".into()),
                    },
                    LocalDecl {
                        index: 2,
                        ty: Ty::u64(),
                        name: Some("b".into()),
                    },
                    LocalDecl {
                        index: 3,
                        ty: Ty::u64(),
                        name: None,
                    }, // add result
                    LocalDecl {
                        index: 4,
                        ty: Ty::u64(),
                        name: None,
                    }, // div result
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    TrustBlock {
                        id: BlockId(1),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(4),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Div,
                                    Operand::Copy(Place::local(3)),
                                    Operand::Constant(ConstValue::Uint(2, 64)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(0),
                                rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::u64(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("midpoint should lower");

        assert_eq!(lir.name, "get_midpoint");
        assert_eq!(lir.blocks.len(), 2);
        assert_eq!(lir.signature.params, vec![LirType::I64, LirType::I64]);
        assert_eq!(lir.signature.returns, vec![LirType::I64]);

        // bb0 should have Iadd + Jump
        let bb0 = &lir.blocks[&Block(0)];
        assert!(bb0
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Iadd)));
        assert!(matches!(
            bb0.instructions.last().unwrap().opcode,
            Opcode::Jump { dest: Block(1) }
        ));

        // bb1 should have Iconst(2) + Udiv + Return
        let bb1 = &lir.blocks[&Block(1)];
        assert!(bb1
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Udiv)));
        assert!(matches!(
            bb1.instructions.last().unwrap().opcode,
            Opcode::Return
        ));
    }

    #[test]
    fn test_lower_unary_not() {
        let func = VerifiableFunction {
            name: "not_fn".to_string(),
            def_path: "test::not_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::Bool,
                        name: None,
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Bool,
                        name: Some("x".into()),
                    },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Not, Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("should lower");
        let bb0 = &lir.blocks[&Block(0)];
        assert!(bb0
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Bnot)));
    }

    #[test]
    fn test_lower_nop_statement() {
        // fn nop_fn(a: i32) -> i32 { a } with a Nop before the return assign
        let func = VerifiableFunction {
            name: "nop_fn".to_string(),
            def_path: "test::nop_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::i32(),
                        name: None,
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::i32(),
                        name: Some("a".into()),
                    },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Nop,
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("Nop should not block lowering");
        let bb0 = &lir.blocks[&Block(0)];
        // Nop produces no instructions; only the Return instruction.
        assert!(matches!(
            bb0.instructions.last().unwrap().opcode,
            Opcode::Return
        ));
    }

    #[test]
    fn test_lower_use_copy() {
        // fn copy_fn(a: i32) -> i32 { let x = a; x }
        let func = VerifiableFunction {
            name: "copy_fn".to_string(),
            def_path: "test::copy_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::i32(),
                        name: None,
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::i32(),
                        name: Some("a".into()),
                    },
                    LocalDecl {
                        index: 2,
                        ty: Ty::i32(),
                        name: Some("x".into()),
                    },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("Use copy should lower");
        // Use is a value alias — should produce only the Return instruction.
        let bb0 = &lir.blocks[&Block(0)];
        assert!(matches!(
            bb0.instructions.last().unwrap().opcode,
            Opcode::Return
        ));
    }

    #[test]
    fn test_lower_const_bool_and_uint_variants() {
        // Test Bool and Uint(val, width) constant variants.
        let func = VerifiableFunction {
            name: "const_variety".to_string(),
            def_path: "test::const_variety".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::i32(),
                        name: None,
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Bool,
                        name: None,
                    },
                    LocalDecl {
                        index: 2,
                        ty: Ty::u8(),
                        name: None,
                    },
                    LocalDecl {
                        index: 3,
                        ty: Ty::u16(),
                        name: None,
                    },
                    LocalDecl {
                        index: 4,
                        ty: Ty::u64(),
                        name: None,
                    },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(255, 8))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1000, 16))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(
                                42_000_000_000,
                                64,
                            ))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("constants should lower");
        let bb0 = &lir.blocks[&Block(0)];

        // Should have 4 Iconst instructions + Return.
        let iconst_count = bb0
            .instructions
            .iter()
            .filter(|i| matches!(i.opcode, Opcode::Iconst { .. }))
            .count();
        assert_eq!(iconst_count, 4, "expected 4 Iconst instructions");

        // Check the Bool const emits B1.
        let bool_inst = bb0
            .instructions
            .iter()
            .find(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::B1, imm: 1 }))
            .expect("should have Iconst B1 for true");
        assert_eq!(bool_inst.results.len(), 1);

        // Check the u8 const emits I8.
        assert!(bb0
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::I8, .. })));

        // Check the u16 const emits I16.
        assert!(bb0
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Iconst { ty: LirType::I16, .. })));
    }

    #[test]
    fn test_lower_cast_widening_unsigned() {
        // fn widen(a: u8) -> u32 { a as u32 }
        let func = VerifiableFunction {
            name: "widen".to_string(),
            def_path: "test::widen".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::u32(),
                        name: None,
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::u8(),
                        name: Some("a".into()),
                    },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u32()),
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

        let lir = lower_to_lir(&func).expect("widening cast should lower");
        let bb0 = &lir.blocks[&Block(0)];
        // Should have Uextend instruction (unsigned source).
        assert!(
            bb0.instructions.iter().any(|i| matches!(
                i.opcode,
                Opcode::Uextend {
                    from_ty: LirType::I8,
                    to_ty: LirType::I32
                }
            )),
            "expected Uextend from I8 to I32"
        );
    }

    #[test]
    fn test_lower_cast_widening_signed() {
        // fn widen_signed(a: i8) -> i32 { a as i32 }
        let func = VerifiableFunction {
            name: "widen_signed".to_string(),
            def_path: "test::widen_signed".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::i32(),
                        name: None,
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::i8(),
                        name: Some("a".into()),
                    },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::i32()),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("signed widening cast should lower");
        let bb0 = &lir.blocks[&Block(0)];
        // Should have Sextend instruction (signed source).
        assert!(
            bb0.instructions.iter().any(|i| matches!(
                i.opcode,
                Opcode::Sextend {
                    from_ty: LirType::I8,
                    to_ty: LirType::I32
                }
            )),
            "expected Sextend from I8 to I32"
        );
    }

    #[test]
    fn test_lower_cast_narrowing() {
        // fn narrow(a: i64) -> i16 { a as i16 }
        let func = VerifiableFunction {
            name: "narrow".to_string(),
            def_path: "test::narrow".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::i16(),
                        name: None,
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::i64(),
                        name: Some("a".into()),
                    },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::i16()),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i16(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("narrowing cast should lower");
        let bb0 = &lir.blocks[&Block(0)];
        // Should have Trunc instruction.
        assert!(
            bb0.instructions
                .iter()
                .any(|i| matches!(i.opcode, Opcode::Trunc { to_ty: LirType::I16 })),
            "expected Trunc to I16"
        );
    }

    #[test]
    fn test_lower_cast_same_width() {
        // fn same(a: i32) -> u32 { a as u32 } (same width, no instruction)
        let func = VerifiableFunction {
            name: "same_width".to_string(),
            def_path: "test::same_width".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::u32(),
                        name: None,
                    },
                    LocalDecl {
                        index: 1,
                        ty: Ty::i32(),
                        name: Some("a".into()),
                    },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u32()),
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

        let lir = lower_to_lir(&func).expect("same-width cast should lower");
        let bb0 = &lir.blocks[&Block(0)];
        // Same width produces no Trunc/Sextend/Uextend — just a Return.
        assert!(!bb0.instructions.iter().any(|i| matches!(
            i.opcode,
            Opcode::Trunc { .. } | Opcode::Sextend { .. } | Opcode::Uextend { .. }
        )));
    }

    #[test]
    fn test_lower_call_terminator() {
        // fn caller() -> i32 { callee(10) }
        let func = VerifiableFunction {
            name: "caller".to_string(),
            def_path: "test::caller".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::i32(),
                        name: None,
                    },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "callee".to_string(),
                            args: vec![Operand::Constant(ConstValue::Int(10))],
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    TrustBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 0,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("call should lower");
        let bb0 = &lir.blocks[&Block(0)];

        // Should have: Iconst (for arg 10) + Call + Jump to bb1.
        let call_inst = bb0
            .instructions
            .iter()
            .find(|i| matches!(i.opcode, Opcode::Call { .. }))
            .expect("should have Call instruction");
        match &call_inst.opcode {
            Opcode::Call { name } => assert_eq!(name, "callee"),
            _ => panic!("expected Call opcode"),
        }
        assert_eq!(call_inst.args.len(), 1, "call should have 1 argument");
        assert_eq!(call_inst.results.len(), 1, "call should have 1 result");

        // Should jump to bb1 after call.
        assert!(bb0.instructions.iter().any(|i| matches!(
            i.opcode,
            Opcode::Jump { dest: Block(1) }
        )));
    }

    #[test]
    fn test_lower_call_no_continuation() {
        // Call with no continuation (diverging function).
        let func = VerifiableFunction {
            name: "diverge".to_string(),
            def_path: "test::diverge".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl {
                        index: 0,
                        ty: Ty::i32(),
                        name: None,
                    },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "abort".to_string(),
                        args: vec![],
                        dest: Place::local(0),
                        target: None,
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                }],
                arg_count: 0,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let lir = lower_to_lir(&func).expect("diverging call should lower");
        let bb0 = &lir.blocks[&Block(0)];

        // Should have Call but no Jump (no continuation).
        assert!(bb0
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Call { .. })));
        assert!(!bb0
            .instructions
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Jump { .. })));
    }

    #[test]
    fn test_error_display() {
        let e = BridgeError::UnsupportedType("Ref { .. }".to_string());
        assert_eq!(e.to_string(), "unsupported type: Ref { .. }");

        let e = BridgeError::UnsupportedOp("calls".to_string());
        assert_eq!(e.to_string(), "unsupported operation: calls");

        let e = BridgeError::MissingBlock(5);
        assert_eq!(e.to_string(), "missing block: bb5");

        let e = BridgeError::MissingLocal(3);
        assert_eq!(e.to_string(), "missing local: _3");
    }
}
