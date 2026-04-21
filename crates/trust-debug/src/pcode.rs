// trust-debug/pcode.rs: Simplified P-code IR for binary analysis
//
// Inspired by Ghidra's P-code, but intentionally reduced to the subset we
// need for trust-debug lifting and verification.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use thiserror::Error;
use trust_types::*;

/// Storage spaces used by simplified P-code varnodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum AddressSpace {
    Register,
    Unique,
    Ram,
    Const,
}

/// A storage location in P-code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct VarNode {
    pub address_space: AddressSpace,
    pub offset: u64,
    pub size: u8,
}

impl VarNode {
    /// Width in bits.
    pub(crate) fn bit_width(&self) -> u32 {
        u32::from(self.size) * 8
    }

    /// Returns true when this varnode encodes an immediate constant.
    pub(crate) fn is_constant(&self) -> bool {
        matches!(self.address_space, AddressSpace::Const)
    }
}

/// Simplified P-code opcodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PcodeOp {
    Copy,
    Load,
    Store,
    IntAdd,
    IntSub,
    IntMult,
    IntDiv,
    IntAnd,
    IntOr,
    IntXor,
    IntLeft,
    IntRight,
    IntSright,
    IntEqual,
    IntNotEqual,
    IntLess,
    IntLessEqual,
    IntSless,
    IntSlessEqual,
    IntNegate,
    IntNot,
    IntZext,
    IntSext,
    BoolAnd,
    BoolOr,
    BoolXor,
    BoolNegate,
    Branch,
    CBranch,
    Call,
    CallInd,
    Return,
    Piece,
    Subpiece,
}

/// A single P-code instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PcodeInstruction {
    pub opcode: PcodeOp,
    pub output: Option<VarNode>,
    pub inputs: Vec<VarNode>,
    pub address: u64,
}

/// A basic block of P-code instructions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PcodeBlock {
    pub address: u64,
    pub instructions: Vec<PcodeInstruction>,
    pub fall_through: Option<u64>,
    pub branch_targets: Vec<u64>,
}

/// A P-code function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PcodeFunction {
    pub name: String,
    pub entry_address: u64,
    pub blocks: Vec<PcodeBlock>,
}

#[derive(Debug, Error)]
enum PcodeLoweringError {
    #[error("missing output for {opcode:?} at {address:#x}")]
    MissingOutput { opcode: PcodeOp, address: u64 },
    #[error("missing input {index} for {opcode:?} at {address:#x}")]
    MissingInput { opcode: PcodeOp, address: u64, index: usize },
    #[error("constant varnode cannot be used as an lvalue for {opcode:?} at {address:#x}")]
    ConstantPlace { opcode: PcodeOp, address: u64 },
    #[error("missing local for varnode {varnode:?} at {address:#x}")]
    MissingLocal { varnode: VarNode, address: u64 },
    #[error("unknown block target {target:#x} referenced from {address:#x}")]
    UnknownBlockTarget { address: u64, target: u64 },
}

#[derive(Debug, Clone)]
struct LocalLayout {
    locals: Vec<LocalDecl>,
    local_map: FxHashMap<VarNode, usize>,
    return_ty: Ty,
    arg_count: usize,
}

impl LocalLayout {
    fn from_function(func: &PcodeFunction) -> Self {
        let return_node = find_return_value(func);
        let mut type_hints = FxHashMap::default();
        let mut seen_nodes = Vec::new();
        let mut seen_set = FxHashSet::default();
        let mut written_registers = FxHashSet::default();
        let mut arg_registers = Vec::new();
        let mut arg_set = FxHashSet::default();

        for block in &func.blocks {
            for instruction in &block.instructions {
                record_type_hints(instruction, &mut type_hints);

                for node in read_varnodes(instruction) {
                    if !node.is_constant()
                        && matches!(node.address_space, AddressSpace::Register)
                        && !written_registers.contains(&node)
                        && arg_set.insert(node)
                    {
                        arg_registers.push(node);
                    }
                }

                for node in instruction_varnodes(instruction) {
                    if !node.is_constant() && seen_set.insert(node) {
                        seen_nodes.push(node);
                    }
                }

                for node in written_varnodes(instruction) {
                    if matches!(node.address_space, AddressSpace::Register) {
                        written_registers.insert(node);
                    }
                }
            }
        }

        let return_ty = return_node
            .map_or(Ty::Unit, |node| ty_for_varnode(&node, type_hints.get(&node).cloned()));

        let mut locals = Vec::new();
        let mut local_map = FxHashMap::default();
        let mut next_local = 1;

        locals.push(LocalDecl { index: 0, ty: return_ty.clone(), name: None });

        for node in arg_registers.iter().chain(seen_nodes.iter()) {
            if local_map.contains_key(node) {
                continue;
            }

            local_map.insert(*node, next_local);
            locals.push(LocalDecl {
                index: next_local,
                ty: ty_for_varnode(node, type_hints.get(node).cloned()),
                name: Some(local_name(*node)),
            });
            next_local += 1;
        }

        Self { locals, local_map, return_ty, arg_count: arg_registers.len() }
    }

    fn operand(
        &self,
        node: VarNode,
        address: u64,
        expected_ty: Option<&Ty>,
    ) -> Result<Operand, PcodeLoweringError> {
        if node.is_constant() {
            return Ok(Operand::Constant(const_value(node, expected_ty)));
        }

        let Some(local) = self.local_map.get(&node).copied() else {
            return Err(PcodeLoweringError::MissingLocal { varnode: node, address });
        };

        Ok(Operand::Copy(Place::local(local)))
    }

    fn place(
        &self,
        node: VarNode,
        opcode: PcodeOp,
        address: u64,
    ) -> Result<Place, PcodeLoweringError> {
        if node.is_constant() {
            return Err(PcodeLoweringError::ConstantPlace { opcode, address });
        }

        let Some(local) = self.local_map.get(&node).copied() else {
            return Err(PcodeLoweringError::MissingLocal { varnode: node, address });
        };

        Ok(Place::local(local))
    }
}

/// Lower a simplified P-code function into `trust-types` IR.
///
/// The lowering is intentionally conservative: when the target IR lacks an
/// exact P-code analogue we keep the closest verifier-friendly operation and
/// preserve control flow/block structure.
pub(crate) fn pcode_to_verifiable_body(func: &PcodeFunction) -> VerifiableBody {
    let layout = LocalLayout::from_function(func);
    let block_ids = func
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (block.address, BlockId(index)))
        .collect::<FxHashMap<_, _>>();

    let blocks = func
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| {
            let next_block = func.blocks.get(index + 1).map(|_| BlockId(index + 1));
            lower_block(BlockId(index), block, next_block, &layout, &block_ids)
        })
        .collect();

    VerifiableBody {
        locals: layout.locals,
        blocks,
        arg_count: layout.arg_count,
        return_ty: layout.return_ty,
    }
}

fn lower_block(
    id: BlockId,
    block: &PcodeBlock,
    next_block: Option<BlockId>,
    layout: &LocalLayout,
    block_ids: &FxHashMap<u64, BlockId>,
) -> BasicBlock {
    let mut stmts = Vec::new();
    let mut terminator = None;

    for instruction in &block.instructions {
        if matches!(instruction.opcode, PcodeOp::Return) {
            if let Some(statement) = lower_return_prelude(instruction, layout) {
                stmts.push(statement.unwrap_or(Statement::Nop));
            }
            terminator = Some(Terminator::Return);
            break;
        }

        if is_control_flow(instruction.opcode) {
            let lowered = lower_control_flow(instruction, block, next_block, layout, block_ids)
                .unwrap_or(Terminator::Unreachable);
            terminator = Some(lowered);
            break;
        }

        let statement = lower_statement(instruction, layout).unwrap_or(Statement::Nop);
        stmts.push(statement);
    }

    let terminator = terminator.unwrap_or_else(|| default_terminator(block, next_block, block_ids));

    BasicBlock { id, stmts, terminator }
}

fn lower_statement(
    instruction: &PcodeInstruction,
    layout: &LocalLayout,
) -> Result<Statement, PcodeLoweringError> {
    if is_control_flow(instruction.opcode) {
        return Ok(Statement::Nop);
    }

    let span = synthetic_span(instruction.address);

    match instruction.opcode {
        PcodeOp::Copy => assign_use(
            instruction,
            layout,
            required_output(instruction)?,
            required_input(instruction, 0)?,
        ),
        PcodeOp::Load => assign_use(
            instruction,
            layout,
            required_output(instruction)?,
            load_source_input(instruction)?,
        ),
        PcodeOp::Store => {
            let dest = store_destination_input(instruction)?;
            let value = required_last_input(instruction)?;
            assign_use(instruction, layout, dest, value)
        }
        PcodeOp::IntAdd => assign_binary(instruction, layout, BinOp::Add),
        PcodeOp::IntSub => assign_binary(instruction, layout, BinOp::Sub),
        PcodeOp::IntMult => assign_binary(instruction, layout, BinOp::Mul),
        PcodeOp::IntDiv => assign_binary(instruction, layout, BinOp::Div),
        PcodeOp::IntAnd | PcodeOp::BoolAnd => assign_binary(instruction, layout, BinOp::BitAnd),
        PcodeOp::IntOr | PcodeOp::BoolOr => assign_binary(instruction, layout, BinOp::BitOr),
        PcodeOp::IntXor | PcodeOp::BoolXor => assign_binary(instruction, layout, BinOp::BitXor),
        PcodeOp::IntLeft => assign_binary(instruction, layout, BinOp::Shl),
        PcodeOp::IntRight | PcodeOp::IntSright => assign_binary(instruction, layout, BinOp::Shr),
        PcodeOp::IntEqual => assign_binary(instruction, layout, BinOp::Eq),
        PcodeOp::IntNotEqual => assign_binary(instruction, layout, BinOp::Ne),
        PcodeOp::IntLess | PcodeOp::IntSless => assign_binary(instruction, layout, BinOp::Lt),
        PcodeOp::IntLessEqual | PcodeOp::IntSlessEqual => {
            assign_binary(instruction, layout, BinOp::Le)
        }
        PcodeOp::IntNegate => assign_unary(instruction, layout, UnOp::Neg),
        PcodeOp::IntNot | PcodeOp::BoolNegate => assign_unary(instruction, layout, UnOp::Not),
        PcodeOp::IntZext | PcodeOp::IntSext => assign_cast(instruction, layout),
        PcodeOp::Piece => assign_piece(instruction, layout),
        PcodeOp::Subpiece => assign_subpiece(instruction, layout),
        PcodeOp::Branch | PcodeOp::CBranch | PcodeOp::Call | PcodeOp::CallInd | PcodeOp::Return => {
            unreachable!("control flow instructions are handled before statement lowering")
        }
    }
    .map(|(place, rvalue)| Statement::Assign { place, rvalue, span })
}

fn lower_control_flow(
    instruction: &PcodeInstruction,
    block: &PcodeBlock,
    next_block: Option<BlockId>,
    layout: &LocalLayout,
    block_ids: &FxHashMap<u64, BlockId>,
) -> Result<Terminator, PcodeLoweringError> {
    match instruction.opcode {
        PcodeOp::Branch => {
            let target = branch_target(instruction, block, block_ids)?;
            Ok(Terminator::Goto(target))
        }
        PcodeOp::CBranch => {
            let target = branch_target(instruction, block, block_ids)?;
            let otherwise = fall_through_target(block, next_block, block_ids).unwrap_or(target);
            let cond = layout.operand(
                required_input(instruction, 1)?,
                instruction.address,
                Some(&Ty::Bool),
            )?;

            Ok(Terminator::SwitchInt {
                discr: cond,
                targets: vec![(1_u128, target)],
                otherwise,
                span: synthetic_span(instruction.address),
            })
        }
        PcodeOp::Call | PcodeOp::CallInd => {
            let func_name = call_name(instruction);
            let args = instruction
                .inputs
                .iter()
                .skip(1)
                .map(|node| layout.operand(*node, instruction.address, None))
                .collect::<Result<Vec<_>, _>>()?;
            let dest = instruction.output.map_or(Ok(Place::local(0)), |node| {
                layout.place(node, instruction.opcode, instruction.address)
            })?;

            Ok(Terminator::Call {
                func: func_name,
                args,
                dest,
                target: fall_through_target(block, next_block, block_ids),
                span: synthetic_span(instruction.address),
                atomic: None,
            })
        }
        PcodeOp::Return => Ok(Terminator::Return),
        _ => Ok(default_terminator(block, next_block, block_ids)),
    }
}

fn assign_use(
    instruction: &PcodeInstruction,
    layout: &LocalLayout,
    output: VarNode,
    value: VarNode,
) -> Result<(Place, Rvalue), PcodeLoweringError> {
    let output_ty = ty_for_varnode(&output, None);
    Ok((
        layout.place(output, instruction.opcode, instruction.address)?,
        Rvalue::Use(layout.operand(value, instruction.address, Some(&output_ty))?),
    ))
}

fn lower_return_prelude(
    instruction: &PcodeInstruction,
    layout: &LocalLayout,
) -> Option<Result<Statement, PcodeLoweringError>> {
    let value = instruction.inputs.first().copied()?;
    let span = synthetic_span(instruction.address);
    Some(layout.operand(value, instruction.address, Some(&layout.return_ty)).map(|operand| {
        Statement::Assign { place: Place::local(0), rvalue: Rvalue::Use(operand), span }
    }))
}

fn assign_binary(
    instruction: &PcodeInstruction,
    layout: &LocalLayout,
    op: BinOp,
) -> Result<(Place, Rvalue), PcodeLoweringError> {
    let output = required_output(instruction)?;
    let output_ty = ty_for_varnode(&output, bool_output_type(instruction.opcode));

    Ok((
        layout.place(output, instruction.opcode, instruction.address)?,
        Rvalue::BinaryOp(
            op,
            layout.operand(
                required_input(instruction, 0)?,
                instruction.address,
                Some(&output_ty),
            )?,
            layout.operand(
                required_input(instruction, 1)?,
                instruction.address,
                Some(&output_ty),
            )?,
        ),
    ))
}

fn assign_unary(
    instruction: &PcodeInstruction,
    layout: &LocalLayout,
    op: UnOp,
) -> Result<(Place, Rvalue), PcodeLoweringError> {
    let output = required_output(instruction)?;
    let output_ty = ty_for_varnode(&output, bool_output_type(instruction.opcode));

    Ok((
        layout.place(output, instruction.opcode, instruction.address)?,
        Rvalue::UnaryOp(
            op,
            layout.operand(
                required_input(instruction, 0)?,
                instruction.address,
                Some(&output_ty),
            )?,
        ),
    ))
}

fn assign_cast(
    instruction: &PcodeInstruction,
    layout: &LocalLayout,
) -> Result<(Place, Rvalue), PcodeLoweringError> {
    let output = required_output(instruction)?;
    let cast_ty = match instruction.opcode {
        PcodeOp::IntSext => signed_ty(output.size),
        _ => unsigned_ty(output.size),
    };

    Ok((
        layout.place(output, instruction.opcode, instruction.address)?,
        Rvalue::Cast(
            layout.operand(required_input(instruction, 0)?, instruction.address, None)?,
            cast_ty,
        ),
    ))
}

fn assign_piece(
    instruction: &PcodeInstruction,
    layout: &LocalLayout,
) -> Result<(Place, Rvalue), PcodeLoweringError> {
    let output = required_output(instruction)?;
    let lhs = required_input(instruction, 0)?;
    let rhs = required_input(instruction, 1)?;
    let output_ty = ty_for_varnode(&output, None);

    let rvalue = if lhs.is_constant() && rhs.is_constant() {
        let rhs_bits = rhs.bit_width();
        let combined = (u128::from(lhs.offset) << rhs_bits) | u128::from(rhs.offset);
        Rvalue::Use(Operand::Constant(int_const_from_bits(combined, &output_ty)))
    } else if rhs.is_constant() && rhs.offset == 0 {
        Rvalue::Cast(layout.operand(lhs, instruction.address, None)?, output_ty)
    } else if lhs.is_constant() && lhs.offset == 0 {
        Rvalue::Cast(layout.operand(rhs, instruction.address, None)?, output_ty)
    } else {
        // Conservative fallback when the verifier IR cannot directly encode bit concatenation.
        Rvalue::Cast(layout.operand(lhs, instruction.address, None)?, output_ty)
    };

    Ok((layout.place(output, instruction.opcode, instruction.address)?, rvalue))
}

fn assign_subpiece(
    instruction: &PcodeInstruction,
    layout: &LocalLayout,
) -> Result<(Place, Rvalue), PcodeLoweringError> {
    let output = required_output(instruction)?;
    let source = required_input(instruction, 0)?;
    let output_ty = ty_for_varnode(&output, None);

    let rvalue = if source.is_constant() {
        let byte_offset = required_input(instruction, 1)?.offset;
        let shifted = u128::from(source.offset) >> (byte_offset * 8);
        Rvalue::Use(Operand::Constant(int_const_from_bits(shifted, &output_ty)))
    } else if required_input(instruction, 1)?.offset == 0 {
        Rvalue::Cast(layout.operand(source, instruction.address, None)?, output_ty)
    } else {
        // Conservative fallback: preserve the source value even when we cannot model byte slicing.
        Rvalue::Cast(layout.operand(source, instruction.address, None)?, output_ty)
    };

    Ok((layout.place(output, instruction.opcode, instruction.address)?, rvalue))
}

fn required_output(instruction: &PcodeInstruction) -> Result<VarNode, PcodeLoweringError> {
    instruction.output.ok_or(PcodeLoweringError::MissingOutput {
        opcode: instruction.opcode,
        address: instruction.address,
    })
}

fn required_input(
    instruction: &PcodeInstruction,
    index: usize,
) -> Result<VarNode, PcodeLoweringError> {
    instruction.inputs.get(index).copied().ok_or(PcodeLoweringError::MissingInput {
        opcode: instruction.opcode,
        address: instruction.address,
        index,
    })
}

fn required_last_input(instruction: &PcodeInstruction) -> Result<VarNode, PcodeLoweringError> {
    let Some(last) = instruction.inputs.last().copied() else {
        return Err(PcodeLoweringError::MissingInput {
            opcode: instruction.opcode,
            address: instruction.address,
            index: 0,
        });
    };

    Ok(last)
}

fn load_source_input(instruction: &PcodeInstruction) -> Result<VarNode, PcodeLoweringError> {
    if instruction.inputs.len() >= 2 && instruction.inputs[0].is_constant() {
        return required_input(instruction, 1);
    }

    required_input(instruction, 0)
}

fn store_destination_input(instruction: &PcodeInstruction) -> Result<VarNode, PcodeLoweringError> {
    if instruction.inputs.len() >= 3 && instruction.inputs[0].is_constant() {
        return required_input(instruction, 1);
    }

    required_input(instruction, 0)
}

fn branch_target(
    instruction: &PcodeInstruction,
    block: &PcodeBlock,
    block_ids: &FxHashMap<u64, BlockId>,
) -> Result<BlockId, PcodeLoweringError> {
    let target_address = instruction
        .inputs
        .first()
        .filter(|node| node.is_constant())
        .map(|node| node.offset)
        .or_else(|| block.branch_targets.first().copied())
        .ok_or(PcodeLoweringError::MissingInput {
            opcode: instruction.opcode,
            address: instruction.address,
            index: 0,
        })?;

    resolve_block_target(instruction.address, target_address, block_ids)
}

fn fall_through_target(
    block: &PcodeBlock,
    next_block: Option<BlockId>,
    block_ids: &FxHashMap<u64, BlockId>,
) -> Option<BlockId> {
    block.fall_through.and_then(|address| block_ids.get(&address).copied()).or(next_block)
}

fn resolve_block_target(
    address: u64,
    target: u64,
    block_ids: &FxHashMap<u64, BlockId>,
) -> Result<BlockId, PcodeLoweringError> {
    block_ids
        .get(&target)
        .copied()
        .ok_or(PcodeLoweringError::UnknownBlockTarget { address, target })
}

fn default_terminator(
    block: &PcodeBlock,
    next_block: Option<BlockId>,
    block_ids: &FxHashMap<u64, BlockId>,
) -> Terminator {
    if let Some(target) = fall_through_target(block, next_block, block_ids) {
        return Terminator::Goto(target);
    }

    if let Some(target) =
        block.branch_targets.first().and_then(|address| block_ids.get(address).copied())
    {
        return Terminator::Goto(target);
    }

    Terminator::Return
}

fn call_name(instruction: &PcodeInstruction) -> String {
    match instruction.inputs.first().copied() {
        Some(node) if node.is_constant() => format!("sub_{:#x}", node.offset),
        Some(node) => format!("indirect_{}", local_name(node)),
        None => "pcode_call".to_string(),
    }
}

fn is_control_flow(opcode: PcodeOp) -> bool {
    matches!(
        opcode,
        PcodeOp::Branch | PcodeOp::CBranch | PcodeOp::Call | PcodeOp::CallInd | PcodeOp::Return
    )
}

fn find_return_value(func: &PcodeFunction) -> Option<VarNode> {
    for block in &func.blocks {
        for instruction in &block.instructions {
            if matches!(instruction.opcode, PcodeOp::Return) {
                return instruction.inputs.first().copied();
            }
        }
    }

    None
}

fn instruction_varnodes(instruction: &PcodeInstruction) -> Vec<VarNode> {
    let mut nodes = Vec::new();

    if let Some(output) = instruction.output {
        nodes.push(output);
    }

    nodes.extend(instruction.inputs.iter().copied());
    nodes
}

fn read_varnodes(instruction: &PcodeInstruction) -> Vec<VarNode> {
    match instruction.opcode {
        PcodeOp::Store => instruction.inputs.iter().skip(1).copied().collect(),
        PcodeOp::Branch => vec![],
        PcodeOp::CBranch => instruction.inputs.iter().skip(1).copied().collect(),
        PcodeOp::Call | PcodeOp::CallInd => instruction.inputs.iter().skip(1).copied().collect(),
        _ => instruction.inputs.clone(),
    }
}

fn written_varnodes(instruction: &PcodeInstruction) -> Vec<VarNode> {
    match instruction.opcode {
        PcodeOp::Store => store_destination_input(instruction).ok().into_iter().collect(),
        _ => instruction.output.into_iter().collect(),
    }
}

fn record_type_hints(instruction: &PcodeInstruction, hints: &mut FxHashMap<VarNode, Ty>) {
    match instruction.opcode {
        PcodeOp::IntEqual
        | PcodeOp::IntNotEqual
        | PcodeOp::IntLess
        | PcodeOp::IntLessEqual
        | PcodeOp::IntSless
        | PcodeOp::IntSlessEqual
        | PcodeOp::BoolAnd
        | PcodeOp::BoolOr
        | PcodeOp::BoolXor
        | PcodeOp::BoolNegate => {
            if let Some(output) = instruction.output {
                record_hint(hints, output, Ty::Bool);
            }
        }
        PcodeOp::IntSright | PcodeOp::IntNegate | PcodeOp::IntSext => {
            for node in instruction.inputs.iter().copied().filter(|node| !node.is_constant()) {
                record_hint(hints, node, signed_ty(node.size));
            }

            if let Some(output) = instruction.output {
                record_hint(hints, output, signed_ty(output.size));
            }
        }
        PcodeOp::CBranch => {
            if let Some(cond) = instruction.inputs.get(1).copied() {
                record_hint(hints, cond, Ty::Bool);
            }
        }
        _ => {}
    }
}

fn record_hint(hints: &mut FxHashMap<VarNode, Ty>, node: VarNode, new_ty: Ty) {
    if node.is_constant() {
        return;
    }

    let replace = hints.get(&node).is_none_or(|current| {
        type_priority(&new_ty) > type_priority(current)
            || (type_priority(&new_ty) == type_priority(current)
                && new_ty.int_width().unwrap_or_default() > current.int_width().unwrap_or_default())
    });

    if replace {
        hints.insert(node, new_ty);
    }
}

fn type_priority(ty: &Ty) -> u8 {
    match ty {
        Ty::Bool => 3,
        Ty::Int { signed: true, .. } => 2,
        Ty::Int { .. } => 1,
        _ => 0,
    }
}

fn bool_output_type(opcode: PcodeOp) -> Option<Ty> {
    match opcode {
        PcodeOp::IntEqual
        | PcodeOp::IntNotEqual
        | PcodeOp::IntLess
        | PcodeOp::IntLessEqual
        | PcodeOp::IntSless
        | PcodeOp::IntSlessEqual
        | PcodeOp::BoolAnd
        | PcodeOp::BoolOr
        | PcodeOp::BoolXor
        | PcodeOp::BoolNegate => Some(Ty::Bool),
        _ => None,
    }
}

fn ty_for_varnode(node: &VarNode, hint: Option<Ty>) -> Ty {
    hint.unwrap_or_else(|| unsigned_ty(node.size))
}

fn unsigned_ty(size: u8) -> Ty {
    if size == 0 { Ty::Unit } else { Ty::Int { width: u32::from(size) * 8, signed: false } }
}

fn signed_ty(size: u8) -> Ty {
    if size == 0 { Ty::Unit } else { Ty::Int { width: u32::from(size) * 8, signed: true } }
}

fn const_value(node: VarNode, expected_ty: Option<&Ty>) -> ConstValue {
    match expected_ty {
        Some(Ty::Bool) => ConstValue::Bool(node.offset != 0),
        Some(Ty::Int { width, signed: true }) => ConstValue::Int(sign_extend(node.offset, *width)),
        Some(Ty::Int { width, signed: false }) => ConstValue::Uint(mask_to_width(node.offset, *width), *width),
        _ if node.size == 0 => ConstValue::Unit,
        _ => ConstValue::Uint(mask_to_width(node.offset, node.bit_width()), node.bit_width()),
    }
}

fn int_const_from_bits(bits: u128, ty: &Ty) -> ConstValue {
    match ty {
        Ty::Bool => ConstValue::Bool(bits != 0),
        Ty::Int { width, signed: true } => ConstValue::Int(sign_extend(bits as u64, *width)),
        Ty::Int { width, signed: false } => ConstValue::Uint(mask_bits(bits, *width), *width),
        Ty::Unit => ConstValue::Unit,
        _ => ConstValue::Uint(bits, 64),
    }
}

fn mask_to_width(value: u64, width: u32) -> u128 {
    mask_bits(u128::from(value), width)
}

fn mask_bits(value: u128, width: u32) -> u128 {
    match width {
        0 => 0,
        1..=127 => value & ((1_u128 << width) - 1),
        _ => value,
    }
}

fn sign_extend(value: u64, width: u32) -> i128 {
    if width == 0 {
        return 0;
    }

    if width >= 128 {
        return i128::from(value);
    }

    let shift = 128 - width;
    ((u128::from(value) << shift) as i128) >> shift
}

fn local_name(node: VarNode) -> String {
    let prefix = match node.address_space {
        AddressSpace::Register => "register",
        AddressSpace::Unique => "unique",
        AddressSpace::Ram => "ram",
        AddressSpace::Const => "const",
    };

    format!("{prefix}_{:#x}_{}", node.offset, node.size)
}

fn synthetic_span(address: u64) -> SourceSpan {
    SourceSpan {
        file: format!("pcode:{address:#x}"),
        line_start: 0,
        col_start: 0,
        line_end: 0,
        col_end: 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reg(offset: u64, size: u8) -> VarNode {
        VarNode { address_space: AddressSpace::Register, offset, size }
    }

    fn unique(offset: u64, size: u8) -> VarNode {
        VarNode { address_space: AddressSpace::Unique, offset, size }
    }

    fn ram(offset: u64, size: u8) -> VarNode {
        VarNode { address_space: AddressSpace::Ram, offset, size }
    }

    fn constant(value: u64, size: u8) -> VarNode {
        VarNode { address_space: AddressSpace::Const, offset: value, size }
    }

    fn find_local(body: &VerifiableBody, name: &str) -> Option<usize> {
        body.locals
            .iter()
            .find(|local| local.name.as_deref() == Some(name))
            .map(|local| local.index)
    }

    #[test]
    fn test_pcode_instruction_construction() {
        let dest = reg(0, 8);
        let lhs = reg(1, 8);
        let rhs = reg(2, 8);
        let instruction = PcodeInstruction {
            opcode: PcodeOp::IntAdd,
            output: Some(dest),
            inputs: vec![lhs, rhs],
            address: 0x401000,
        };

        assert_eq!(instruction.opcode, PcodeOp::IntAdd);
        assert_eq!(instruction.output, Some(dest));
        assert_eq!(instruction.inputs, vec![lhs, rhs]);
        assert_eq!(instruction.address, 0x401000);
    }

    #[test]
    fn test_pcode_to_verifiable_body_simple_function() {
        let rax = reg(0, 8);
        let rdi = reg(1, 8);
        let rsi = reg(2, 8);
        let function = PcodeFunction {
            name: "add_then_return".to_string(),
            entry_address: 0x1000,
            blocks: vec![PcodeBlock {
                address: 0x1000,
                instructions: vec![
                    PcodeInstruction {
                        opcode: PcodeOp::Copy,
                        output: Some(rax),
                        inputs: vec![rdi],
                        address: 0x1000,
                    },
                    PcodeInstruction {
                        opcode: PcodeOp::IntAdd,
                        output: Some(rax),
                        inputs: vec![rax, rsi],
                        address: 0x1001,
                    },
                    PcodeInstruction {
                        opcode: PcodeOp::Return,
                        output: None,
                        inputs: vec![rax],
                        address: 0x1002,
                    },
                ],
                fall_through: None,
                branch_targets: vec![],
            }],
        };

        let body = pcode_to_verifiable_body(&function);
        let rax_local = find_local(&body, "register_0x0_8");
        let rdi_local = find_local(&body, "register_0x1_8");
        let rsi_local = find_local(&body, "register_0x2_8");

        assert_eq!(body.arg_count, 2);
        assert_eq!(body.return_ty, Ty::Int { width: 64, signed: false });
        assert_eq!(body.blocks.len(), 1);
        assert_eq!(body.locals[0].ty, Ty::Int { width: 64, signed: false });
        assert_eq!(rax_local, Some(3));
        assert_eq!(rdi_local, Some(1));
        assert_eq!(rsi_local, Some(2));

        let block = &body.blocks[0];
        assert_eq!(block.id, BlockId(0));
        assert_eq!(block.stmts.len(), 3);
        assert!(matches!(block.terminator, Terminator::Return));

        assert!(matches!(
            &block.stmts[0],
            Statement::Assign {
                place,
                rvalue: Rvalue::Use(Operand::Copy(src)),
                ..
            } if *place == Place::local(3) && *src == Place::local(1)
        ));

        assert!(matches!(
            &block.stmts[1],
            Statement::Assign {
                place,
                rvalue: Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Copy(lhs),
                    Operand::Copy(rhs),
                ),
                ..
            } if *place == Place::local(3)
                && *lhs == Place::local(3)
                && *rhs == Place::local(2)
        ));

        assert!(matches!(
            &block.stmts[2],
            Statement::Assign {
                place,
                rvalue: Rvalue::Use(Operand::Copy(src)),
                ..
            } if *place == Place::local(0) && *src == Place::local(3)
        ));
    }

    #[test]
    fn test_varnode_addressing() {
        let register = reg(0x10, 8);
        let scratch = unique(0x20, 4);
        let memory = ram(0x3000, 8);
        let immediate = constant(7, 1);

        assert_eq!(register.address_space, AddressSpace::Register);
        assert_eq!(register.offset, 0x10);
        assert_eq!(register.bit_width(), 64);

        assert_eq!(scratch.address_space, AddressSpace::Unique);
        assert_eq!(scratch.size, 4);

        assert_eq!(memory.address_space, AddressSpace::Ram);
        assert_eq!(memory.offset, 0x3000);

        assert_eq!(immediate.address_space, AddressSpace::Const);
        assert!(immediate.is_constant());
        assert_eq!(immediate.bit_width(), 8);
    }
}
