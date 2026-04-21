// trust-debug/vex_lift.rs: VEX-style binary lifting to P-code IR
//
// Inspired by angr's VEX lifting, but intentionally reduced to the opcode
// patterns trust-debug needs for early binary analysis.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use thiserror::Error;

use crate::binary::{BinarySymbol, SymbolKind};
use crate::pcode::{AddressSpace, PcodeBlock, PcodeFunction, PcodeInstruction, PcodeOp, VarNode};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Architecture {
    X86_64,
    Aarch64,
    X86,
    Arm,
}

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub(crate) enum LiftError {
    #[error("unsupported architecture: {arch:?}")]
    UnsupportedArchitecture { arch: Architecture },
    #[error("unknown opcode {byte:#04x} at {address:#x}")]
    UnknownOpcode { byte: u8, address: u64 },
    #[error(
        "truncated instruction at {address:#x}: expected {expected} bytes, only {available} available"
    )]
    TruncatedInstruction { address: u64, expected: usize, available: usize },
    #[error("invalid instruction at {address:#x}: {bytes:02x?}")]
    InvalidInstruction { address: u64, bytes: Vec<u8> },
}

#[derive(Debug, Clone)]
pub(crate) struct VexLiftConfig {
    pub architecture: Architecture,
    pub base_address: u64,
    pub max_instructions: usize,
    pub follow_jumps: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct VexLiftResult {
    pub function: PcodeFunction,
    pub bytes_consumed: usize,
    pub warnings: Vec<String>,
}

#[derive(Debug, Clone, Copy)]
struct RexPrefix {
    w: bool,
    r: bool,
    x: bool,
    b: bool,
}

#[derive(Debug, Clone)]
struct DecodedInstruction {
    length: usize,
    instructions: Vec<PcodeInstruction>,
    warnings: Vec<String>,
    terminator: Option<BlockTerminator>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BlockTerminator {
    Call { target: u64, fall_through: u64 },
    Branch { target: u64 },
    CBranch { target: u64, fall_through: u64 },
    Return,
}

#[derive(Debug, Clone)]
enum X86Operand {
    Register(VarNode),
    Memory(AddressExpr),
}

#[derive(Debug, Clone)]
struct AddressExpr {
    base: Option<VarNode>,
    index: Option<VarNode>,
    scale: u8,
    displacement: i64,
    rip_relative: bool,
}

pub(crate) fn vex_lift(bytes: &[u8], config: &VexLiftConfig) -> Result<VexLiftResult, LiftError> {
    if config.architecture != Architecture::X86_64 {
        return Err(LiftError::UnsupportedArchitecture { arch: config.architecture });
    }

    let mut blocks = Vec::new();
    let mut warnings = Vec::new();
    let mut bytes_consumed = 0usize;
    let mut lifted_instructions = 0usize;
    let mut current_block = PcodeBlock {
        address: config.base_address,
        instructions: Vec::new(),
        fall_through: None,
        branch_targets: Vec::new(),
    };

    while bytes_consumed < bytes.len() && lifted_instructions < config.max_instructions {
        let address = config.base_address + bytes_consumed as u64;
        let decoded = decode_x86_64_instruction(&bytes[bytes_consumed..], address)?;

        warnings.extend(decoded.warnings);
        current_block.instructions.extend(decoded.instructions);
        bytes_consumed += decoded.length;
        lifted_instructions += 1;

        if let Some(terminator) = decoded.terminator {
            apply_terminator(&mut current_block, terminator);

            if !current_block.instructions.is_empty() {
                blocks.push(current_block);
            }

            let continue_linear_sweep = match terminator {
                BlockTerminator::Call { .. } | BlockTerminator::CBranch { .. } => true,
                BlockTerminator::Branch { .. } => config.follow_jumps,
                BlockTerminator::Return => false,
            };

            if !continue_linear_sweep || bytes_consumed >= bytes.len() {
                current_block = empty_block(config.base_address + bytes_consumed as u64);
                break;
            }

            current_block = empty_block(config.base_address + bytes_consumed as u64);
        }
    }

    if !current_block.instructions.is_empty() {
        blocks.push(current_block);
    }

    Ok(VexLiftResult {
        function: PcodeFunction {
            name: format!("sub_{:#x}", config.base_address),
            entry_address: config.base_address,
            blocks,
        },
        bytes_consumed,
        warnings,
    })
}

pub(crate) fn lift_elf_functions(binary: &[u8], symbols: &[BinarySymbol]) -> Vec<PcodeFunction> {
    let mut functions = Vec::new();

    for symbol in symbols {
        if symbol.kind != SymbolKind::Function {
            continue;
        }

        let Some(end_address) = symbol.address.checked_add(symbol.size) else {
            continue;
        };
        let (Ok(start), Ok(end)) = (usize::try_from(symbol.address), usize::try_from(end_address))
        else {
            continue;
        };

        let Some(function_bytes) = binary.get(start..end) else {
            continue;
        };

        let config = VexLiftConfig {
            architecture: Architecture::X86_64,
            base_address: symbol.address,
            max_instructions: symbol.size as usize,
            follow_jumps: true,
        };

        let Ok(mut lifted) = vex_lift(function_bytes, &config) else {
            continue;
        };
        lifted.function.name = symbol.name.clone();
        functions.push(lifted.function);
    }

    functions
}

pub(crate) fn decode_modrm(byte: u8) -> (u8, u8, u8) {
    ((byte >> 6) & 0b11, (byte >> 3) & 0b111, byte & 0b111)
}

pub(crate) fn x86_64_register_varnode(reg_index: u8) -> VarNode {
    VarNode { address_space: AddressSpace::Register, offset: u64::from(reg_index), size: 8 }
}

fn empty_block(address: u64) -> PcodeBlock {
    PcodeBlock { address, instructions: Vec::new(), fall_through: None, branch_targets: Vec::new() }
}

fn apply_terminator(block: &mut PcodeBlock, terminator: BlockTerminator) {
    match terminator {
        BlockTerminator::Call { target, fall_through } => {
            block.fall_through = Some(fall_through);
            block.branch_targets = vec![target];
        }
        BlockTerminator::Branch { target } => {
            block.fall_through = None;
            block.branch_targets = vec![target];
        }
        BlockTerminator::CBranch { target, fall_through } => {
            block.fall_through = Some(fall_through);
            block.branch_targets = vec![target];
        }
        BlockTerminator::Return => {
            block.fall_through = None;
            block.branch_targets.clear();
        }
    }
}

fn decode_x86_64_instruction(bytes: &[u8], address: u64) -> Result<DecodedInstruction, LiftError> {
    if bytes.is_empty() {
        return Err(LiftError::TruncatedInstruction { address, expected: 1, available: 0 });
    }

    let mut opcode_index = 0usize;
    let mut rex = RexPrefix { w: false, r: false, x: false, b: false };
    if (0x40..=0x4f).contains(&bytes[0]) {
        ensure_available(bytes, 2, address)?;
        rex = parse_rex(bytes[0]);
        opcode_index = 1;
    }

    let opcode = bytes[opcode_index];
    match opcode {
        0x90 => Ok(DecodedInstruction {
            length: opcode_index + 1,
            instructions: Vec::new(),
            warnings: Vec::new(),
            terminator: None,
        }),
        0xC3 => Ok(DecodedInstruction {
            length: opcode_index + 1,
            instructions: vec![PcodeInstruction {
                opcode: PcodeOp::Return,
                output: None,
                inputs: vec![x86_64_register_varnode(0)],
                address,
            }],
            warnings: Vec::new(),
            terminator: Some(BlockTerminator::Return),
        }),
        0xE8 => decode_rel32_control_flow(bytes, address, opcode_index, PcodeOp::Call),
        0xE9 => decode_rel32_control_flow(bytes, address, opcode_index, PcodeOp::Branch),
        0xEB => decode_rel8_branch(bytes, address, opcode_index),
        0x74 | 0x75 => decode_conditional_branch(bytes, address, opcode_index, opcode),
        0x55 => decode_push_rbp(address, opcode_index + 1),
        0x5D => decode_pop_rbp(address, opcode_index + 1),
        0x89 | 0x8B | 0x01 | 0x29 | 0x31 | 0x39 | 0x8D if rex.w => {
            decode_rex_modrm_instruction(bytes, address, opcode_index, rex, opcode)
        }
        _ => Ok(decode_unknown_opcode(opcode, address + opcode_index as u64, opcode_index + 1)),
    }
}

fn decode_rel32_control_flow(
    bytes: &[u8],
    address: u64,
    opcode_index: usize,
    opcode: PcodeOp,
) -> Result<DecodedInstruction, LiftError> {
    let total_len = opcode_index + 5;
    ensure_available(bytes, total_len, address)?;

    let displacement = i32::from_le_bytes([
        bytes[opcode_index + 1],
        bytes[opcode_index + 2],
        bytes[opcode_index + 3],
        bytes[opcode_index + 4],
    ]);
    let target = next_address(address, total_len).wrapping_add_signed(i64::from(displacement));
    let terminator = match opcode {
        PcodeOp::Call => {
            BlockTerminator::Call { target, fall_through: next_address(address, total_len) }
        }
        PcodeOp::Branch => BlockTerminator::Branch { target },
        _ => unreachable!("rel32 helper only supports call/branch"),
    };

    Ok(DecodedInstruction {
        length: total_len,
        instructions: vec![PcodeInstruction {
            opcode,
            output: (opcode == PcodeOp::Call).then(|| x86_64_register_varnode(0)),
            inputs: vec![constant_varnode(target, 8)],
            address,
        }],
        warnings: Vec::new(),
        terminator: Some(terminator),
    })
}

fn decode_rel8_branch(
    bytes: &[u8],
    address: u64,
    opcode_index: usize,
) -> Result<DecodedInstruction, LiftError> {
    let total_len = opcode_index + 2;
    ensure_available(bytes, total_len, address)?;

    let displacement = bytes[opcode_index + 1] as i8;
    let target = next_address(address, total_len).wrapping_add_signed(i64::from(displacement));

    Ok(DecodedInstruction {
        length: total_len,
        instructions: vec![PcodeInstruction {
            opcode: PcodeOp::Branch,
            output: None,
            inputs: vec![constant_varnode(target, 8)],
            address,
        }],
        warnings: Vec::new(),
        terminator: Some(BlockTerminator::Branch { target }),
    })
}

fn decode_conditional_branch(
    bytes: &[u8],
    address: u64,
    opcode_index: usize,
    opcode: u8,
) -> Result<DecodedInstruction, LiftError> {
    let total_len = opcode_index + 2;
    ensure_available(bytes, total_len, address)?;

    let displacement = bytes[opcode_index + 1] as i8;
    let target = next_address(address, total_len).wrapping_add_signed(i64::from(displacement));
    let flags = x86_64_register_varnode(16);
    let condition = unique_varnode(address, 0x30, 1);
    let compare_opcode = if opcode == 0x74 { PcodeOp::IntEqual } else { PcodeOp::IntNotEqual };

    Ok(DecodedInstruction {
        length: total_len,
        instructions: vec![
            PcodeInstruction {
                opcode: compare_opcode,
                output: Some(condition),
                inputs: vec![flags, constant_varnode(0, flags.size)],
                address,
            },
            PcodeInstruction {
                opcode: PcodeOp::CBranch,
                output: None,
                inputs: vec![constant_varnode(target, 8), condition],
                address,
            },
        ],
        warnings: Vec::new(),
        terminator: Some(BlockTerminator::CBranch {
            target,
            fall_through: next_address(address, total_len),
        }),
    })
}

fn decode_push_rbp(address: u64, length: usize) -> Result<DecodedInstruction, LiftError> {
    ensure_nonzero_length(length, address)?;
    let rsp = x86_64_register_varnode(4);
    let rbp = x86_64_register_varnode(5);

    Ok(DecodedInstruction {
        length,
        instructions: vec![
            PcodeInstruction {
                opcode: PcodeOp::IntSub,
                output: Some(rsp),
                inputs: vec![rsp, constant_varnode(8, 8)],
                address,
            },
            PcodeInstruction {
                opcode: PcodeOp::Store,
                output: None,
                inputs: vec![rsp, rbp],
                address,
            },
        ],
        warnings: Vec::new(),
        terminator: None,
    })
}

fn decode_pop_rbp(address: u64, length: usize) -> Result<DecodedInstruction, LiftError> {
    ensure_nonzero_length(length, address)?;
    let rsp = x86_64_register_varnode(4);
    let rbp = x86_64_register_varnode(5);

    Ok(DecodedInstruction {
        length,
        instructions: vec![
            PcodeInstruction {
                opcode: PcodeOp::Load,
                output: Some(rbp),
                inputs: vec![rsp],
                address,
            },
            PcodeInstruction {
                opcode: PcodeOp::IntAdd,
                output: Some(rsp),
                inputs: vec![rsp, constant_varnode(8, 8)],
                address,
            },
        ],
        warnings: Vec::new(),
        terminator: None,
    })
}

fn decode_rex_modrm_instruction(
    bytes: &[u8],
    address: u64,
    opcode_index: usize,
    rex: RexPrefix,
    opcode: u8,
) -> Result<DecodedInstruction, LiftError> {
    let (reg, rm, total_len) = decode_modrm_operands(bytes, address, opcode_index, rex)?;
    let instructions = match opcode {
        0x89 => lift_mov_rm_r(address, total_len, reg, rm)?,
        0x8B => lift_mov_r_rm(address, total_len, reg, rm)?,
        0x01 => lift_binary_rm_r(address, total_len, PcodeOp::IntAdd, reg, rm)?,
        0x29 => lift_binary_rm_r(address, total_len, PcodeOp::IntSub, reg, rm)?,
        0x31 => lift_binary_rm_r(address, total_len, PcodeOp::IntXor, reg, rm)?,
        0x39 => lift_cmp_rm_r(address, total_len, reg, rm)?,
        0x8D => lift_lea(address, total_len, reg, rm, &bytes[..total_len])?,
        _ => unreachable!("unsupported rex/modrm opcode"),
    };

    Ok(DecodedInstruction {
        length: total_len,
        instructions,
        warnings: Vec::new(),
        terminator: None,
    })
}

fn lift_mov_rm_r(
    address: u64,
    length: usize,
    source: VarNode,
    dest: X86Operand,
) -> Result<Vec<PcodeInstruction>, LiftError> {
    match dest {
        X86Operand::Register(dest) => Ok(vec![copy_instruction(address, dest, source)]),
        X86Operand::Memory(expr) => {
            let (addr, mut instructions) = materialize_address(address, length, expr, 0x10);
            instructions.push(PcodeInstruction {
                opcode: PcodeOp::Store,
                output: None,
                inputs: vec![addr, source],
                address,
            });
            Ok(instructions)
        }
    }
}

fn lift_mov_r_rm(
    address: u64,
    length: usize,
    dest: VarNode,
    source: X86Operand,
) -> Result<Vec<PcodeInstruction>, LiftError> {
    match source {
        X86Operand::Register(source) => Ok(vec![copy_instruction(address, dest, source)]),
        X86Operand::Memory(expr) => {
            let (addr, mut instructions) = materialize_address(address, length, expr, 0x10);
            instructions.push(PcodeInstruction {
                opcode: PcodeOp::Load,
                output: Some(dest),
                inputs: vec![addr],
                address,
            });
            Ok(instructions)
        }
    }
}

fn lift_binary_rm_r(
    address: u64,
    length: usize,
    opcode: PcodeOp,
    source: VarNode,
    dest: X86Operand,
) -> Result<Vec<PcodeInstruction>, LiftError> {
    match dest {
        X86Operand::Register(dest) => Ok(vec![PcodeInstruction {
            opcode,
            output: Some(dest),
            inputs: vec![dest, source],
            address,
        }]),
        X86Operand::Memory(expr) => {
            let (addr, mut instructions) = materialize_address(address, length, expr, 0x10);
            let scratch = unique_varnode(address, 0x20, 8);
            instructions.push(PcodeInstruction {
                opcode: PcodeOp::Load,
                output: Some(scratch),
                inputs: vec![addr],
                address,
            });
            instructions.push(PcodeInstruction {
                opcode,
                output: Some(scratch),
                inputs: vec![scratch, source],
                address,
            });
            instructions.push(PcodeInstruction {
                opcode: PcodeOp::Store,
                output: None,
                inputs: vec![addr, scratch],
                address,
            });
            Ok(instructions)
        }
    }
}

fn lift_cmp_rm_r(
    address: u64,
    length: usize,
    source: VarNode,
    lhs: X86Operand,
) -> Result<Vec<PcodeInstruction>, LiftError> {
    let flags = x86_64_register_varnode(16);

    match lhs {
        X86Operand::Register(lhs) => Ok(vec![PcodeInstruction {
            opcode: PcodeOp::IntSub,
            output: Some(flags),
            inputs: vec![lhs, source],
            address,
        }]),
        X86Operand::Memory(expr) => {
            let (addr, mut instructions) = materialize_address(address, length, expr, 0x10);
            let scratch = unique_varnode(address, 0x20, 8);
            instructions.push(PcodeInstruction {
                opcode: PcodeOp::Load,
                output: Some(scratch),
                inputs: vec![addr],
                address,
            });
            instructions.push(PcodeInstruction {
                opcode: PcodeOp::IntSub,
                output: Some(flags),
                inputs: vec![scratch, source],
                address,
            });
            Ok(instructions)
        }
    }
}

fn lift_lea(
    address: u64,
    length: usize,
    dest: VarNode,
    source: X86Operand,
    raw_bytes: &[u8],
) -> Result<Vec<PcodeInstruction>, LiftError> {
    let X86Operand::Memory(expr) = source else {
        return Err(LiftError::InvalidInstruction { address, bytes: raw_bytes.to_vec() });
    };

    let instructions = lea_address_instructions(address, length, dest, expr);
    Ok(instructions)
}

fn decode_modrm_operands(
    bytes: &[u8],
    address: u64,
    opcode_index: usize,
    rex: RexPrefix,
) -> Result<(VarNode, X86Operand, usize), LiftError> {
    ensure_available(bytes, opcode_index + 2, address)?;

    let modrm_byte = bytes[opcode_index + 1];
    let (mode, reg_bits, rm_bits) = decode_modrm(modrm_byte);
    let reg = x86_64_register_varnode(reg_bits | if rex.r { 8 } else { 0 });
    let (rm, rm_len) = decode_rm_operand(bytes, address, opcode_index + 2, mode, rm_bits, rex)?;

    Ok((reg, rm, opcode_index + 2 + rm_len))
}

fn decode_rm_operand(
    bytes: &[u8],
    address: u64,
    offset: usize,
    mode: u8,
    rm_bits: u8,
    rex: RexPrefix,
) -> Result<(X86Operand, usize), LiftError> {
    if mode == 0b11 {
        return Ok((
            X86Operand::Register(x86_64_register_varnode(rm_bits | if rex.b { 8 } else { 0 })),
            0,
        ));
    }

    let mut consumed = 0usize;
    let mut base = None;
    let mut index = None;
    let mut scale = 1u8;
    let mut displacement = 0i64;
    let mut rip_relative = false;

    if rm_bits == 0b100 {
        ensure_available(bytes, offset + 1, address)?;
        let sib = bytes[offset];
        consumed += 1;

        scale = 1u8 << ((sib >> 6) & 0b11);
        let index_bits = (sib >> 3) & 0b111;
        let base_bits = sib & 0b111;

        if index_bits != 0b100 {
            index = Some(x86_64_register_varnode(index_bits | if rex.x { 8 } else { 0 }));
        }

        if mode == 0b00 && base_bits == 0b101 {
            displacement = read_i32(bytes, address, offset + consumed, offset + consumed + 4)?;
            consumed += 4;
        } else {
            base = Some(x86_64_register_varnode(base_bits | if rex.b { 8 } else { 0 }));
        }
    } else if mode == 0b00 && rm_bits == 0b101 {
        rip_relative = true;
        displacement = read_i32(bytes, address, offset, offset + 4)?;
        consumed += 4;
    } else {
        base = Some(x86_64_register_varnode(rm_bits | if rex.b { 8 } else { 0 }));
    }

    match mode {
        0b00 => {}
        0b01 => {
            ensure_available(bytes, offset + consumed + 1, address)?;
            displacement += i64::from(bytes[offset + consumed] as i8);
            consumed += 1;
        }
        0b10 => {
            displacement += read_i32(bytes, address, offset + consumed, offset + consumed + 4)?;
            consumed += 4;
        }
        _ => unreachable!("register direct handled earlier"),
    }

    Ok((
        X86Operand::Memory(AddressExpr { base, index, scale, displacement, rip_relative }),
        consumed,
    ))
}

fn materialize_address(
    address: u64,
    length: usize,
    expr: AddressExpr,
    slot_base: u8,
) -> (VarNode, Vec<PcodeInstruction>) {
    if let (Some(base), None, 1, 0, false) =
        (expr.base, expr.index, expr.scale, expr.displacement, expr.rip_relative)
    {
        return (base, Vec::new());
    }

    let temp = unique_varnode(address, slot_base, 8);
    (temp, lea_address_instructions(address, length, temp, expr))
}

fn lea_address_instructions(
    address: u64,
    length: usize,
    dest: VarNode,
    expr: AddressExpr,
) -> Vec<PcodeInstruction> {
    let mut instructions = Vec::new();
    let next = next_address(address, length);
    let displacement = constant_varnode(expr.displacement as u64, 8);

    let base_operand = if expr.rip_relative {
        constant_varnode(next, 8)
    } else {
        expr.base.unwrap_or_else(|| constant_varnode(0, 8))
    };

    let rhs = match expr.index {
        Some(index) if expr.scale == 1 => index,
        Some(index) => {
            let scaled = unique_varnode(address, 0x41, 8);
            instructions.push(PcodeInstruction {
                opcode: PcodeOp::IntMult,
                output: Some(scaled),
                inputs: vec![index, constant_varnode(u64::from(expr.scale), 8)],
                address,
            });
            scaled
        }
        None if expr.displacement != 0 || expr.base.is_none() || expr.rip_relative => displacement,
        None => constant_varnode(0, 8),
    };

    instructions.push(PcodeInstruction {
        opcode: PcodeOp::IntAdd,
        output: Some(dest),
        inputs: vec![base_operand, rhs],
        address,
    });

    if expr.displacement != 0 && expr.index.is_some() {
        instructions.push(PcodeInstruction {
            opcode: PcodeOp::IntAdd,
            output: Some(dest),
            inputs: vec![dest, displacement],
            address,
        });
    }

    instructions
}

fn copy_instruction(address: u64, output: VarNode, input: VarNode) -> PcodeInstruction {
    PcodeInstruction { opcode: PcodeOp::Copy, output: Some(output), inputs: vec![input], address }
}

fn decode_unknown_opcode(byte: u8, address: u64, length: usize) -> DecodedInstruction {
    let scratch = unique_varnode(address, 0xff, 1);
    DecodedInstruction {
        length,
        instructions: vec![PcodeInstruction {
            opcode: PcodeOp::Copy,
            output: Some(scratch),
            inputs: vec![constant_varnode(u64::from(byte), 1)],
            address,
        }],
        warnings: vec![format!(
            "unknown opcode {byte:#04x} at {address:#x}; emitted placeholder Copy"
        )],
        terminator: None,
    }
}

fn parse_rex(prefix: u8) -> RexPrefix {
    RexPrefix {
        w: prefix & 0b1000 != 0,
        r: prefix & 0b0100 != 0,
        x: prefix & 0b0010 != 0,
        b: prefix & 0b0001 != 0,
    }
}

fn ensure_available(bytes: &[u8], expected: usize, address: u64) -> Result<(), LiftError> {
    if bytes.len() < expected {
        return Err(LiftError::TruncatedInstruction { address, expected, available: bytes.len() });
    }

    Ok(())
}

fn ensure_nonzero_length(length: usize, address: u64) -> Result<(), LiftError> {
    if length == 0 {
        return Err(LiftError::InvalidInstruction { address, bytes: Vec::new() });
    }

    Ok(())
}

fn read_i32(bytes: &[u8], address: u64, start: usize, expected: usize) -> Result<i64, LiftError> {
    ensure_available(bytes, expected, address)?;
    Ok(i64::from(i32::from_le_bytes([
        bytes[start],
        bytes[start + 1],
        bytes[start + 2],
        bytes[start + 3],
    ])))
}

fn next_address(address: u64, length: usize) -> u64 {
    address.wrapping_add(length as u64)
}

fn unique_varnode(address: u64, slot: u8, size: u8) -> VarNode {
    VarNode { address_space: AddressSpace::Unique, offset: (address << 8) | u64::from(slot), size }
}

fn constant_varnode(value: u64, size: u8) -> VarNode {
    VarNode { address_space: AddressSpace::Const, offset: value, size }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn config(architecture: Architecture, base_address: u64) -> VexLiftConfig {
        VexLiftConfig { architecture, base_address, max_instructions: 128, follow_jumps: true }
    }

    fn opcodes(result: &VexLiftResult) -> Vec<PcodeOp> {
        result
            .function
            .blocks
            .iter()
            .flat_map(|block| block.instructions.iter().map(|instruction| instruction.opcode))
            .collect()
    }

    #[test]
    fn test_lift_ret() {
        let result = vex_lift(&[0xC3], &config(Architecture::X86_64, 0x1000)).unwrap();
        assert_eq!(opcodes(&result), vec![PcodeOp::Return]);
    }

    #[test]
    fn test_lift_nop() {
        let result = vex_lift(&[0x90], &config(Architecture::X86_64, 0x1000)).unwrap();
        assert!(opcodes(&result).is_empty());
        assert_eq!(result.bytes_consumed, 1);
    }

    #[test]
    fn test_lift_call_rel32() {
        let result =
            vex_lift(&[0xE8, 0x05, 0x00, 0x00, 0x00], &config(Architecture::X86_64, 0x1000))
                .unwrap();

        let call = &result.function.blocks[0].instructions[0];
        assert_eq!(call.opcode, PcodeOp::Call);
        assert_eq!(call.inputs[0], constant_varnode(0x100A, 8));
    }

    #[test]
    fn test_lift_push_pop() {
        let result = vex_lift(&[0x55, 0x5D, 0xC3], &config(Architecture::X86_64, 0x1000)).unwrap();
        assert_eq!(
            opcodes(&result),
            vec![PcodeOp::IntSub, PcodeOp::Store, PcodeOp::Load, PcodeOp::IntAdd, PcodeOp::Return]
        );
    }

    #[test]
    fn test_lift_mov_add() {
        let result = vex_lift(
            &[0x48, 0x89, 0xE5, 0x48, 0x01, 0xD0, 0xC3],
            &config(Architecture::X86_64, 0x1000),
        )
        .unwrap();

        assert_eq!(opcodes(&result), vec![PcodeOp::Copy, PcodeOp::IntAdd, PcodeOp::Return]);
    }

    #[test]
    fn test_unsupported_arch() {
        let error = vex_lift(&[0xC3], &config(Architecture::Aarch64, 0x1000)).unwrap_err();
        assert_eq!(error, LiftError::UnsupportedArchitecture { arch: Architecture::Aarch64 });
    }

    #[test]
    fn test_empty_input() {
        let result = vex_lift(&[], &config(Architecture::X86_64, 0x1000)).unwrap();
        assert!(result.function.blocks.is_empty());
        assert_eq!(result.bytes_consumed, 0);
    }
}
