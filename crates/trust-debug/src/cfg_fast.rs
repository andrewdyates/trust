// trust-debug/cfg_fast.rs: Fast CFG recovery for stripped binaries
//
// Implements a lightweight CFGFast-style pass for x86_64 binaries. The pass
// starts from known function symbols, supplements them with prologue and
// alignment heuristics, then recursively descends through direct control flow
// to recover functions and basic blocks.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use trust_types::fx::{FxHashMap, FxHashSet};

use crate::binary::SymbolKind;
use crate::pcode::{AddressSpace, PcodeBlock, PcodeFunction, PcodeInstruction, PcodeOp, VarNode};

/// Configuration for CFGFast recovery.
#[derive(Debug, Clone)]
pub(crate) struct CfgFastConfig {
    pub max_iterations: usize,
    pub heuristic_function_starts: bool,
    pub follow_calls: bool,
}

impl Default for CfgFastConfig {
    fn default() -> Self {
        Self { max_iterations: 10_000, heuristic_function_starts: true, follow_calls: true }
    }
}

/// A recovered function and its discovered basic blocks.
#[derive(Debug, Clone)]
pub(crate) struct RecoveredFunction {
    pub entry_address: u64,
    pub name: Option<String>,
    pub size: u64,
    pub blocks: Vec<RecoveredBlock>,
    pub is_complete: bool,
}

/// A recovered machine-code basic block.
#[derive(Debug, Clone)]
pub(crate) struct RecoveredBlock {
    pub address: u64,
    pub size: u64,
    pub instructions: Vec<RawInstruction>,
    pub successors: Vec<u64>,
    pub is_call: bool,
    pub call_target: Option<u64>,
}

/// A decoded raw machine instruction.
#[derive(Debug, Clone)]
pub(crate) struct RawInstruction {
    pub address: u64,
    pub size: u8,
    pub mnemonic: String,
    pub operands: Vec<InstructionOperand>,
}

/// Operand shape for recovered instructions.
#[derive(Debug, Clone)]
pub(crate) enum InstructionOperand {
    Register(String),
    Immediate(i64),
    Memory { base: Option<String>, index: Option<String>, scale: u8, displacement: i64 },
    Label(u64),
}

/// Full recovery result across all discovered functions.
#[derive(Debug, Clone)]
pub(crate) struct CfgFastResult {
    pub functions: Vec<RecoveredFunction>,
    pub unresolved_jumps: Vec<u64>,
    pub coverage: f64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ControlFlowKind {
    None,
    Call { target: Option<u64> },
    Jump { target: Option<u64>, conditional: bool },
    Return,
    Trap,
    Unknown,
}

#[derive(Debug, Clone)]
struct DecodedInstruction {
    instruction: RawInstruction,
    control_flow: ControlFlowKind,
}

#[derive(Debug, Clone, Copy, Default)]
struct RexPrefix {
    r: bool,
    x: bool,
    b: bool,
}

#[derive(Debug, Clone, Copy)]
struct ModRm {
    mode: u8,
    reg: u8,
    rm: u8,
    reg_raw: u8,
    rm_raw: u8,
}

#[derive(Debug, Clone, Copy)]
struct Sib {
    scale: u8,
    index: u8,
    base: u8,
    index_raw: u8,
    base_raw: u8,
}

#[derive(Debug, Clone)]
struct RecoveredBlockState {
    block: Option<RecoveredBlock>,
    discovered_functions: BTreeSet<u64>,
    unresolved_jumps: BTreeSet<u64>,
    covered_offsets: BTreeSet<usize>,
    is_complete: bool,
}

#[derive(Debug, Clone)]
struct FunctionRecovery {
    function: Option<RecoveredFunction>,
    discovered_functions: BTreeSet<u64>,
    unresolved_jumps: BTreeSet<u64>,
    covered_offsets: BTreeSet<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SliceStateKey {
    block_index: usize,
    before_index: usize,
    needed: Vec<String>,
}

/// Recover functions and a control-flow graph from a raw binary slice.
pub(crate) fn cfg_fast_recover(
    binary: &[u8],
    symbols: &[crate::binary::BinarySymbol],
    config: &CfgFastConfig,
) -> CfgFastResult {
    if binary.is_empty() {
        return CfgFastResult { functions: vec![], unresolved_jumps: vec![], coverage: 0.0 };
    }

    let base_address = infer_base_address(symbols);
    let symbol_names = symbols
        .iter()
        .filter(|symbol| symbol.kind == SymbolKind::Function)
        .map(|symbol| (symbol.address, symbol.name.clone()))
        .collect::<FxHashMap<_, _>>();

    let mut entries = BTreeSet::new();
    entries.extend(
        symbols
            .iter()
            .filter(|symbol| symbol.kind == SymbolKind::Function)
            .map(|symbol| symbol.address),
    );
    entries.extend(discover_function_prologues(binary, base_address));
    if config.heuristic_function_starts {
        entries.extend(discover_heuristic_function_starts(binary, base_address));
    }

    let mut pending = VecDeque::new();
    pending.extend(entries.iter().copied());

    let mut recovered = BTreeMap::new();
    let mut covered_offsets = BTreeSet::new();
    let mut unresolved_jumps = BTreeSet::new();

    while let Some(entry) = pending.pop_front() {
        if recovered.contains_key(&entry) || !address_in_range(entry, base_address, binary.len()) {
            continue;
        }

        let recovery =
            recover_function(entry, binary, base_address, &entries, &symbol_names, config);

        if let Some(function) = recovery.function {
            recovered.insert(entry, function);
        }

        covered_offsets.extend(recovery.covered_offsets);
        unresolved_jumps.extend(recovery.unresolved_jumps);

        for target in recovery.discovered_functions {
            if !config.follow_calls || !address_in_range(target, base_address, binary.len()) {
                continue;
            }
            if entries.insert(target)
                || (!recovered.contains_key(&target) && !pending.contains(&target))
            {
                pending.push_back(target);
            }
        }
    }

    let functions = recovered.into_values().collect::<Vec<_>>();
    let coverage = covered_offsets.len() as f64 / binary.len() as f64;

    CfgFastResult { functions, unresolved_jumps: unresolved_jumps.into_iter().collect(), coverage }
}

/// Convert a recovered function into simplified P-code IR.
pub(crate) fn recovered_to_pcode(func: &RecoveredFunction) -> crate::pcode::PcodeFunction {
    let name = func.name.clone().unwrap_or_else(|| format!("sub_{:#x}", func.entry_address));
    let blocks = func.blocks.iter().map(recovered_block_to_pcode).collect();

    PcodeFunction { name, entry_address: func.entry_address, blocks }
}

/// Compute a conservative backward slice rooted at the given sink instruction.
pub(crate) fn backward_slice(functions: &[RecoveredFunction], sink_address: u64) -> Vec<u64> {
    let Some((function, block_index, instruction_index)) = locate_sink(functions, sink_address)
    else {
        return vec![];
    };

    let sink_instruction = &function.blocks[block_index].instructions[instruction_index];
    let mut needed = uses_of_instruction(sink_instruction);
    if needed.is_empty() {
        return vec![];
    }

    let block_map = function
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (block.address, index))
        .collect::<FxHashMap<_, _>>();
    let mut predecessors = vec![Vec::new(); function.blocks.len()];

    for (index, block) in function.blocks.iter().enumerate() {
        for successor in &block.successors {
            if let Some(target_index) = block_map.get(successor).copied() {
                predecessors[target_index].push(index);
            }
        }
    }

    let mut result = BTreeSet::new();
    let mut seen = FxHashSet::default();
    let mut queue = VecDeque::new();
    let initial_key = SliceStateKey {
        block_index,
        before_index: instruction_index,
        needed: needed.iter().cloned().collect(),
    };
    seen.insert(initial_key);
    queue.push_back((block_index, instruction_index, std::mem::take(&mut needed)));

    while let Some((current_block, before_index, mut needed_values)) = queue.pop_front() {
        let block = &function.blocks[current_block];
        let stop = before_index.min(block.instructions.len());

        for instruction in block.instructions[..stop].iter().rev() {
            let defs = defs_of_instruction(instruction);
            if intersects(&defs, &needed_values) {
                result.insert(instruction.address);
                for defined in defs {
                    needed_values.remove(&defined);
                }
                needed_values.extend(uses_of_instruction(instruction));
            }
        }

        if needed_values.is_empty() {
            continue;
        }

        for predecessor in &predecessors[current_block] {
            let key = SliceStateKey {
                block_index: *predecessor,
                before_index: function.blocks[*predecessor].instructions.len(),
                needed: needed_values.iter().cloned().collect(),
            };
            if seen.insert(key) {
                queue.push_back((
                    *predecessor,
                    function.blocks[*predecessor].instructions.len(),
                    needed_values.clone(),
                ));
            }
        }
    }

    result.into_iter().collect()
}

fn recover_function(
    entry: u64,
    binary: &[u8],
    base_address: u64,
    known_entries: &BTreeSet<u64>,
    symbol_names: &FxHashMap<u64, String>,
    config: &CfgFastConfig,
) -> FunctionRecovery {
    let mut budget = config.max_iterations;
    let mut block_queue = VecDeque::new();
    block_queue.push_back(entry);

    let mut seen_blocks = BTreeSet::new();
    let mut blocks = Vec::new();
    let mut discovered_functions = BTreeSet::new();
    let mut unresolved_jumps = BTreeSet::new();
    let mut covered_offsets = BTreeSet::new();
    let mut is_complete = true;

    while let Some(block_address) = block_queue.pop_front() {
        if !seen_blocks.insert(block_address) {
            continue;
        }

        let recovered =
            decode_block(block_address, binary, base_address, known_entries, &mut budget);
        is_complete &= recovered.is_complete;
        discovered_functions.extend(recovered.discovered_functions);
        unresolved_jumps.extend(recovered.unresolved_jumps);
        covered_offsets.extend(recovered.covered_offsets);

        let Some(block) = recovered.block else {
            continue;
        };

        if let Some(target) = block.call_target {
            discovered_functions.insert(target);
        }

        for successor in &block.successors {
            if address_in_range(*successor, base_address, binary.len())
                && !seen_blocks.contains(successor)
            {
                block_queue.push_back(*successor);
            }
        }

        blocks.push(block);

        if budget == 0 {
            is_complete = false;
            break;
        }
    }

    blocks.sort_by_key(|block| block.address);
    let size = blocks.iter().map(|block| block.size).sum();

    FunctionRecovery {
        function: (!blocks.is_empty()).then(|| RecoveredFunction {
            entry_address: entry,
            name: symbol_names.get(&entry).cloned(),
            size,
            blocks,
            is_complete,
        }),
        discovered_functions,
        unresolved_jumps,
        covered_offsets,
    }
}

fn decode_block(
    start_address: u64,
    binary: &[u8],
    base_address: u64,
    known_entries: &BTreeSet<u64>,
    budget: &mut usize,
) -> RecoveredBlockState {
    if !address_in_range(start_address, base_address, binary.len()) {
        return RecoveredBlockState {
            block: None,
            discovered_functions: BTreeSet::new(),
            unresolved_jumps: BTreeSet::new(),
            covered_offsets: BTreeSet::new(),
            is_complete: false,
        };
    }

    let mut current_address = start_address;
    let mut instructions = Vec::new();
    let mut successors = Vec::new();
    let mut discovered_functions = BTreeSet::new();
    let mut unresolved_jumps = BTreeSet::new();
    let mut covered_offsets = BTreeSet::new();
    let mut is_complete = true;
    let mut is_call = false;
    let mut call_target = None;

    loop {
        if *budget == 0 {
            is_complete = false;
            break;
        }

        if current_address != start_address && known_entries.contains(&current_address) {
            break;
        }

        let Some(decoded) = decode_instruction(binary, base_address, current_address) else {
            is_complete = false;
            break;
        };

        *budget = budget.saturating_sub(1);

        let offset = address_to_offset(current_address, base_address, binary.len())
            .expect("current address is always in range while decoding a block");
        let end = offset.saturating_add(decoded.instruction.size as usize).min(binary.len());
        covered_offsets.extend(offset..end);

        let next_address = current_address + u64::from(decoded.instruction.size);
        instructions.push(decoded.instruction.clone());

        match decoded.control_flow {
            ControlFlowKind::None => {
                current_address = next_address;
            }
            ControlFlowKind::Call { target } => {
                is_call = true;
                call_target = target;
                if let Some(target) = target {
                    discovered_functions.insert(target);
                } else {
                    unresolved_jumps.insert(current_address);
                }
                if address_in_range(next_address, base_address, binary.len()) {
                    successors.push(next_address);
                }
                break;
            }
            ControlFlowKind::Jump { target, conditional } => {
                if let Some(target) = target {
                    if address_in_range(target, base_address, binary.len()) {
                        successors.push(target);
                    } else {
                        unresolved_jumps.insert(current_address);
                    }
                } else {
                    unresolved_jumps.insert(current_address);
                }

                if conditional && address_in_range(next_address, base_address, binary.len()) {
                    successors.push(next_address);
                }
                break;
            }
            ControlFlowKind::Return | ControlFlowKind::Trap => break,
            ControlFlowKind::Unknown => {
                is_complete = false;
                break;
            }
        }
    }

    sort_and_dedup(&mut successors);

    let block = (!instructions.is_empty()).then(|| RecoveredBlock {
        address: start_address,
        size: instructions.iter().map(|instruction| u64::from(instruction.size)).sum(),
        instructions,
        successors,
        is_call,
        call_target,
    });

    RecoveredBlockState {
        block,
        discovered_functions,
        unresolved_jumps,
        covered_offsets,
        is_complete,
    }
}

fn discover_function_prologues(binary: &[u8], base_address: u64) -> BTreeSet<u64> {
    let mut entries = BTreeSet::new();
    if binary.len() < 4 {
        return entries;
    }

    for offset in 0..=binary.len() - 4 {
        if binary[offset..offset + 4] == [0x55, 0x48, 0x89, 0xe5] {
            entries.insert(base_address + offset as u64);
        }
    }

    entries
}

fn discover_heuristic_function_starts(binary: &[u8], base_address: u64) -> BTreeSet<u64> {
    let mut entries = BTreeSet::new();
    let mut offset = 0;

    while offset < binary.len() {
        if !matches!(binary[offset], 0xc3 | 0xcc) {
            offset += 1;
            continue;
        }

        let mut next = offset + 1;
        while next < binary.len() && matches!(binary[next], 0xcc | 0x90) {
            next += 1;
        }

        for alignment in [16_u64, 8_u64] {
            let candidate = align_up(base_address + next as u64, alignment);
            let Some(candidate_offset) = address_to_offset(candidate, base_address, binary.len())
            else {
                continue;
            };

            if candidate_offset < next || !looks_like_function_start(binary, candidate_offset) {
                continue;
            }

            entries.insert(candidate);
        }

        offset = next;
    }

    entries
}

fn looks_like_function_start(binary: &[u8], offset: usize) -> bool {
    let Some(byte) = binary.get(offset).copied() else {
        return false;
    };

    matches!(byte, 0x55 | 0x48 | 0x53 | 0x56 | 0x57 | 0x90 | 0x41..=0x4f)
}

fn recovered_block_to_pcode(block: &RecoveredBlock) -> PcodeBlock {
    let mut instructions = Vec::new();
    let mut unique_seed = 0_u64;

    for instruction in &block.instructions {
        translate_instruction(instruction, &mut instructions, &mut unique_seed);
    }

    let (fall_through, branch_targets) = classify_edges(block);

    PcodeBlock { address: block.address, instructions, fall_through, branch_targets }
}

fn translate_instruction(
    instruction: &RawInstruction,
    lowered: &mut Vec<PcodeInstruction>,
    unique_seed: &mut u64,
) {
    match instruction.mnemonic.as_str() {
        "mov" => translate_mov(instruction, lowered, unique_seed),
        "add" => translate_binary_op(instruction, PcodeOp::IntAdd, lowered, unique_seed),
        "sub" => translate_binary_op(instruction, PcodeOp::IntSub, lowered, unique_seed),
        "cmp" => translate_cmp(instruction, lowered, unique_seed),
        "jmp" => translate_branch(instruction, PcodeOp::Branch, flag_varnode("zf"), lowered),
        "je" => translate_branch(instruction, PcodeOp::CBranch, flag_varnode("zf"), lowered),
        "jne" => translate_branch(instruction, PcodeOp::CBranch, flag_varnode("nzf"), lowered),
        "call" => translate_call(instruction, lowered, unique_seed),
        "ret" => lowered.push(PcodeInstruction {
            opcode: PcodeOp::Return,
            output: None,
            inputs: vec![register_varnode("rax", 8)],
            address: instruction.address,
        }),
        "push" => translate_push(instruction, lowered),
        "pop" => translate_pop(instruction, lowered),
        "lea" => translate_lea(instruction, lowered, unique_seed),
        _ => {}
    }
}

fn translate_mov(
    instruction: &RawInstruction,
    lowered: &mut Vec<PcodeInstruction>,
    unique_seed: &mut u64,
) {
    let [destination, source] = instruction.operands.as_slice() else {
        return;
    };

    match destination {
        InstructionOperand::Register(register) => {
            let output = register_varnode(register, operand_size(destination));
            let (opcode, input) = if matches!(source, InstructionOperand::Memory { .. }) {
                (
                    PcodeOp::Load,
                    effective_address_varnode(source, instruction.address, lowered, unique_seed),
                )
            } else {
                (
                    PcodeOp::Copy,
                    materialize_operand(source, instruction.address, lowered, unique_seed),
                )
            };

            lowered.push(PcodeInstruction {
                opcode,
                output: Some(output),
                inputs: vec![input],
                address: instruction.address,
            });
        }
        InstructionOperand::Memory { .. } => {
            let address =
                effective_address_varnode(destination, instruction.address, lowered, unique_seed);
            let value = materialize_operand(source, instruction.address, lowered, unique_seed);

            lowered.push(PcodeInstruction {
                opcode: PcodeOp::Store,
                output: None,
                inputs: vec![address, value],
                address: instruction.address,
            });
        }
        InstructionOperand::Immediate(_) | InstructionOperand::Label(_) => {}
    }
}

fn translate_binary_op(
    instruction: &RawInstruction,
    opcode: PcodeOp,
    lowered: &mut Vec<PcodeInstruction>,
    unique_seed: &mut u64,
) {
    let [destination, source] = instruction.operands.as_slice() else {
        return;
    };

    let InstructionOperand::Register(register) = destination else {
        return;
    };

    let output = register_varnode(register, operand_size(destination));
    let rhs = materialize_operand(source, instruction.address, lowered, unique_seed);

    lowered.push(PcodeInstruction {
        opcode,
        output: Some(output),
        inputs: vec![output, rhs],
        address: instruction.address,
    });
}

fn translate_cmp(
    instruction: &RawInstruction,
    lowered: &mut Vec<PcodeInstruction>,
    unique_seed: &mut u64,
) {
    let [lhs_operand, rhs_operand] = instruction.operands.as_slice() else {
        return;
    };

    let lhs = materialize_operand(lhs_operand, instruction.address, lowered, unique_seed);
    let rhs = materialize_operand(rhs_operand, instruction.address, lowered, unique_seed);
    let diff = unique_varnode(instruction.address, next_unique(unique_seed), 8);
    let zero = const_varnode(0, 8);

    lowered.push(PcodeInstruction {
        opcode: PcodeOp::IntSub,
        output: Some(diff),
        inputs: vec![lhs, rhs],
        address: instruction.address,
    });
    lowered.push(PcodeInstruction {
        opcode: PcodeOp::IntEqual,
        output: Some(flag_varnode("zf")),
        inputs: vec![diff, zero],
        address: instruction.address,
    });
    lowered.push(PcodeInstruction {
        opcode: PcodeOp::IntNotEqual,
        output: Some(flag_varnode("nzf")),
        inputs: vec![diff, zero],
        address: instruction.address,
    });
}

fn translate_branch(
    instruction: &RawInstruction,
    opcode: PcodeOp,
    flag: VarNode,
    lowered: &mut Vec<PcodeInstruction>,
) {
    let Some(first_operand) = instruction.operands.first() else {
        return;
    };

    let target = match first_operand {
        InstructionOperand::Label(target) => const_varnode(*target as i64, 8),
        _ => return,
    };

    let inputs = if opcode == PcodeOp::CBranch { vec![target, flag] } else { vec![target] };

    lowered.push(PcodeInstruction { opcode, output: None, inputs, address: instruction.address });
}

fn translate_call(
    instruction: &RawInstruction,
    lowered: &mut Vec<PcodeInstruction>,
    unique_seed: &mut u64,
) {
    let Some(target_operand) = instruction.operands.first() else {
        return;
    };

    let (opcode, target) = match target_operand {
        InstructionOperand::Label(target) => (PcodeOp::Call, const_varnode(*target as i64, 8)),
        InstructionOperand::Register(register) => {
            (PcodeOp::CallInd, register_varnode(register, operand_size(target_operand)))
        }
        InstructionOperand::Memory { .. } => (
            PcodeOp::CallInd,
            effective_address_varnode(target_operand, instruction.address, lowered, unique_seed),
        ),
        InstructionOperand::Immediate(value) => (PcodeOp::Call, const_varnode(*value, 8)),
    };

    let mut inputs = vec![target];
    inputs.extend(call_arg_varnodes());

    lowered.push(PcodeInstruction {
        opcode,
        output: Some(register_varnode("rax", 8)),
        inputs,
        address: instruction.address,
    });
}

fn translate_push(instruction: &RawInstruction, lowered: &mut Vec<PcodeInstruction>) {
    let Some(source) = instruction.operands.first() else {
        return;
    };

    lowered.push(PcodeInstruction {
        opcode: PcodeOp::Store,
        output: None,
        inputs: vec![stack_slot_varnode(instruction.address, 0), simple_operand_varnode(source)],
        address: instruction.address,
    });
}

fn translate_pop(instruction: &RawInstruction, lowered: &mut Vec<PcodeInstruction>) {
    let Some(InstructionOperand::Register(destination)) = instruction.operands.first() else {
        return;
    };

    lowered.push(PcodeInstruction {
        opcode: PcodeOp::Load,
        output: Some(register_varnode(destination, 8)),
        inputs: vec![stack_slot_varnode(instruction.address, 0)],
        address: instruction.address,
    });
}

fn translate_lea(
    instruction: &RawInstruction,
    lowered: &mut Vec<PcodeInstruction>,
    unique_seed: &mut u64,
) {
    let [InstructionOperand::Register(destination), source] = instruction.operands.as_slice()
    else {
        return;
    };

    let InstructionOperand::Memory { base, index, scale, displacement } = source else {
        return;
    };

    let output = register_varnode(destination, 8);
    let base_node = base
        .as_deref()
        .map(|register| register_varnode(register, 8))
        .unwrap_or_else(|| const_varnode(0, 8));

    let input = if let Some(index_register) = index.as_deref() {
        let scaled_index = if *scale > 1 {
            let temp = unique_varnode(instruction.address, next_unique(unique_seed), 8);
            lowered.push(PcodeInstruction {
                opcode: PcodeOp::IntMult,
                output: Some(temp),
                inputs: vec![register_varnode(index_register, 8), const_varnode(*scale as i64, 8)],
                address: instruction.address,
            });
            temp
        } else {
            register_varnode(index_register, 8)
        };

        let temp = unique_varnode(instruction.address, next_unique(unique_seed), 8);
        lowered.push(PcodeInstruction {
            opcode: PcodeOp::IntAdd,
            output: Some(temp),
            inputs: vec![base_node, scaled_index],
            address: instruction.address,
        });
        temp
    } else {
        base_node
    };

    lowered.push(PcodeInstruction {
        opcode: PcodeOp::IntAdd,
        output: Some(output),
        inputs: vec![input, const_varnode(*displacement, 8)],
        address: instruction.address,
    });
}

fn materialize_operand(
    operand: &InstructionOperand,
    address: u64,
    lowered: &mut Vec<PcodeInstruction>,
    unique_seed: &mut u64,
) -> VarNode {
    match operand {
        InstructionOperand::Memory { .. } => {
            let effective = effective_address_varnode(operand, address, lowered, unique_seed);
            let value = unique_varnode(address, next_unique(unique_seed), 8);
            lowered.push(PcodeInstruction {
                opcode: PcodeOp::Load,
                output: Some(value),
                inputs: vec![effective],
                address,
            });
            value
        }
        _ => simple_operand_varnode(operand),
    }
}

fn simple_operand_varnode(operand: &InstructionOperand) -> VarNode {
    match operand {
        InstructionOperand::Register(register) => register_varnode(register, operand_size(operand)),
        InstructionOperand::Immediate(value) => const_varnode(*value, operand_size(operand)),
        InstructionOperand::Label(address) => const_varnode(*address as i64, operand_size(operand)),
        InstructionOperand::Memory { .. } => stack_slot_varnode(0, 0),
    }
}

fn effective_address_varnode(
    operand: &InstructionOperand,
    address: u64,
    lowered: &mut Vec<PcodeInstruction>,
    unique_seed: &mut u64,
) -> VarNode {
    let InstructionOperand::Memory { base, index, scale, displacement } = operand else {
        return simple_operand_varnode(operand);
    };

    if base.is_none() && index.is_none() && *displacement >= 0 {
        return VarNode { address_space: AddressSpace::Ram, offset: *displacement as u64, size: 8 };
    }

    let base_node = base
        .as_deref()
        .map(|register| register_varnode(register, 8))
        .unwrap_or_else(|| const_varnode(0, 8));
    let mut current = base_node;

    if let Some(index_register) = index.as_deref() {
        let scaled_index = if *scale > 1 {
            let temp = unique_varnode(address, next_unique(unique_seed), 8);
            lowered.push(PcodeInstruction {
                opcode: PcodeOp::IntMult,
                output: Some(temp),
                inputs: vec![register_varnode(index_register, 8), const_varnode(*scale as i64, 8)],
                address,
            });
            temp
        } else {
            register_varnode(index_register, 8)
        };

        let temp = unique_varnode(address, next_unique(unique_seed), 8);
        lowered.push(PcodeInstruction {
            opcode: PcodeOp::IntAdd,
            output: Some(temp),
            inputs: vec![current, scaled_index],
            address,
        });
        current = temp;
    }

    let temp = unique_varnode(address, next_unique(unique_seed), 8);
    lowered.push(PcodeInstruction {
        opcode: PcodeOp::IntAdd,
        output: Some(temp),
        inputs: vec![current, const_varnode(*displacement, 8)],
        address,
    });
    temp
}

fn classify_edges(block: &RecoveredBlock) -> (Option<u64>, Vec<u64>) {
    let last_mnemonic = block.instructions.last().map(|instruction| instruction.mnemonic.as_str());

    match last_mnemonic {
        Some("je" | "jne") => (
            block.successors.get(1).copied(),
            block.successors.first().copied().into_iter().collect(),
        ),
        Some("jmp") => (None, block.successors.first().copied().into_iter().collect()),
        Some("call") => (block.successors.first().copied(), vec![]),
        _ => (block.successors.first().copied(), vec![]),
    }
}

fn locate_sink(
    functions: &[RecoveredFunction],
    sink_address: u64,
) -> Option<(&RecoveredFunction, usize, usize)> {
    for function in functions {
        for (block_index, block) in function.blocks.iter().enumerate() {
            for (instruction_index, instruction) in block.instructions.iter().enumerate() {
                if instruction.address == sink_address {
                    return Some((function, block_index, instruction_index));
                }
            }

            if block.address == sink_address && !block.instructions.is_empty() {
                return Some((function, block_index, block.instructions.len() - 1));
            }
        }
    }

    None
}

fn defs_of_instruction(instruction: &RawInstruction) -> BTreeSet<String> {
    let mut defs = BTreeSet::new();

    match instruction.mnemonic.as_str() {
        "mov" | "add" | "sub" | "lea" | "pop" => {
            if let Some(InstructionOperand::Register(register)) = instruction.operands.first() {
                defs.insert(register.clone());
            }
        }
        "cmp" => {
            defs.insert("zf".to_string());
            defs.insert("nzf".to_string());
        }
        "call" => {
            defs.insert("rax".to_string());
        }
        "push" => {
            defs.insert("rsp".to_string());
        }
        _ => {}
    }

    defs
}

fn uses_of_instruction(instruction: &RawInstruction) -> BTreeSet<String> {
    let mut uses = BTreeSet::new();

    match instruction.mnemonic.as_str() {
        "mov" => {
            if let [_, source] = instruction.operands.as_slice() {
                uses.extend(operand_uses(source));
            }
        }
        "add" | "sub" => {
            if let [destination, source] = instruction.operands.as_slice() {
                uses.extend(operand_uses(destination));
                uses.extend(operand_uses(source));
            }
        }
        "cmp" => {
            if let [lhs, rhs] = instruction.operands.as_slice() {
                uses.extend(operand_uses(lhs));
                uses.extend(operand_uses(rhs));
            }
        }
        "je" => {
            uses.insert("zf".to_string());
        }
        "jne" => {
            uses.insert("nzf".to_string());
        }
        "call" => {
            uses.extend(call_arg_register_names());
            if let Some(target) = instruction.operands.first() {
                uses.extend(operand_uses(target));
            }
        }
        "ret" => {
            uses.insert("rax".to_string());
        }
        "push" => {
            if let Some(source) = instruction.operands.first() {
                uses.extend(operand_uses(source));
            }
            uses.insert("rsp".to_string());
        }
        "pop" => {
            uses.insert("rsp".to_string());
        }
        "lea" => {
            if let [_, source] = instruction.operands.as_slice() {
                uses.extend(operand_uses(source));
            }
        }
        _ => {
            for operand in &instruction.operands {
                uses.extend(operand_uses(operand));
            }
        }
    }

    uses
}

fn operand_uses(operand: &InstructionOperand) -> BTreeSet<String> {
    let mut uses = BTreeSet::new();

    match operand {
        InstructionOperand::Register(register) => {
            uses.insert(register.clone());
        }
        InstructionOperand::Memory { base, index, .. } => {
            if let Some(base) = base {
                uses.insert(base.clone());
            }
            if let Some(index) = index {
                uses.insert(index.clone());
            }
        }
        InstructionOperand::Immediate(_) | InstructionOperand::Label(_) => {}
    }

    uses
}

fn call_arg_register_names() -> BTreeSet<String> {
    ["rdi", "rsi", "rdx", "rcx", "r8", "r9"].into_iter().map(str::to_string).collect()
}

fn call_arg_varnodes() -> Vec<VarNode> {
    ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
        .into_iter()
        .map(|register| register_varnode(register, 8))
        .collect()
}

fn decode_instruction(
    binary: &[u8],
    base_address: u64,
    address: u64,
) -> Option<DecodedInstruction> {
    let offset = address_to_offset(address, base_address, binary.len())?;
    let byte = *binary.get(offset)?;

    let mut rex = RexPrefix::default();
    let mut opcode_offset = offset;
    let mut prefix_len = 0usize;

    if (0x40..=0x4f).contains(&byte) {
        rex = RexPrefix::from_byte(byte);
        opcode_offset += 1;
        prefix_len = 1;
    }

    if let Some(decoded) = decode_with_prefix(binary, address, opcode_offset, prefix_len, rex) {
        return Some(decoded);
    }

    Some(DecodedInstruction {
        instruction: RawInstruction {
            address,
            size: 1,
            mnemonic: "db".to_string(),
            operands: vec![InstructionOperand::Immediate(i64::from(byte))],
        },
        control_flow: ControlFlowKind::Unknown,
    })
}

fn decode_with_prefix(
    binary: &[u8],
    address: u64,
    opcode_offset: usize,
    prefix_len: usize,
    rex: RexPrefix,
) -> Option<DecodedInstruction> {
    let opcode = *binary.get(opcode_offset)?;
    let operand_address = opcode_offset + 1;

    match opcode {
        0x50..=0x57 => {
            let register = register_name((opcode - 0x50) | if rex.b { 8 } else { 0 })?;
            Some(simple_instruction(address, prefix_len + 1, "push", vec![reg_operand(register)]))
        }
        0x58..=0x5f => {
            let register = register_name((opcode - 0x58) | if rex.b { 8 } else { 0 })?;
            Some(simple_instruction(address, prefix_len + 1, "pop", vec![reg_operand(register)]))
        }
        0x90 => Some(simple_instruction(address, prefix_len + 1, "nop", vec![])),
        0xc3 => Some(DecodedInstruction {
            instruction: RawInstruction {
                address,
                size: (prefix_len + 1) as u8,
                mnemonic: "ret".to_string(),
                operands: vec![],
            },
            control_flow: ControlFlowKind::Return,
        }),
        0xcc => Some(DecodedInstruction {
            instruction: RawInstruction {
                address,
                size: (prefix_len + 1) as u8,
                mnemonic: "int3".to_string(),
                operands: vec![],
            },
            control_flow: ControlFlowKind::Trap,
        }),
        0xe8 => {
            let displacement = read_i32(binary, operand_address)?;
            let size = (prefix_len + 5) as u8;
            let target = relative_target(address, size, i64::from(displacement));
            Some(DecodedInstruction {
                instruction: RawInstruction {
                    address,
                    size,
                    mnemonic: "call".to_string(),
                    operands: target
                        .map_or_else(Vec::new, |target| vec![InstructionOperand::Label(target)]),
                },
                control_flow: ControlFlowKind::Call { target },
            })
        }
        0xe9 => {
            let displacement = read_i32(binary, operand_address)?;
            let size = (prefix_len + 5) as u8;
            let target = relative_target(address, size, i64::from(displacement));
            Some(DecodedInstruction {
                instruction: RawInstruction {
                    address,
                    size,
                    mnemonic: "jmp".to_string(),
                    operands: target
                        .map_or_else(Vec::new, |target| vec![InstructionOperand::Label(target)]),
                },
                control_flow: ControlFlowKind::Jump { target, conditional: false },
            })
        }
        0xeb => {
            let displacement = i64::from(read_i8(binary, operand_address)?);
            let size = (prefix_len + 2) as u8;
            let target = relative_target(address, size, displacement);
            Some(DecodedInstruction {
                instruction: RawInstruction {
                    address,
                    size,
                    mnemonic: "jmp".to_string(),
                    operands: target
                        .map_or_else(Vec::new, |target| vec![InstructionOperand::Label(target)]),
                },
                control_flow: ControlFlowKind::Jump { target, conditional: false },
            })
        }
        0x74 | 0x75 => {
            let displacement = i64::from(read_i8(binary, operand_address)?);
            let size = (prefix_len + 2) as u8;
            let target = relative_target(address, size, displacement);
            let mnemonic = if opcode == 0x74 { "je" } else { "jne" };
            Some(DecodedInstruction {
                instruction: RawInstruction {
                    address,
                    size,
                    mnemonic: mnemonic.to_string(),
                    operands: target
                        .map_or_else(Vec::new, |target| vec![InstructionOperand::Label(target)]),
                },
                control_flow: ControlFlowKind::Jump { target, conditional: true },
            })
        }
        0x0f => decode_extended_jump(binary, address, opcode_offset, prefix_len),
        0x89 | 0x8b | 0x01 | 0x03 | 0x29 | 0x2b | 0x39 | 0x3b | 0x8d => {
            decode_modrm_binary(binary, address, operand_address, prefix_len, rex, opcode)
        }
        0x81 | 0x83 => decode_group_one(binary, address, operand_address, prefix_len, rex, opcode),
        0xff => decode_ff_group(binary, address, operand_address, prefix_len, rex),
        _ => None,
    }
}

fn decode_extended_jump(
    binary: &[u8],
    address: u64,
    opcode_offset: usize,
    prefix_len: usize,
) -> Option<DecodedInstruction> {
    let opcode = *binary.get(opcode_offset + 1)?;
    let displacement = read_i32(binary, opcode_offset + 2)?;
    let size = (prefix_len + 6) as u8;
    let target = relative_target(address, size, i64::from(displacement));

    let mnemonic = match opcode {
        0x84 => "je",
        0x85 => "jne",
        _ => return None,
    };

    Some(DecodedInstruction {
        instruction: RawInstruction {
            address,
            size,
            mnemonic: mnemonic.to_string(),
            operands: target
                .map_or_else(Vec::new, |target| vec![InstructionOperand::Label(target)]),
        },
        control_flow: ControlFlowKind::Jump { target, conditional: true },
    })
}

fn decode_modrm_binary(
    binary: &[u8],
    address: u64,
    operand_offset: usize,
    prefix_len: usize,
    rex: RexPrefix,
    opcode: u8,
) -> Option<DecodedInstruction> {
    let modrm = parse_modrm(*binary.get(operand_offset)?, rex);
    let (rm_operand, rm_size) = decode_rm_operand(binary, operand_offset + 1, modrm, rex)?;
    let reg_operand = reg_operand(register_name(modrm.reg)?);

    let (mnemonic, operands) = match opcode {
        0x89 => ("mov", vec![rm_operand, reg_operand]),
        0x8b => ("mov", vec![reg_operand, rm_operand]),
        0x01 => ("add", vec![rm_operand, reg_operand]),
        0x03 => ("add", vec![reg_operand, rm_operand]),
        0x29 => ("sub", vec![rm_operand, reg_operand]),
        0x2b => ("sub", vec![reg_operand, rm_operand]),
        0x39 => ("cmp", vec![rm_operand, reg_operand]),
        0x3b => ("cmp", vec![reg_operand, rm_operand]),
        0x8d => ("lea", vec![reg_operand, rm_operand]),
        _ => return None,
    };

    Some(simple_instruction(address, prefix_len + 2 + rm_size, mnemonic, operands))
}

fn decode_group_one(
    binary: &[u8],
    address: u64,
    operand_offset: usize,
    prefix_len: usize,
    rex: RexPrefix,
    opcode: u8,
) -> Option<DecodedInstruction> {
    let modrm = parse_modrm(*binary.get(operand_offset)?, rex);
    let (destination, operand_size) = decode_rm_operand(binary, operand_offset + 1, modrm, rex)?;
    let extension = modrm.reg_raw & 0b111;
    let (mnemonic, immediate, immediate_size) = match opcode {
        0x83 => match extension {
            0 => ("add", i64::from(read_i8(binary, operand_offset + 1 + operand_size)?), 1),
            5 => ("sub", i64::from(read_i8(binary, operand_offset + 1 + operand_size)?), 1),
            7 => ("cmp", i64::from(read_i8(binary, operand_offset + 1 + operand_size)?), 1),
            _ => return None,
        },
        0x81 => match extension {
            0 => ("add", i64::from(read_i32(binary, operand_offset + 1 + operand_size)?), 4),
            5 => ("sub", i64::from(read_i32(binary, operand_offset + 1 + operand_size)?), 4),
            7 => ("cmp", i64::from(read_i32(binary, operand_offset + 1 + operand_size)?), 4),
            _ => return None,
        },
        _ => return None,
    };

    Some(simple_instruction(
        address,
        prefix_len + 2 + operand_size + immediate_size,
        mnemonic,
        vec![destination, InstructionOperand::Immediate(immediate)],
    ))
}

fn decode_ff_group(
    binary: &[u8],
    address: u64,
    operand_offset: usize,
    prefix_len: usize,
    rex: RexPrefix,
) -> Option<DecodedInstruction> {
    let modrm = parse_modrm(*binary.get(operand_offset)?, rex);
    let (operand, operand_size) = decode_rm_operand(binary, operand_offset + 1, modrm, rex)?;
    let size = (prefix_len + 2 + operand_size) as u8;

    match modrm.reg_raw & 0b111 {
        2 => Some(DecodedInstruction {
            instruction: RawInstruction {
                address,
                size,
                mnemonic: "call".to_string(),
                operands: vec![operand],
            },
            control_flow: ControlFlowKind::Call { target: None },
        }),
        4 => Some(DecodedInstruction {
            instruction: RawInstruction {
                address,
                size,
                mnemonic: "jmp".to_string(),
                operands: vec![operand],
            },
            control_flow: ControlFlowKind::Jump { target: None, conditional: false },
        }),
        _ => None,
    }
}

fn parse_modrm(byte: u8, rex: RexPrefix) -> ModRm {
    let reg_raw = (byte >> 3) & 0b111;
    let rm_raw = byte & 0b111;

    ModRm {
        mode: byte >> 6,
        reg: reg_raw | if rex.r { 8 } else { 0 },
        rm: rm_raw | if rex.b { 8 } else { 0 },
        reg_raw,
        rm_raw,
    }
}

fn parse_sib(byte: u8, rex: RexPrefix) -> Sib {
    let index_raw = (byte >> 3) & 0b111;
    let base_raw = byte & 0b111;

    Sib {
        scale: (byte >> 6) & 0b11,
        index: index_raw | if rex.x { 8 } else { 0 },
        base: base_raw | if rex.b { 8 } else { 0 },
        index_raw,
        base_raw,
    }
}

fn decode_rm_operand(
    binary: &[u8],
    offset: usize,
    modrm: ModRm,
    rex: RexPrefix,
) -> Option<(InstructionOperand, usize)> {
    if modrm.mode == 0b11 {
        return Some((reg_operand(register_name(modrm.rm)?), 0));
    }

    let mut consumed = 0usize;

    if modrm.rm_raw == 0b100 {
        let sib = parse_sib(*binary.get(offset)?, rex);
        consumed += 1;

        let index = if sib.index_raw == 0b100 && !rex.x {
            None
        } else {
            Some(register_name(sib.index)?.to_string())
        };

        let (base, displacement) = match modrm.mode {
            0b00 if sib.base_raw == 0b101 && !rex.b => {
                let displacement = i64::from(read_i32(binary, offset + 1)?);
                consumed += 4;
                (None, displacement)
            }
            0b00 => (Some(register_name(sib.base)?.to_string()), 0),
            0b01 => {
                let displacement = i64::from(read_i8(binary, offset + 1)?);
                consumed += 1;
                (Some(register_name(sib.base)?.to_string()), displacement)
            }
            0b10 => {
                let displacement = i64::from(read_i32(binary, offset + 1)?);
                consumed += 4;
                (Some(register_name(sib.base)?.to_string()), displacement)
            }
            _ => return None,
        };

        return Some((
            InstructionOperand::Memory { base, index, scale: 1_u8 << sib.scale, displacement },
            consumed,
        ));
    }

    let (base, displacement) = match modrm.mode {
        0b00 if modrm.rm_raw == 0b101 && !rex.b => {
            let displacement = i64::from(read_i32(binary, offset)?);
            consumed += 4;
            (Some("rip".to_string()), displacement)
        }
        0b00 => (Some(register_name(modrm.rm)?.to_string()), 0),
        0b01 => {
            let displacement = i64::from(read_i8(binary, offset)?);
            consumed += 1;
            (Some(register_name(modrm.rm)?.to_string()), displacement)
        }
        0b10 => {
            let displacement = i64::from(read_i32(binary, offset)?);
            consumed += 4;
            (Some(register_name(modrm.rm)?.to_string()), displacement)
        }
        _ => return None,
    };

    Some((InstructionOperand::Memory { base, index: None, scale: 1, displacement }, consumed))
}

fn infer_base_address(symbols: &[crate::binary::BinarySymbol]) -> u64 {
    symbols
        .iter()
        .filter(|symbol| symbol.kind == SymbolKind::Function)
        .map(|symbol| symbol.address)
        .min()
        .unwrap_or(0)
}

fn address_to_offset(address: u64, base_address: u64, len: usize) -> Option<usize> {
    let offset = usize::try_from(address.checked_sub(base_address)?).ok()?;
    (offset < len).then_some(offset)
}

fn address_in_range(address: u64, base_address: u64, len: usize) -> bool {
    address_to_offset(address, base_address, len).is_some()
}

fn align_up(value: u64, alignment: u64) -> u64 {
    if alignment <= 1 { value } else { value.div_ceil(alignment) * alignment }
}

fn relative_target(address: u64, size: u8, displacement: i64) -> Option<u64> {
    let next = i128::from(address) + i128::from(size);
    let target = next + i128::from(displacement);
    (0..=i128::from(u64::MAX)).contains(&target).then_some(target as u64)
}

fn read_i8(binary: &[u8], offset: usize) -> Option<i8> {
    binary.get(offset).copied().map(|byte| byte as i8)
}

fn read_i32(binary: &[u8], offset: usize) -> Option<i32> {
    let bytes = binary.get(offset..offset + 4)?;
    Some(i32::from_le_bytes(bytes.try_into().ok()?))
}

fn simple_instruction(
    address: u64,
    size: usize,
    mnemonic: &str,
    operands: Vec<InstructionOperand>,
) -> DecodedInstruction {
    DecodedInstruction {
        instruction: RawInstruction {
            address,
            size: size as u8,
            mnemonic: mnemonic.to_string(),
            operands,
        },
        control_flow: ControlFlowKind::None,
    }
}

fn reg_operand(register: &str) -> InstructionOperand {
    InstructionOperand::Register(register.to_string())
}

fn register_name(index: u8) -> Option<&'static str> {
    match index {
        0 => Some("rax"),
        1 => Some("rcx"),
        2 => Some("rdx"),
        3 => Some("rbx"),
        4 => Some("rsp"),
        5 => Some("rbp"),
        6 => Some("rsi"),
        7 => Some("rdi"),
        8 => Some("r8"),
        9 => Some("r9"),
        10 => Some("r10"),
        11 => Some("r11"),
        12 => Some("r12"),
        13 => Some("r13"),
        14 => Some("r14"),
        15 => Some("r15"),
        _ => None,
    }
}

fn register_varnode(register: &str, size: u8) -> VarNode {
    VarNode {
        address_space: AddressSpace::Register,
        offset: match register {
            "rax" => 0,
            "rdi" => 1,
            "rsi" => 2,
            "rdx" => 3,
            "rcx" => 4,
            "r8" => 5,
            "r9" => 6,
            "rbp" => 7,
            "rsp" => 8,
            "rbx" => 9,
            "r10" => 10,
            "r11" => 11,
            "r12" => 12,
            "r13" => 13,
            "r14" => 14,
            "r15" => 15,
            "rip" => 16,
            "zf" => 17,
            "nzf" => 18,
            _ => 0xff,
        },
        size,
    }
}

fn flag_varnode(name: &str) -> VarNode {
    register_varnode(name, 1)
}

fn const_varnode(value: i64, size: u8) -> VarNode {
    VarNode { address_space: AddressSpace::Const, offset: value as u64, size }
}

fn unique_varnode(address: u64, unique_seed: u64, size: u8) -> VarNode {
    VarNode {
        address_space: AddressSpace::Unique,
        offset: address.wrapping_shl(8) ^ unique_seed,
        size,
    }
}

fn stack_slot_varnode(address: u64, ordinal: u64) -> VarNode {
    VarNode { address_space: AddressSpace::Ram, offset: address.wrapping_add(ordinal), size: 8 }
}

fn next_unique(seed: &mut u64) -> u64 {
    let current = *seed;
    *seed = seed.wrapping_add(1);
    current
}

fn operand_size(operand: &InstructionOperand) -> u8 {
    match operand {
        InstructionOperand::Register(_) | InstructionOperand::Immediate(_) => 8,
        InstructionOperand::Memory { .. } | InstructionOperand::Label(_) => 8,
    }
}

fn sort_and_dedup(values: &mut Vec<u64>) {
    let mut seen = BTreeSet::new();
    values.retain(|value| seen.insert(*value));
}

fn intersects(lhs: &BTreeSet<String>, rhs: &BTreeSet<String>) -> bool {
    lhs.iter().any(|value| rhs.contains(value))
}

impl RexPrefix {
    fn from_byte(byte: u8) -> Self {
        Self { r: (byte & 0b0100) != 0, x: (byte & 0b0010) != 0, b: (byte & 0b0001) != 0 }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::binary::{BinarySymbol, SymbolKind};

    #[test]
    fn test_cfg_fast_from_symbols() {
        let binary = vec![
            0x55, 0x48, 0x89, 0xe5, 0xe8, 0x07, 0x00, 0x00, 0x00, 0x5d, 0xc3, 0xcc, 0xcc, 0xcc,
            0xcc, 0xcc, 0x55, 0x48, 0x89, 0xe5, 0x5d, 0xc3,
        ];
        let symbols = vec![
            BinarySymbol {
                name: "main".to_string(),
                address: 0x1000,
                size: 11,
                kind: SymbolKind::Function,
            },
            BinarySymbol {
                name: "helper".to_string(),
                address: 0x1010,
                size: 6,
                kind: SymbolKind::Function,
            },
        ];

        let result = cfg_fast_recover(&binary, &symbols, &CfgFastConfig::default());

        assert_eq!(result.functions.len(), 2);
        assert!(result.functions.iter().any(|function| function.name.as_deref() == Some("main")));
        assert!(result.functions.iter().any(|function| function.name.as_deref() == Some("helper")));
        assert!(result.coverage > 0.0);
        assert!(result.unresolved_jumps.is_empty());
    }

    #[test]
    fn test_function_prologue_detection() {
        let binary = [0x55, 0x48, 0x89, 0xe5, 0x5d, 0xc3];
        let result = cfg_fast_recover(
            &binary,
            &[],
            &CfgFastConfig {
                max_iterations: 128,
                heuristic_function_starts: false,
                follow_calls: false,
            },
        );

        assert_eq!(result.functions.len(), 1);
        assert_eq!(result.functions[0].entry_address, 0);
        assert_eq!(result.functions[0].blocks[0].instructions[0].mnemonic, "push");
    }

    #[test]
    fn test_recovered_to_pcode() {
        let function = RecoveredFunction {
            entry_address: 0x1000,
            name: Some("add_then_return".to_string()),
            size: 7,
            blocks: vec![RecoveredBlock {
                address: 0x1000,
                size: 7,
                instructions: vec![
                    RawInstruction {
                        address: 0x1000,
                        size: 3,
                        mnemonic: "mov".to_string(),
                        operands: vec![
                            InstructionOperand::Register("rax".to_string()),
                            InstructionOperand::Register("rdi".to_string()),
                        ],
                    },
                    RawInstruction {
                        address: 0x1003,
                        size: 3,
                        mnemonic: "add".to_string(),
                        operands: vec![
                            InstructionOperand::Register("rax".to_string()),
                            InstructionOperand::Register("rsi".to_string()),
                        ],
                    },
                    RawInstruction {
                        address: 0x1006,
                        size: 1,
                        mnemonic: "ret".to_string(),
                        operands: vec![],
                    },
                ],
                successors: vec![],
                is_call: false,
                call_target: None,
            }],
            is_complete: true,
        };

        let pcode = recovered_to_pcode(&function);

        assert_eq!(pcode.name, "add_then_return");
        assert_eq!(pcode.blocks.len(), 1);
        assert_eq!(pcode.blocks[0].instructions.len(), 3);
        assert_eq!(pcode.blocks[0].instructions[0].opcode, PcodeOp::Copy);
        assert_eq!(pcode.blocks[0].instructions[1].opcode, PcodeOp::IntAdd);
        assert_eq!(pcode.blocks[0].instructions[2].opcode, PcodeOp::Return);
    }

    #[test]
    fn test_backward_slice() {
        let function = RecoveredFunction {
            entry_address: 0x1000,
            name: Some("main".to_string()),
            size: 8,
            blocks: vec![RecoveredBlock {
                address: 0x1000,
                size: 8,
                instructions: vec![
                    RawInstruction {
                        address: 0x1000,
                        size: 3,
                        mnemonic: "mov".to_string(),
                        operands: vec![
                            InstructionOperand::Register("rax".to_string()),
                            InstructionOperand::Register("rbx".to_string()),
                        ],
                    },
                    RawInstruction {
                        address: 0x1003,
                        size: 3,
                        mnemonic: "mov".to_string(),
                        operands: vec![
                            InstructionOperand::Register("rdi".to_string()),
                            InstructionOperand::Register("rax".to_string()),
                        ],
                    },
                    RawInstruction {
                        address: 0x1006,
                        size: 5,
                        mnemonic: "call".to_string(),
                        operands: vec![InstructionOperand::Label(0x2000)],
                    },
                ],
                successors: vec![],
                is_call: true,
                call_target: Some(0x2000),
            }],
            is_complete: true,
        };

        let slice = backward_slice(&[function], 0x1006);
        assert_eq!(slice, vec![0x1000, 0x1003]);
    }

    #[test]
    fn test_empty_binary() {
        let result = cfg_fast_recover(&[], &[], &CfgFastConfig::default());
        assert!(result.functions.is_empty());
        assert!(result.unresolved_jumps.is_empty());
        assert_eq!(result.coverage, 0.0);
    }
}
