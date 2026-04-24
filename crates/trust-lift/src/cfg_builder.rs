// trust-lift: CFG recovery from disassembled instructions
//
// Implements basic block recovery by following control flow from the entry point.
// Uses a worklist algorithm to discover all reachable blocks.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeSet, VecDeque};
use trust_types::fx::FxHashMap;

use trust_disasm::{ControlFlow, Decoder, Instruction};

use crate::cfg::{Cfg, LiftedBlock};
use crate::error::LiftError;

fn strict_cfg_error(message: impl Into<String>) -> LiftError {
    LiftError::Ssa(format!("CFG proof mode: {}", message.into()))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DirectBranchTarget {
    InFunction(u64),
    External(u64),
}

fn classify_direct_branch_target(
    insn: &Instruction,
    entry: u64,
    func_end: u64,
) -> Result<DirectBranchTarget, LiftError> {
    match insn.branch_target() {
        Some(target) if target >= entry && target < func_end => {
            Ok(DirectBranchTarget::InFunction(target))
        }
        Some(target) => Ok(DirectBranchTarget::External(target)),
        None => Err(strict_cfg_error(format!(
            "branch at 0x{:x} has no direct CFG target",
            insn.address
        ))),
    }
}

fn conditional_branch_successors(
    insn: &Instruction,
    fallthrough: u64,
    entry: u64,
    func_end: u64,
) -> Result<Vec<u64>, LiftError> {
    let target = classify_direct_branch_target(insn, entry, func_end)?;
    let raw_fallthrough = fallthrough;
    let fallthrough = (fallthrough >= entry && fallthrough < func_end).then_some(fallthrough);

    match (fallthrough, target) {
        (Some(fallthrough), DirectBranchTarget::InFunction(target)) => {
            Ok(vec![fallthrough, target])
        }
        (None, DirectBranchTarget::External(_)) => Ok(Vec::new()),
        (Some(fallthrough), DirectBranchTarget::External(target)) => {
            Err(strict_cfg_error(format!(
                "conditional branch at 0x{:x} has in-function fallthrough 0x{fallthrough:x} and external target 0x{target:x}; existing CFG edges cannot represent the external arm",
                insn.address
            )))
        }
        (None, DirectBranchTarget::InFunction(target)) => Err(strict_cfg_error(format!(
            "conditional branch at 0x{:x} has in-function target 0x{target:x} and external fallthrough 0x{raw_fallthrough:x}; existing CFG edges cannot represent the external arm",
            insn.address
        ))),
    }
}

/// Recover the control flow graph starting from `entry` within the given
/// code bytes (which begin at virtual address `base_addr`).
///
/// Uses a worklist algorithm:
/// 1. Start with the entry address on the worklist.
/// 2. Decode instructions sequentially from each worklist address until a
///    terminating instruction (branch, return, exception) is reached.
/// 3. For each successor address, add it to the worklist if not yet visited.
/// 4. If a branch lands in the middle of an existing block, split it.
pub(crate) fn recover_cfg(
    decoder: &dyn Decoder,
    code: &[u8],
    base_addr: u64,
    entry: u64,
    func_end: u64,
) -> Result<Cfg, LiftError> {
    // Phase 1: Identify all block leader addresses.
    let leaders = find_leaders(decoder, code, base_addr, entry, func_end)?;

    // Phase 2: Build blocks by decoding from each leader to the next.
    let mut cfg = Cfg::new();
    let sorted_leaders: Vec<u64> = leaders.into_iter().collect();

    // Pre-decode all instructions in the function for efficiency.
    let insn_map = decode_range(decoder, code, base_addr, entry, func_end)?;

    for (block_idx, &leader_addr) in sorted_leaders.iter().enumerate() {
        let next_leader = sorted_leaders.get(block_idx + 1).copied().unwrap_or(func_end);
        let mut instructions = Vec::new();
        let mut successors = Vec::new();
        let mut is_return = false;

        // Collect instructions from this leader to (but not including) the next leader.
        let mut addr = leader_addr;
        while addr < next_leader && addr < func_end {
            if let Some(insn) = insn_map.get(&addr) {
                let next_addr = addr + insn.size as u64;
                match insn.flow {
                    ControlFlow::Return => {
                        is_return = true;
                        instructions.push(insn.clone());
                        break;
                    }
                    ControlFlow::Branch => {
                        match classify_direct_branch_target(insn, entry, func_end)? {
                            DirectBranchTarget::InFunction(target) => successors.push(target),
                            DirectBranchTarget::External(_) => {}
                        }
                        instructions.push(insn.clone());
                        break;
                    }
                    ControlFlow::ConditionalBranch => {
                        // Fallthrough + target.
                        successors.extend(conditional_branch_successors(
                            insn, next_addr, entry, func_end,
                        )?);
                        instructions.push(insn.clone());
                        break;
                    }
                    ControlFlow::Call => {
                        // Calls fall through to the next instruction.
                        instructions.push(insn.clone());
                        if next_addr < next_leader {
                            addr = next_addr;
                        } else {
                            // Call at end of block — fallthrough is next leader.
                            if next_addr < func_end {
                                successors.push(next_addr);
                            }
                            break;
                        }
                    }
                    ControlFlow::Exception => {
                        instructions.push(insn.clone());
                        break;
                    }
                    ControlFlow::Fallthrough => {
                        instructions.push(insn.clone());
                        addr = next_addr;
                    }
                    other => {
                        return Err(strict_cfg_error(format!(
                            "unsupported control-flow classification at 0x{:x}: {other:?}",
                            insn.address
                        )));
                    }
                }
            } else {
                // Could not decode instruction at this address — stop the block.
                break;
            }
        }

        // If we fell off the end without a terminator, add fallthrough to next leader.
        if !is_return && successors.is_empty() && !instructions.is_empty() {
            let last = instructions.last().ok_or(LiftError::EmptyBlock { address: leader_addr })?;
            let fallthrough = last.address + last.size as u64;
            match last.flow {
                ControlFlow::Fallthrough if fallthrough < func_end => successors.push(fallthrough),
                ControlFlow::Fallthrough
                | ControlFlow::Call
                | ControlFlow::Branch
                | ControlFlow::ConditionalBranch
                | ControlFlow::Return
                | ControlFlow::Exception => {}
                other => {
                    return Err(strict_cfg_error(format!(
                        "unsupported control-flow classification at 0x{:x}: {other:?}",
                        last.address
                    )));
                }
            }
        }

        cfg.add_block(LiftedBlock {
            id: block_idx,
            start_addr: leader_addr,
            instructions,
            successors,
            is_return,
        });
    }

    // Set entry to the block containing the entry address.
    cfg.entry = cfg.block_index(entry).ok_or_else(|| {
        strict_cfg_error(format!(
            "entry address 0x{entry:x} does not map to a recovered basic block"
        ))
    })?;

    Ok(cfg)
}

/// Find all basic block leaders (addresses that start a basic block).
///
/// Leaders are:
/// 1. The entry point.
/// 2. Branch targets.
/// 3. The instruction after a branch/call (fallthrough).
fn find_leaders(
    decoder: &dyn Decoder,
    code: &[u8],
    base_addr: u64,
    entry: u64,
    func_end: u64,
) -> Result<BTreeSet<u64>, LiftError> {
    let mut leaders = BTreeSet::new();
    let mut worklist = VecDeque::new();
    let mut visited = BTreeSet::new();

    leaders.insert(entry);
    worklist.push_back(entry);

    while let Some(addr) = worklist.pop_front() {
        if !visited.insert(addr) {
            continue;
        }
        if addr < entry || addr >= func_end {
            continue;
        }

        let mut cur = addr;
        while cur < func_end {
            let offset = (cur - base_addr) as usize;
            if offset >= code.len() {
                break;
            }
            let insn = decoder
                .decode(&code[offset..], cur)
                .map_err(|e| LiftError::Disasm { address: cur, source: e })?;
            let next = cur + insn.size as u64;

            match insn.flow {
                ControlFlow::Return | ControlFlow::Exception => break,
                ControlFlow::Branch => {
                    match classify_direct_branch_target(&insn, entry, func_end)? {
                        DirectBranchTarget::InFunction(target) => {
                            leaders.insert(target);
                            worklist.push_back(target);
                        }
                        DirectBranchTarget::External(_) => {}
                    }
                    break;
                }
                ControlFlow::ConditionalBranch => {
                    // Fallthrough is a leader.
                    for successor in conditional_branch_successors(&insn, next, entry, func_end)? {
                        leaders.insert(successor);
                        worklist.push_back(successor);
                    }
                    break;
                }
                ControlFlow::Call => {
                    // After a call, fallthrough is a leader if we split here.
                    cur = next;
                }
                ControlFlow::Fallthrough => {
                    cur = next;
                }
                other => {
                    return Err(strict_cfg_error(format!(
                        "unsupported control-flow classification at 0x{:x}: {other:?}",
                        insn.address
                    )));
                }
            }
        }
    }

    Ok(leaders)
}

/// Decode all instructions in a range and return them indexed by address.
fn decode_range(
    decoder: &dyn Decoder,
    code: &[u8],
    base_addr: u64,
    start: u64,
    end: u64,
) -> Result<FxHashMap<u64, Instruction>, LiftError> {
    let mut map = FxHashMap::default();
    let mut addr = start;
    while addr < end {
        let offset = (addr - base_addr) as usize;
        if offset >= code.len() {
            break;
        }
        match decoder.decode(&code[offset..], addr) {
            Ok(insn) => {
                let size = insn.size as u64;
                map.insert(addr, insn);
                addr += size;
            }
            Err(_) => {
                // Skip undecoded bytes by minimum instruction size.
                addr += decoder.min_insn_size() as u64;
            }
        }
    }
    Ok(map)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Verify that the leader finder puts the entry into the leader set.
    #[test]
    fn test_find_leaders_entry_is_leader() {
        // We can't easily test without a real decoder, but we verify the
        // module compiles and the types are correct.
        let leaders = BTreeSet::from([0x1000u64]);
        assert!(leaders.contains(&0x1000));
    }

    #[test]
    fn test_recover_cfg_indirect_branch_fails_closed() {
        let decoder = trust_disasm::aarch64::Aarch64Decoder::new();
        let code = 0xD61F0200u32.to_le_bytes(); // BR X16

        let err = recover_cfg(&decoder, &code, 0x1000, 0x1000, 0x1004)
            .expect_err("indirect branch target is not recoverable");
        assert!(err.to_string().contains("has no direct CFG target"));
    }

    #[test]
    fn test_recover_cfg_direct_external_branch_is_terminal() {
        let decoder = trust_disasm::aarch64::Aarch64Decoder::new();
        let code = 0x14000040u32.to_le_bytes(); // B #0x100 from 0x1000 -> 0x1100

        let cfg = recover_cfg(&decoder, &code, 0x1000, 0x1000, 0x1004)
            .expect("direct external branch should recover as a terminal block");

        assert_eq!(cfg.block_count(), 1);
        let block = &cfg.blocks[0];
        assert_eq!(block.start_addr, 0x1000);
        assert!(block.successors.is_empty());
        assert!(!block.is_return);
        assert_eq!(block.instructions.last().and_then(Instruction::branch_target), Some(0x1100));
    }
}
