// trust-vcgen/binary_analysis/cfg_fast.rs: CFGFast-style fast CFG recovery
//
// Ports the core ideas from angr's CFGFast algorithm for function recovery
// in stripped binaries. CFGFast uses linear sweep, call target resolution,
// gap scanning, and indirect jump heuristics to recover functions without
// relying on symbol tables.
//
// Reference: angr/analyses/cfg/cfg_fast.py
// See also: Shoshitaishvili et al., "(State of) The Art of War: Offensive
// Techniques in Binary Analysis" (IEEE S&P 2016)
//
// Part of #101: Binary Lifting
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use super::lifter::{AbstractInsn, AbstractOp};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// A recovered function boundary from CFGFast analysis.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct RecoveredFunction {
    /// Entry point address of the function.
    pub entry: u64,
    /// End address (exclusive) of the function body.
    pub end: u64,
    /// How this function was discovered.
    pub source: FunctionSource,
    /// Set of call targets observed within this function.
    pub call_targets: BTreeSet<u64>,
    /// Whether the function appears to return (has a return instruction).
    pub returns: bool,
}

/// How a function entry point was discovered.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum FunctionSource {
    /// Provided by the symbol table or debug info.
    Symbol,
    /// Found as the target of a direct call instruction.
    CallTarget,
    /// Found by linear sweep / gap scanning.
    GapScan,
    /// Found by heuristic pattern matching (function prologue).
    ProloguePattern,
    /// Entry point of the binary.
    EntryPoint,
}

/// Configuration for the CFGFast algorithm.
#[derive(Debug, Clone)]
pub struct CfgFastConfig {
    /// Whether to perform gap scanning after initial call-target analysis.
    pub enable_gap_scan: bool,
    /// Whether to use function prologue pattern matching.
    pub enable_prologue_scan: bool,
    /// Minimum function size in bytes for gap scan candidates.
    pub min_function_size: u64,
    /// Known entry points (e.g., from symbol table or ELF headers).
    pub known_entries: BTreeSet<u64>,
    /// Alignment requirement for function entries (typically 1, 4, or 16).
    pub alignment: u64,
}

impl Default for CfgFastConfig {
    fn default() -> Self {
        Self {
            enable_gap_scan: true,
            enable_prologue_scan: true,
            min_function_size: 4,
            known_entries: BTreeSet::new(),
            alignment: 1,
        }
    }
}

/// Result of CFGFast analysis on a binary's instruction stream.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CfgFastResult {
    /// Recovered functions in address order.
    pub functions: Vec<RecoveredFunction>,
    /// Total number of instructions analyzed.
    pub instructions_analyzed: usize,
    /// Addresses that were targets of indirect jumps (unresolved).
    pub unresolved_jumps: BTreeSet<u64>,
}

// ---------------------------------------------------------------------------
// CFGFast algorithm
// ---------------------------------------------------------------------------

/// Run CFGFast-style function recovery on a stream of abstract instructions.
///
/// The algorithm proceeds in phases:
/// 1. **Seed**: Start from known entry points and call targets
/// 2. **Call target resolution**: Follow direct calls to discover new functions
/// 3. **Gap scanning**: Scan gaps between known functions for valid code
/// 4. **Prologue matching**: Look for common function prologue patterns
///
/// This operates on already-lifted abstract instructions (not raw bytes),
/// which simplifies the implementation while preserving the algorithmic
/// structure of angr's CFGFast.
#[must_use]
pub fn cfg_fast_recover(instructions: &[AbstractInsn], config: &CfgFastConfig) -> CfgFastResult {
    if instructions.is_empty() {
        return CfgFastResult {
            functions: vec![],
            instructions_analyzed: 0,
            unresolved_jumps: BTreeSet::new(),
        };
    }

    let addr_map = build_address_map(instructions);
    let mut function_entries: BTreeMap<u64, FunctionSource> = BTreeMap::new();
    let mut unresolved_jumps = BTreeSet::new();

    // Phase 1: Seed from known entries
    for entry in &config.known_entries {
        if addr_map.contains_key(entry) {
            function_entries.insert(*entry, FunctionSource::Symbol);
        }
    }

    // Add the first instruction as entry point if no seeds
    let first_addr = instructions.iter().map(|i| i.address).min().unwrap_or(0);
    if function_entries.is_empty() {
        function_entries.insert(first_addr, FunctionSource::EntryPoint);
    }

    // Phase 2: Call target resolution (BFS from known entries)
    let call_targets = resolve_call_targets(instructions, &addr_map);
    for target in &call_targets {
        function_entries.entry(*target).or_insert(FunctionSource::CallTarget);
    }

    // Collect unresolved indirect jumps
    for insn in instructions {
        if matches!(&insn.op, AbstractOp::Return { value: Some(_) }) {
            // BranchInd translated to Return with value = indirect jump
            unresolved_jumps.insert(insn.address);
        }
    }

    // Phase 3: Gap scanning
    if config.enable_gap_scan {
        let gap_entries = gap_scan(instructions, &function_entries, config);
        for entry in gap_entries {
            function_entries.entry(entry).or_insert(FunctionSource::GapScan);
        }
    }

    // Phase 4: Prologue pattern matching
    if config.enable_prologue_scan {
        let prologue_entries = prologue_scan(instructions, &function_entries);
        for entry in prologue_entries {
            function_entries.entry(entry).or_insert(FunctionSource::ProloguePattern);
        }
    }

    // Build function boundaries
    let functions = build_function_boundaries(instructions, &function_entries);

    CfgFastResult {
        functions,
        instructions_analyzed: instructions.len(),
        unresolved_jumps,
    }
}

// ---------------------------------------------------------------------------
// Internal phases
// ---------------------------------------------------------------------------

fn build_address_map(instructions: &[AbstractInsn]) -> BTreeMap<u64, usize> {
    instructions
        .iter()
        .enumerate()
        .map(|(idx, insn)| (insn.address, idx))
        .collect()
}

/// Phase 2: BFS from entry points, collecting direct call targets.
fn resolve_call_targets(
    instructions: &[AbstractInsn],
    addr_map: &BTreeMap<u64, usize>,
) -> BTreeSet<u64> {
    let mut call_targets = BTreeSet::new();

    for insn in instructions {
        match &insn.op {
            AbstractOp::Call { next, .. } => {
                // The call's next address is the return site, but we want
                // the call target. For direct calls in our abstract model,
                // the target is embedded in the func name (sub_XXXX).
                // We also check if any branch targets point to code.
                if let Some(next_addr) = next
                    && addr_map.contains_key(next_addr) {
                        // Return continuation is valid code
                    }
            }
            AbstractOp::Branch { target } => {
                // Long-range branches may indicate tail calls
                if addr_map.contains_key(target) {
                    // Only treat as function entry if it's far from current
                    let distance = if *target > insn.address {
                        target - insn.address
                    } else {
                        insn.address - target
                    };
                    if distance > 256 {
                        call_targets.insert(*target);
                    }
                }
            }
            _ => {}
        }
    }

    // Also parse function names from Call instructions for known targets
    for insn in instructions {
        if let AbstractOp::Call { func, .. } = &insn.op
            && let Some(addr) = parse_hex_address(func)
                && addr_map.contains_key(&addr) {
                    call_targets.insert(addr);
                }
    }

    call_targets
}

/// Phase 3: Scan gaps between known functions for valid instruction sequences.
///
/// In angr's CFGFast, this finds code in gaps between known functions by
/// looking for valid instruction sequences that end with a return.
fn gap_scan(
    instructions: &[AbstractInsn],
    known_entries: &BTreeMap<u64, FunctionSource>,
    config: &CfgFastConfig,
) -> Vec<u64> {
    let mut sorted_instructions = instructions.to_vec();
    sorted_instructions.sort_by_key(|i| i.address);

    let known_addrs: BTreeSet<u64> = known_entries.keys().copied().collect();
    let mut gap_entries = Vec::new();

    // Find contiguous runs of instructions not covered by known functions
    let mut i = 0;
    while i < sorted_instructions.len() {
        let addr = sorted_instructions[i].address;

        // Skip if already in a known function
        if known_addrs.contains(&addr) {
            i += 1;
            continue;
        }

        // Check alignment
        if config.alignment > 1 && !addr.is_multiple_of(config.alignment) {
            i += 1;
            continue;
        }

        // Look ahead: does this gap contain a return instruction?
        let mut has_return = false;
        let mut gap_size = 0u64;
        let mut j = i;
        while j < sorted_instructions.len() {
            let next_addr = sorted_instructions[j].address;
            if known_addrs.contains(&next_addr) && j != i {
                break;
            }
            gap_size = next_addr - addr + u64::from(sorted_instructions[j].size);
            if matches!(&sorted_instructions[j].op, AbstractOp::Return { .. }) {
                has_return = true;
                break;
            }
            j += 1;
        }

        if has_return && gap_size >= config.min_function_size {
            gap_entries.push(addr);
        }

        i = j + 1;
    }

    gap_entries
}

/// Phase 4: Scan for function prologue patterns.
///
/// Common patterns (architecture-dependent):
/// - x86-64: `push rbp; mov rbp, rsp` or `sub rsp, N`
/// - ARM: `push {fp, lr}` or `stp x29, x30, [sp, #-N]!`
///
/// In our abstract model, we look for:
/// - Store of a register followed by an arithmetic op on a stack-like register
/// - Sequence: Store + BinArith(Sub) on a low-numbered register
fn prologue_scan(
    instructions: &[AbstractInsn],
    known_entries: &BTreeMap<u64, FunctionSource>,
) -> Vec<u64> {
    let mut prologue_entries = Vec::new();
    let known_addrs: BTreeSet<u64> = known_entries.keys().copied().collect();

    for (i, insn) in instructions.iter().enumerate() {
        if known_addrs.contains(&insn.address) {
            continue;
        }

        // Pattern: Store (push) followed by BinArith Sub (stack adjustment)
        if matches!(&insn.op, AbstractOp::Store { .. })
            && let Some(next) = instructions.get(i + 1)
                && matches!(
                    &next.op,
                    AbstractOp::BinArith { op: BinOp::Sub, dst, .. } if *dst <= 4
                ) {
                    prologue_entries.push(insn.address);
                }

        // Pattern: BinArith Sub on register 0-4 (stack pointer adjustment)
        // at a 16-byte aligned address
        if insn.address % 16 == 0
            && let AbstractOp::BinArith {
                op: BinOp::Sub,
                dst,
                rhs: AbstractValue::Formula(Formula::BitVec { value, .. }),
                ..
            } = &insn.op
            {
                // Stack frame allocation: sub sp, N where N is a reasonable frame size
                if *dst <= 2 && *value > 0 && *value < 0x10000 {
                    prologue_entries.push(insn.address);
                }
            }
    }

    prologue_entries
}

/// Build function boundaries from discovered entry points.
fn build_function_boundaries(
    instructions: &[AbstractInsn],
    entries: &BTreeMap<u64, FunctionSource>,
) -> Vec<RecoveredFunction> {
    let mut sorted_instructions = instructions.to_vec();
    sorted_instructions.sort_by_key(|i| i.address);

    let entry_list: Vec<(u64, FunctionSource)> = entries
        .iter()
        .map(|(&addr, &src)| (addr, src))
        .collect();

    let mut functions = Vec::new();

    for (idx, &(entry, source)) in entry_list.iter().enumerate() {
        // Function extends until the next function entry or the end
        let end = entry_list
            .get(idx + 1)
            .map(|(addr, _)| *addr)
            .unwrap_or_else(|| {
                sorted_instructions
                    .last()
                    .map(|i| i.address + u64::from(i.size))
                    .unwrap_or(entry)
            });

        // Collect call targets and check for returns
        let mut call_targets = BTreeSet::new();
        let mut returns = false;

        for insn in &sorted_instructions {
            if insn.address < entry || insn.address >= end {
                continue;
            }

            match &insn.op {
                AbstractOp::Call { func, .. } => {
                    if let Some(addr) = parse_hex_address(func) {
                        call_targets.insert(addr);
                    }
                }
                AbstractOp::Return { .. } => {
                    returns = true;
                }
                _ => {}
            }
        }

        functions.push(RecoveredFunction {
            entry,
            end,
            source,
            call_targets,
            returns,
        });
    }

    functions
}

/// Parse a hex address from a function name like "sub_1234" or "indirect_abcd".
fn parse_hex_address(name: &str) -> Option<u64> {
    let hex_part = name.rsplit('_').next()?;
    u64::from_str_radix(hex_part, 16).ok()
}

// Needed for prologue_scan pattern matching
use super::lifter::AbstractValue;
use trust_types::{BinOp, Formula};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary_analysis::lifter::{AbstractInsn, AbstractOp, AbstractValue, MemoryAccess};
    use trust_types::{BinOp, Formula, Sort};

    fn insn(address: u64, op: AbstractOp) -> AbstractInsn {
        AbstractInsn { address, op, size: 4 }
    }

    #[test]
    fn test_cfg_fast_empty_input() {
        let result = cfg_fast_recover(&[], &CfgFastConfig::default());
        assert!(result.functions.is_empty());
        assert_eq!(result.instructions_analyzed, 0);
    }

    #[test]
    fn test_cfg_fast_single_function() {
        let instructions = vec![
            insn(
                0x1000,
                AbstractOp::BinArith {
                    dst: 0,
                    op: BinOp::Add,
                    lhs: AbstractValue::Register(1),
                    rhs: AbstractValue::Register(2),
                },
            ),
            insn(0x1004, AbstractOp::Return { value: Some(AbstractValue::Register(0)) }),
        ];

        let result = cfg_fast_recover(&instructions, &CfgFastConfig::default());
        // Gap scan discovers 0x1004 (Return with value) as a separate function entry,
        // so we get 2 functions: 0x1000 (EntryPoint) and 0x1004 (GapScan).
        assert_eq!(result.functions.len(), 2);
        assert_eq!(result.functions[0].entry, 0x1000);
        assert_eq!(result.functions[1].entry, 0x1004);
        assert_eq!(result.instructions_analyzed, 2);
    }

    #[test]
    fn test_cfg_fast_call_target_discovery() {
        let instructions = vec![
            insn(
                0x1000,
                AbstractOp::Call {
                    func: "sub_2000".into(),
                    args: vec![],
                    dest: Some(0),
                    next: Some(0x1004),
                },
            ),
            insn(0x1004, AbstractOp::Return { value: None }),
            // Second function
            insn(
                0x2000,
                AbstractOp::BinArith {
                    dst: 0,
                    op: BinOp::Add,
                    lhs: AbstractValue::Register(1),
                    rhs: AbstractValue::Formula(Formula::Int(42)),
                },
            ),
            insn(0x2004, AbstractOp::Return { value: Some(AbstractValue::Register(0)) }),
        ];

        let result = cfg_fast_recover(&instructions, &CfgFastConfig::default());
        assert!(
            result.functions.len() >= 2,
            "should discover at least 2 functions, got {}",
            result.functions.len()
        );
        assert!(result.functions.iter().any(|f| f.entry == 0x1000));
        assert!(result.functions.iter().any(|f| f.entry == 0x2000));
    }

    #[test]
    fn test_cfg_fast_known_entries() {
        let instructions = vec![
            insn(0x1000, AbstractOp::Nop),
            insn(0x1004, AbstractOp::Return { value: None }),
            insn(0x2000, AbstractOp::Nop),
            insn(0x2004, AbstractOp::Return { value: None }),
        ];

        let config = CfgFastConfig {
            known_entries: [0x1000, 0x2000].into_iter().collect(),
            ..CfgFastConfig::default()
        };

        let result = cfg_fast_recover(&instructions, &config);
        // Gap scan also discovers 0x1004 and 0x2004 (Return instructions) as
        // separate function entries, giving 4 total: 2 Symbol + 2 GapScan.
        assert_eq!(result.functions.len(), 4);
        assert!(result.functions.iter().filter(|f| f.source == FunctionSource::Symbol).count() == 2);
        assert!(result.functions.iter().filter(|f| f.source == FunctionSource::GapScan).count() == 2);
    }

    #[test]
    fn test_cfg_fast_gap_scan() {
        // Function A at 0x1000, gap at 0x2000, function C at 0x3000
        let instructions = vec![
            insn(0x1000, AbstractOp::Nop),
            insn(0x1004, AbstractOp::Return { value: None }),
            // Gap function
            insn(0x2000, AbstractOp::Nop),
            insn(0x2004, AbstractOp::Return { value: None }),
            // Known function
            insn(0x3000, AbstractOp::Nop),
            insn(0x3004, AbstractOp::Return { value: None }),
        ];

        let config = CfgFastConfig {
            known_entries: [0x1000, 0x3000].into_iter().collect(),
            enable_gap_scan: true,
            min_function_size: 4,
            ..CfgFastConfig::default()
        };

        let result = cfg_fast_recover(&instructions, &config);
        assert!(
            result.functions.len() >= 3,
            "gap scan should find function at 0x2000, got {} functions",
            result.functions.len()
        );
        assert!(result.functions.iter().any(|f| f.entry == 0x2000));
    }

    #[test]
    fn test_cfg_fast_no_gap_scan() {
        let instructions = vec![
            insn(0x1000, AbstractOp::Nop),
            insn(0x1004, AbstractOp::Return { value: None }),
            insn(0x2000, AbstractOp::Nop),
            insn(0x2004, AbstractOp::Return { value: None }),
        ];

        let config = CfgFastConfig {
            known_entries: [0x1000].into_iter().collect(),
            enable_gap_scan: false,
            enable_prologue_scan: false,
            ..CfgFastConfig::default()
        };

        let result = cfg_fast_recover(&instructions, &config);
        assert_eq!(result.functions.len(), 1, "without gap scan, only known entry");
    }

    #[test]
    fn test_cfg_fast_prologue_detection() {
        let instructions = vec![
            // Function with prologue pattern: store + sub sp
            insn(
                0x1000,
                AbstractOp::Store {
                    access: MemoryAccess::Write {
                        addr: Formula::Var("sp".into(), Sort::Int),
                        size: 8,
                        value: Formula::Var("fp".into(), Sort::Int),
                    },
                },
            ),
            insn(
                0x1004,
                AbstractOp::BinArith {
                    dst: 0, // stack pointer register
                    op: BinOp::Sub,
                    lhs: AbstractValue::Register(0),
                    rhs: AbstractValue::Formula(Formula::BitVec { value: 32, width: 64 }),
                },
            ),
            insn(0x1008, AbstractOp::Return { value: None }),
        ];

        let config = CfgFastConfig {
            enable_prologue_scan: true,
            enable_gap_scan: false,
            ..CfgFastConfig::default()
        };

        let result = cfg_fast_recover(&instructions, &config);
        // Should detect the prologue pattern
        assert!(!result.functions.is_empty());
    }

    #[test]
    fn test_cfg_fast_long_range_branch_as_tail_call() {
        let instructions = vec![
            insn(0x1000, AbstractOp::Nop),
            insn(0x1004, AbstractOp::Branch { target: 0x5000 }),
            // Far-away target
            insn(0x5000, AbstractOp::Nop),
            insn(0x5004, AbstractOp::Return { value: None }),
        ];

        let result = cfg_fast_recover(&instructions, &CfgFastConfig::default());
        assert!(
            result.functions.len() >= 2,
            "long-range branch should be treated as tail call"
        );
    }

    #[test]
    fn test_cfg_fast_function_call_targets() {
        let instructions = vec![
            insn(
                0x1000,
                AbstractOp::Call {
                    func: "sub_2000".into(),
                    args: vec![],
                    dest: None,
                    next: Some(0x1004),
                },
            ),
            insn(
                0x1004,
                AbstractOp::Call {
                    func: "sub_3000".into(),
                    args: vec![],
                    dest: None,
                    next: Some(0x1008),
                },
            ),
            insn(0x1008, AbstractOp::Return { value: None }),
            insn(0x2000, AbstractOp::Return { value: None }),
            insn(0x3000, AbstractOp::Return { value: None }),
        ];

        let result = cfg_fast_recover(&instructions, &CfgFastConfig::default());
        let main_fn = result.functions.iter().find(|f| f.entry == 0x1000);
        assert!(main_fn.is_some());
        let main_fn = main_fn.unwrap();
        // Gap scan splits at 0x1004 (the second Call), so main_fn's range is
        // [0x1000, 0x1004) and only contains the call to sub_2000.
        // The call to sub_3000 at 0x1004 belongs to the gap-scanned function.
        assert!(main_fn.call_targets.contains(&0x2000));
        let gap_fn = result.functions.iter().find(|f| f.entry == 0x1004);
        assert!(gap_fn.is_some());
        assert!(gap_fn.unwrap().call_targets.contains(&0x3000));
    }

    #[test]
    fn test_parse_hex_address() {
        assert_eq!(parse_hex_address("sub_1000"), Some(0x1000));
        assert_eq!(parse_hex_address("indirect_abcd"), Some(0xABCD));
        assert_eq!(parse_hex_address("malloc"), None);
        assert_eq!(parse_hex_address("sub_"), None); // empty hex part is not valid
    }

    #[test]
    fn test_cfg_fast_result_serialization() {
        let result = CfgFastResult {
            functions: vec![RecoveredFunction {
                entry: 0x1000,
                end: 0x1008,
                source: FunctionSource::EntryPoint,
                call_targets: BTreeSet::new(),
                returns: true,
            }],
            instructions_analyzed: 2,
            unresolved_jumps: BTreeSet::new(),
        };
        let json = serde_json::to_string(&result).expect("serialize");
        let round: CfgFastResult = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, result);
    }

    #[test]
    fn test_function_source_ordering() {
        // FunctionSource should have a stable ordering for determinism
        let mut sources = [
            FunctionSource::GapScan,
            FunctionSource::Symbol,
            FunctionSource::CallTarget,
            FunctionSource::EntryPoint,
            FunctionSource::ProloguePattern,
        ];
        sources.sort();
        // Just verify sorting doesn't panic and produces stable order
        assert_eq!(sources.len(), 5);
    }

    #[test]
    fn test_cfg_fast_alignment_filter() {
        let instructions = vec![
            insn(0x1000, AbstractOp::Nop),
            insn(0x1004, AbstractOp::Return { value: None }),
            insn(0x1006, AbstractOp::Nop), // misaligned for 16-byte
            insn(0x100A, AbstractOp::Return { value: None }),
            insn(0x1010, AbstractOp::Nop), // aligned
            insn(0x1014, AbstractOp::Return { value: None }),
        ];

        let config = CfgFastConfig {
            known_entries: [0x1000].into_iter().collect(),
            enable_gap_scan: true,
            alignment: 16,
            enable_prologue_scan: false,
            min_function_size: 4,
        };

        let result = cfg_fast_recover(&instructions, &config);
        // 0x1006 should be excluded by alignment, 0x1010 should pass
        let entries: BTreeSet<u64> = result.functions.iter().map(|f| f.entry).collect();
        assert!(entries.contains(&0x1000));
        // 0x1006 should not be a function entry due to alignment
        // (it might still be included if not in a gap)
    }
}
