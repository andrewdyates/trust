// trust-lift: Control flow graph types for lifted binary code
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_disasm::Instruction;

/// A basic block in the lifted CFG, prior to tMIR conversion.
///
/// Each block contains the decoded instructions from the binary and tracks
/// its successor edges for CFG construction.
#[derive(Debug, Clone)]
pub struct LiftedBlock {
    /// Block index (corresponds to its position in the CFG block list).
    pub id: usize,
    /// Start address of the block.
    pub start_addr: u64,
    /// Decoded instructions in this block.
    pub instructions: Vec<Instruction>,
    /// Successor block addresses (for CFG edge construction).
    pub successors: Vec<u64>,
    /// Whether this block ends with a return.
    pub is_return: bool,
}

/// A control flow graph built from recovered basic blocks.
#[derive(Debug, Clone, Default)]
pub struct Cfg {
    /// Basic blocks, indexed by their block ID.
    pub blocks: Vec<LiftedBlock>,
    /// Map from start address to block index.
    // tRust #513: Made pub for downstream crate construction.
    pub addr_to_block: FxHashMap<u64, usize>,
    /// Entry block index.
    pub entry: usize,
}

impl Cfg {
    /// Create a new empty CFG.
    // tRust #513: Made pub so trust-vcgen tests can construct fixtures.
    pub fn new() -> Self {
        Self {
            blocks: Vec::new(),
            addr_to_block: FxHashMap::default(),
            entry: 0,
        }
    }

    /// Add a block and register its address mapping.
    // tRust #513: Made pub so trust-vcgen tests can construct fixtures.
    pub fn add_block(&mut self, block: LiftedBlock) -> usize {
        let idx = self.blocks.len();
        self.addr_to_block.insert(block.start_addr, idx);
        self.blocks.push(block);
        idx
    }

    /// Look up a block index by start address.
    #[must_use]
    pub fn block_index(&self, addr: u64) -> Option<usize> {
        self.addr_to_block.get(&addr).copied()
    }

    /// Number of blocks.
    #[must_use]
    pub fn block_count(&self) -> usize {
        self.blocks.len()
    }
}

/// A fully lifted function ready for verification.
#[derive(Debug, Clone)]
pub struct LiftedFunction {
    /// Function name (from symbol table).
    pub name: String,
    /// Entry point address.
    pub entry_point: u64,
    /// The recovered control flow graph.
    pub cfg: Cfg,
    /// The tMIR representation of the function body.
    pub tmir_body: trust_types::VerifiableBody,
    /// SSA form computed from the CFG (None if SSA construction was skipped).
    pub ssa: Option<crate::ssa::SsaForm>,
    /// Proof annotations linking tMIR statements to binary offsets.
    pub annotations: Vec<ProofAnnotation>,
}

/// Proof annotation linking a tMIR statement back to its binary source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofAnnotation {
    /// tMIR block index.
    pub block_id: usize,
    /// Statement index within the block.
    pub stmt_index: usize,
    /// Original binary offset.
    pub binary_offset: u64,
    /// Original instruction encoding.
    pub encoding: u32,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cfg_add_and_lookup() {
        let mut cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        };
        let idx = cfg.add_block(block);
        assert_eq!(idx, 0);
        assert_eq!(cfg.block_index(0x1000), Some(0));
        assert_eq!(cfg.block_index(0x2000), None);
        assert_eq!(cfg.block_count(), 1);
    }

}
