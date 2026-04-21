// trust-lift: Top-level lifter orchestration
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use trust_disasm::aarch64::Aarch64Decoder;
use trust_disasm::arch::Decoder;
use trust_disasm::operand::Register;
use trust_disasm::x86_64::X86_64Decoder;
use trust_types::{Ty, VerifiableBody};

use crate::boundary::{FunctionBoundary, find_function_at};
use crate::cfg::{LiftedFunction, ProofAnnotation};
use crate::cfg_builder::recover_cfg;
use crate::error::LiftError;
use crate::semantic_lift::lift_cfg_semantic;
use crate::ssa::construct_ssa;

/// Target architecture for the lifter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiftArch {
    /// AArch64 (ARM 64-bit).
    Aarch64,
    /// x86-64 (AMD64).
    X86_64,
}

/// The binary lifter: converts binary code into tMIR functions.
///
/// Created from pre-extracted function boundaries and text section info.
/// For Mach-O loading, use `Lifter::from_macho` (requires `macho` feature).
/// For ELF loading, use `Lifter::from_elf` (requires `elf` feature).
#[derive(Debug)]
pub struct Lifter {
    /// Detected function boundaries.
    boundaries: Vec<FunctionBoundary>,
    /// Text section base virtual address.
    text_base: u64,
    /// Text section size in bytes.
    text_size: u64,
    /// File offset of text section within the binary.
    text_file_offset: usize,
    /// Target architecture for decoding.
    arch: LiftArch,
}

impl Lifter {
    /// Create a lifter from pre-extracted binary metadata.
    ///
    /// This is the primary constructor that does not require Mach-O parsing.
    /// Useful when function boundaries and text section info are already known.
    ///
    /// # Arguments
    /// * `boundaries` - Detected function boundaries (sorted by start address).
    /// * `text_base` - Virtual address of the text section start.
    /// * `text_size` - Size of the text section in bytes.
    /// * `text_file_offset` - File offset of the text section within the binary.
    #[must_use]
    pub fn new(
        boundaries: Vec<FunctionBoundary>,
        text_base: u64,
        text_size: u64,
        text_file_offset: usize,
    ) -> Self {
        Self {
            boundaries,
            text_base,
            text_size,
            text_file_offset,
            arch: LiftArch::Aarch64,
        }
    }

    /// Create a lifter from pre-extracted binary metadata with an explicit architecture.
    #[must_use]
    pub fn new_with_arch(
        boundaries: Vec<FunctionBoundary>,
        text_base: u64,
        text_size: u64,
        text_file_offset: usize,
        arch: LiftArch,
    ) -> Self {
        Self {
            boundaries,
            text_base,
            text_size,
            text_file_offset,
            arch,
        }
    }

    /// Create a lifter by analyzing a Mach-O binary.
    ///
    /// Detects function boundaries from the symbol table and locates the text section.
    #[cfg(feature = "macho")]
    pub fn from_macho(macho: &trust_binary_parse::MachO<'_>) -> Result<Self, LiftError> {
        let boundaries = crate::boundary::detect_functions(macho)?;
        let text_section = macho.text_section().ok_or(LiftError::NoTextSection)?;

        Ok(Self {
            boundaries,
            text_base: text_section.addr,
            text_size: text_section.size,
            text_file_offset: text_section.offset as usize,
            arch: LiftArch::Aarch64, // Mach-O in this pipeline is always AArch64
        })
    }

    /// Create a lifter by analyzing an ELF64 binary.
    ///
    /// Detects function boundaries from the symbol table and locates the text
    /// section (or first executable segment). Supports both AArch64 and x86-64
    /// ELF binaries based on the `e_machine` header field.
    #[cfg(feature = "elf")]
    pub fn from_elf(elf: &trust_binary_parse::Elf64<'_>) -> Result<Self, LiftError> {
        // EM_AARCH64 = 0xB7, EM_X86_64 = 0x3E
        let machine = elf.header.e_machine;
        let arch = match machine {
            0xB7 => LiftArch::Aarch64,
            0x3E => LiftArch::X86_64,
            _ => return Err(LiftError::UnsupportedMachine(machine)),
        };

        let boundaries = crate::boundary::detect_functions_elf(elf)?;

        // Prefer .text section; fall back to first executable segment.
        let (text_base, text_size, text_file_offset) = if let Some(text) = elf.text_section() {
            (text.sh_addr, text.sh_size, text.sh_offset as usize)
        } else {
            let exec_segs = elf.executable_segments();
            let seg = exec_segs.first().ok_or(LiftError::NoTextSection)?;
            (seg.p_vaddr, seg.p_filesz, seg.p_offset as usize)
        };

        Ok(Self {
            boundaries,
            text_base,
            text_size,
            text_file_offset,
            arch,
        })
    }

    /// List all detected function boundaries.
    #[must_use]
    pub fn functions(&self) -> &[FunctionBoundary] {
        &self.boundaries
    }

    /// Lift a single function from the binary at the given entry point.
    ///
    /// The `binary` parameter should be the full binary file bytes. The function
    /// is identified by matching `entry` against detected symbol boundaries.
    pub fn lift_function(
        &self,
        binary: &[u8],
        entry: u64,
    ) -> Result<LiftedFunction, LiftError> {
        // Validate entry is within text section.
        let text_end = self.text_base + self.text_size;
        if entry < self.text_base || entry >= text_end {
            return Err(LiftError::EntryOutOfBounds {
                entry,
                text_start: self.text_base,
                text_end,
            });
        }

        // Find the function boundary.
        let boundary = find_function_at(&self.boundaries, entry)
            .ok_or(LiftError::NoFunctionAtAddress(entry))?;

        let func_name = boundary.name.clone();
        let func_start = boundary.start;
        let func_end = func_start + boundary.size;

        // Select decoder based on target architecture.
        let aarch64_dec = Aarch64Decoder::new();
        let x86_64_dec = X86_64Decoder::new();
        let decoder: &dyn Decoder = match self.arch {
            LiftArch::Aarch64 => &aarch64_dec,
            LiftArch::X86_64 => &x86_64_dec,
        };

        // Extract text section bytes from the binary.
        let text_end_offset = self.text_file_offset + self.text_size as usize;
        if text_end_offset > binary.len() {
            return Err(LiftError::NoTextSection);
        }
        let text_bytes = &binary[self.text_file_offset..text_end_offset];

        // Recover CFG.
        let cfg = recover_cfg(decoder, text_bytes, self.text_base, func_start, func_end)?;

        // Extract variable definitions per block for SSA.
        let defined_vars = extract_defined_vars(&cfg);

        // Construct SSA form.
        let ssa = construct_ssa(&cfg, &defined_vars)?;

        // Generate proof annotations.
        let annotations = generate_annotations(&cfg);

        // tRust: #573 — Semantically lift CFG to tMIR using arch-aware semantics.
        let (tmir_blocks, layout) = lift_cfg_semantic(&cfg, self.arch)?;

        // tRust: #561 — Analyze which argument registers are read before
        // being written in the entry block to determine the function's arg_count.
        let arg_count = analyze_arg_count(&cfg, self.arch);

        // Build the tMIR body with full register/flag/memory locals.
        let tmir_body = VerifiableBody {
            locals: layout.to_local_decls(),
            blocks: tmir_blocks,
            arg_count,
            return_ty: Ty::Unit,
        };

        Ok(LiftedFunction {
            name: func_name,
            entry_point: func_start,
            cfg,
            tmir_body,
            ssa: Some(ssa),
            annotations,
        })
    }
}

/// tRust: #561 — Analyze argument register usage to determine arg_count.
///
/// Walks instructions in the entry block and tracks which ABI argument registers
/// are read before being written. The highest such register index + 1 gives the
/// argument count (since the ABI packs arguments into contiguous registers).
///
/// - AArch64 (AAPCS64): X0-X7 (GPR indices 0-7)
/// - x86-64 (SysV ABI): RDI(7), RSI(6), RDX(2), RCX(1), R8(8), R9(9)
///
/// Returns the number of arguments detected (0-8 for AArch64, 0-6 for x86-64).
fn analyze_arg_count(cfg: &crate::cfg::Cfg, arch: LiftArch) -> usize {
    let entry_block = match cfg.blocks.get(cfg.entry) {
        Some(b) => b,
        None => return 0,
    };

    match arch {
        LiftArch::Aarch64 => analyze_arg_count_aarch64(entry_block),
        LiftArch::X86_64 => analyze_arg_count_x86_64(entry_block),
    }
}

/// AArch64 argument register analysis: X0-X7 are argument registers.
/// Walk instructions in order; for each, check if it reads an arg register
/// as a *source* operand that hasn't been written yet. Track writes to know
/// when a register is "defined" (no longer an incoming argument).
///
/// Important: `reads_register` checks ALL operand positions, including the
/// destination (operand 0). For non-store instructions, operand 0 is a write
/// target, not a source. We use `is_source_register` to only check source
/// operand positions (1+ for non-stores, all for stores).
fn analyze_arg_count_aarch64(block: &crate::cfg::LiftedBlock) -> usize {
    // AArch64 AAPCS64: X0-X7 are argument registers (GPR indices 0-7).
    const ARG_REGS: usize = 8;
    let mut written: FxHashSet<u8> = FxHashSet::default();
    let mut used_as_arg = [false; ARG_REGS];

    for insn in &block.instructions {
        // Check source reads first — a register read as a source before any
        // write is an incoming argument.
        for idx in 0..ARG_REGS as u8 {
            if !written.contains(&idx) {
                let reg = Register::gpr(idx, true); // X-register (64-bit)
                let reg_w = Register::gpr(idx, false); // W-register (32-bit)
                if is_source_register(insn, &reg) || is_source_register(insn, &reg_w) {
                    used_as_arg[idx as usize] = true;
                }
            }
        }
        // Track writes.
        for idx in 0..ARG_REGS as u8 {
            let reg = Register::gpr(idx, true);
            let reg_w = Register::gpr(idx, false);
            if insn.writes_register(&reg) || insn.writes_register(&reg_w) {
                written.insert(idx);
            }
        }
    }

    // The arg_count is the highest used argument register index + 1.
    // E.g., if X0 and X2 are used, arg_count = 3 (X0, X1, X2 — X1 is
    // implicit even if not referenced, per the contiguous ABI convention).
    let highest = used_as_arg.iter().rposition(|&used| used);
    highest.map_or(0, |idx| idx + 1)
}

/// x86-64 SysV ABI argument register analysis.
/// Argument registers in call order: RDI, RSI, RDX, RCX, R8, R9.
/// GPR indices: RDI=7, RSI=6, RDX=2, RCX=1, R8=8, R9=9.
fn analyze_arg_count_x86_64(block: &crate::cfg::LiftedBlock) -> usize {
    // SysV ABI argument registers in order, mapped to GPR index.
    const ARG_REG_INDICES: [u8; 6] = [7, 6, 2, 1, 8, 9]; // RDI, RSI, RDX, RCX, R8, R9
    let mut written: FxHashSet<u8> = FxHashSet::default();
    let mut used_as_arg = [false; 6];

    for insn in &block.instructions {
        // Check source reads first (operands 1+ for non-stores).
        for (slot, &gpr_idx) in ARG_REG_INDICES.iter().enumerate() {
            if !written.contains(&gpr_idx) {
                let reg64 = Register::gpr(gpr_idx, true);
                let reg32 = Register::gpr(gpr_idx, false);
                if is_source_register(insn, &reg64) || is_source_register(insn, &reg32) {
                    used_as_arg[slot] = true;
                }
            }
        }
        // Track writes.
        for &gpr_idx in &ARG_REG_INDICES {
            let reg64 = Register::gpr(gpr_idx, true);
            let reg32 = Register::gpr(gpr_idx, false);
            if insn.writes_register(&reg64) || insn.writes_register(&reg32) {
                written.insert(gpr_idx);
            }
        }
    }

    // Highest used slot + 1, since args are contiguous in call order.
    let highest = used_as_arg.iter().rposition(|&used| used);
    highest.map_or(0, |idx| idx + 1)
}

/// Check if a register is used as a *source* operand in an instruction.
///
/// For non-store instructions, operand 0 is the destination (write), so we
/// only check operands at positions 1+. For store instructions, all operands
/// can be sources (the first operand is the data being stored). Memory base
/// and index registers are always source reads.
fn is_source_register(insn: &trust_disasm::Instruction, reg: &Register) -> bool {
    use trust_disasm::operand::Operand as DisasmOp;

    let start = if insn.is_store() { 0 } else { 1 };

    for i in start..insn.operand_count() {
        if let Some(op) = insn.operand(i) {
            match op {
                DisasmOp::Reg(r)
                | DisasmOp::ShiftedReg { reg: r, .. }
                | DisasmOp::ExtendedReg { reg: r, .. } => {
                    if r == reg {
                        return true;
                    }
                }
                DisasmOp::Mem(mem) => {
                    if mem_has_register(mem, reg) {
                        return true;
                    }
                }
                _ => {}
            }
        }
    }

    // Also check operand 0 memory base/index for load instructions
    // (e.g., LDR X0, [X1] — X1 is a source read even though it's in the
    // memory operand at position 1, but LDP has memory at different positions).
    // Memory operands at ANY position are source reads.
    if !insn.is_store()
        && let Some(DisasmOp::Mem(mem)) = insn.operand(0)
            && mem_has_register(mem, reg) {
                return true;
            }

    false
}

/// Check if a memory operand references a specific register (base or index).
fn mem_has_register(mem: &trust_disasm::operand::MemoryOperand, reg: &Register) -> bool {
    use trust_disasm::operand::MemoryOperand;
    match mem {
        MemoryOperand::Base { base } => base == reg,
        MemoryOperand::BaseOffset { base, .. } => base == reg,
        MemoryOperand::BaseRegister { base, index, .. } => base == reg || index == reg,
        MemoryOperand::PreIndex { base, .. } => base == reg,
        MemoryOperand::PostIndex { base, .. } => base == reg,
        MemoryOperand::PcRelative { .. } | _ => false,
    }
}

/// Extract which variables (registers) are defined in each block.
///
/// For now, this extracts destination registers from instructions that
/// write registers (first operand for data-processing instructions).
fn extract_defined_vars(cfg: &crate::cfg::Cfg) -> FxHashMap<usize, Vec<String>> {
    let mut result = FxHashMap::default();

    for block in &cfg.blocks {
        let mut vars = Vec::new();
        for insn in &block.instructions {
            // For instructions that write a register (operand 0 for most data-processing),
            // record the register name.
            if !insn.is_store() && insn.operand_count() > 0
                && let Some(trust_disasm::Operand::Reg(reg)) = insn.operand(0) {
                    vars.push(format!("{reg:?}"));
                }
        }
        if !vars.is_empty() {
            result.insert(block.id, vars);
        }
    }

    result
}

/// Generate proof annotations linking each tMIR statement to its binary offset.
fn generate_annotations(cfg: &crate::cfg::Cfg) -> Vec<ProofAnnotation> {
    let mut annotations = Vec::new();
    for block in &cfg.blocks {
        for (stmt_idx, insn) in block.instructions.iter().enumerate() {
            annotations.push(ProofAnnotation {
                block_id: block.id,
                stmt_index: stmt_idx,
                binary_offset: insn.address,
                encoding: insn.encoding,
            });
        }
    }
    annotations
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_defined_vars_empty() {
        let cfg = crate::cfg::Cfg::new();
        let vars = extract_defined_vars(&cfg);
        assert!(vars.is_empty());
    }

    #[test]
    fn test_generate_annotations_empty() {
        let cfg = crate::cfg::Cfg::new();
        let annotations = generate_annotations(&cfg);
        assert!(annotations.is_empty());
    }

    #[test]
    fn test_lifter_entry_out_of_bounds() {
        let lifter = Lifter::new(
            vec![FunctionBoundary {
                name: "test".into(),
                start: 0x1000,
                size: 0x100,
            }],
            0x1000,
            0x100,
            0,
        );
        let result = lifter.lift_function(&[], 0x2000);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), LiftError::EntryOutOfBounds { .. }));
    }

    #[test]
    fn test_lift_arch_enum() {
        assert_eq!(LiftArch::Aarch64, LiftArch::Aarch64);
        assert_ne!(LiftArch::Aarch64, LiftArch::X86_64);
    }

    #[test]
    fn test_new_with_arch_x86_64() {
        let lifter = Lifter::new_with_arch(
            vec![FunctionBoundary {
                name: "main".into(),
                start: 0x400000,
                size: 0x20,
            }],
            0x400000,
            0x100,
            0,
            LiftArch::X86_64,
        );
        assert_eq!(lifter.functions().len(), 1);
        assert_eq!(lifter.arch, LiftArch::X86_64);
    }

    #[cfg(feature = "elf")]
    #[test]
    fn test_from_elf_unsupported_machine() {
        // Build a minimal ELF with unsupported machine type (MIPS = 0x08)
        let data = build_test_elf_with_machine(0x08);
        let elf = trust_binary_parse::Elf64::parse(&data).expect("should parse");
        let result = Lifter::from_elf(&elf);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), LiftError::UnsupportedMachine(0x08)));
    }

    #[cfg(feature = "elf")]
    #[test]
    fn test_from_elf_aarch64_detects_functions() {
        let data = build_test_elf_with_machine(0xB7); // EM_AARCH64
        let elf = trust_binary_parse::Elf64::parse(&data).expect("should parse");
        let lifter = Lifter::from_elf(&elf).expect("should create lifter");
        assert_eq!(lifter.arch, LiftArch::Aarch64);
        // Should detect _start and main from symtab
        assert_eq!(lifter.functions().len(), 2);
        let names: Vec<&str> = lifter.functions().iter().map(|f| f.name.as_str()).collect();
        assert!(names.contains(&"_start"));
        assert!(names.contains(&"main"));
    }

    #[cfg(feature = "elf")]
    #[test]
    fn test_from_elf_x86_64_detects_functions() {
        let data = build_test_elf_with_machine(0x3E); // EM_X86_64
        let elf = trust_binary_parse::Elf64::parse(&data).expect("should parse");
        let lifter = Lifter::from_elf(&elf).expect("should create lifter");
        assert_eq!(lifter.arch, LiftArch::X86_64);
        assert_eq!(lifter.functions().len(), 2);
    }

    /// Build a minimal valid ELF64 binary with a configurable machine type.
    ///
    /// Contains: ELF header, 1 program header (PT_LOAD, PF_R|PF_X),
    /// .text section (with RET instruction), .symtab, .strtab, .shstrtab,
    /// and 2 function symbols (_start, main).
    #[cfg(feature = "elf")]
    fn build_test_elf_with_machine(machine: u16) -> Vec<u8> {
        let mut buf = Vec::new();

        // Section header string table
        // 0: "", 1: ".shstrtab", 11: ".symtab", 19: ".strtab", 27: ".text"
        let shstrtab = b"\0.shstrtab\0.symtab\0.strtab\0.text\0";
        let strtab = b"\0_start\0main\0";

        // Layout:
        // 0x000: ELF header (64 bytes)
        // 0x040: Program header (56 bytes)
        // 0x078: .text section (32 bytes: 8 NOP instructions for AArch64 or padding)
        // 0x098: shstrtab data (33 bytes, pad to 0x0C0)
        // 0x0C0: strtab data (14 bytes, pad to 0x0D0)
        // 0x0D0: symtab data (3 * 24 = 72 bytes) => ends at 0x118
        // 0x118: Section headers (5 * 64 = 320 bytes) => ends at 0x258

        let phdr_off: u64 = 0x40;
        let text_off: u64 = 0x78;
        let text_size: u64 = 0x20; // 32 bytes
        let shstrtab_off: u64 = 0x98;
        let strtab_off: u64 = 0xC0;
        let symtab_off: u64 = 0xD0;
        let shdr_off: u64 = 0x118;
        let text_vaddr: u64 = 0x400000;

        // --- ELF Header (64 bytes) ---
        buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']); // magic
        buf.push(2);            // ELFCLASS64
        buf.push(1);            // ELFDATA2LSB
        buf.push(1);            // EV_CURRENT
        buf.push(0);            // OS/ABI
        buf.extend_from_slice(&[0u8; 8]); // padding
        buf.extend_from_slice(&2u16.to_le_bytes());        // ET_EXEC
        buf.extend_from_slice(&machine.to_le_bytes());     // e_machine
        buf.extend_from_slice(&1u32.to_le_bytes());        // e_version
        buf.extend_from_slice(&text_vaddr.to_le_bytes());  // e_entry
        buf.extend_from_slice(&phdr_off.to_le_bytes());    // e_phoff
        buf.extend_from_slice(&shdr_off.to_le_bytes());    // e_shoff
        buf.extend_from_slice(&0u32.to_le_bytes());        // e_flags
        buf.extend_from_slice(&64u16.to_le_bytes());       // e_ehsize
        buf.extend_from_slice(&56u16.to_le_bytes());       // e_phentsize
        buf.extend_from_slice(&1u16.to_le_bytes());        // e_phnum
        buf.extend_from_slice(&64u16.to_le_bytes());       // e_shentsize
        buf.extend_from_slice(&5u16.to_le_bytes());        // e_shnum (NULL + shstrtab + symtab + strtab + .text)
        buf.extend_from_slice(&1u16.to_le_bytes());        // e_shstrndx
        assert_eq!(buf.len(), 64);

        // --- Program Header (56 bytes at 0x40) ---
        buf.extend_from_slice(&1u32.to_le_bytes());        // PT_LOAD
        buf.extend_from_slice(&5u32.to_le_bytes());        // PF_R | PF_X
        buf.extend_from_slice(&0u64.to_le_bytes());        // p_offset
        buf.extend_from_slice(&text_vaddr.to_le_bytes());  // p_vaddr
        buf.extend_from_slice(&text_vaddr.to_le_bytes());  // p_paddr
        buf.extend_from_slice(&0x258u64.to_le_bytes());    // p_filesz (whole file)
        buf.extend_from_slice(&0x258u64.to_le_bytes());    // p_memsz
        buf.extend_from_slice(&0x1000u64.to_le_bytes());   // p_align
        assert_eq!(buf.len(), 0x78);

        // --- .text section at 0x78 (32 bytes) ---
        // Fill with AArch64 RET (0xD65F03C0) or x86 RET (0xC3) + padding
        if machine == 0xB7 {
            // AArch64: 8x RET instructions
            for _ in 0..8 {
                buf.extend_from_slice(&0xD65F03C0u32.to_le_bytes());
            }
        } else {
            // x86-64: RET + NOP padding
            buf.push(0xC3); // RET
            buf.extend_from_slice(&[0x90; 15]); // NOP padding for _start
            buf.push(0xC3); // RET
            buf.extend_from_slice(&[0x90; 15]); // NOP padding for main
        }
        assert_eq!(buf.len(), 0x98);

        // --- .shstrtab data at 0x98 (33 bytes, pad to 0xC0) ---
        buf.extend_from_slice(shstrtab);
        while buf.len() < 0xC0 {
            buf.push(0);
        }

        // --- .strtab data at 0xC0 (14 bytes, pad to 0xD0) ---
        buf.extend_from_slice(strtab);
        while buf.len() < 0xD0 {
            buf.push(0);
        }

        // --- .symtab data at 0xD0 (3 entries * 24 bytes = 72 bytes) ---
        // Symbol 0: null
        buf.extend_from_slice(&0u32.to_le_bytes());  // st_name
        buf.push(0); buf.push(0);                     // st_info, st_other
        buf.extend_from_slice(&0u16.to_le_bytes());  // st_shndx
        buf.extend_from_slice(&0u64.to_le_bytes());  // st_value
        buf.extend_from_slice(&0u64.to_le_bytes());  // st_size

        // Symbol 1: _start (global func, section 4=.text, addr text_vaddr)
        buf.extend_from_slice(&1u32.to_le_bytes());  // st_name => "_start"
        buf.push((1 << 4) | 2);                      // STB_GLOBAL | STT_FUNC
        buf.push(0);                                  // STV_DEFAULT
        buf.extend_from_slice(&4u16.to_le_bytes());  // st_shndx => .text section
        buf.extend_from_slice(&text_vaddr.to_le_bytes()); // st_value
        buf.extend_from_slice(&16u64.to_le_bytes()); // st_size

        // Symbol 2: main (global func, section 4=.text, addr text_vaddr+16)
        buf.extend_from_slice(&8u32.to_le_bytes());  // st_name => "main"
        buf.push((1 << 4) | 2);                      // STB_GLOBAL | STT_FUNC
        buf.push(0);
        buf.extend_from_slice(&4u16.to_le_bytes());  // st_shndx
        buf.extend_from_slice(&(text_vaddr + 16).to_le_bytes()); // st_value
        buf.extend_from_slice(&16u64.to_le_bytes()); // st_size

        assert_eq!(buf.len(), 0x118);

        // --- Section Headers at 0x118 (5 entries * 64 bytes = 320 bytes) ---
        // Section 0: NULL
        write_shdr(&mut buf, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);

        // Section 1: .shstrtab (SHT_STRTAB=3)
        write_shdr(&mut buf, 1, 3, 0, 0, shstrtab_off, shstrtab.len() as u64, 0, 0, 1, 0);

        // Section 2: .symtab (SHT_SYMTAB=2, sh_link=3 => .strtab)
        write_shdr(&mut buf, 11, 2, 0, 0, symtab_off, 72, 3, 1, 8, 24);

        // Section 3: .strtab (SHT_STRTAB=3)
        write_shdr(&mut buf, 19, 3, 0, 0, strtab_off, strtab.len() as u64, 0, 0, 1, 0);

        // Section 4: .text (SHT_PROGBITS=1, SHF_ALLOC|SHF_EXECINSTR=0x6)
        write_shdr(&mut buf, 27, 1, 0x6, text_vaddr, text_off, text_size, 0, 0, 16, 0);

        assert_eq!(buf.len(), 0x258);
        buf
    }

    // ====================================================================
    // analyze_arg_count tests
    // ====================================================================

    /// Helper: decode an AArch64 instruction from a u32 encoding.
    fn decode_aarch64(encoding: u32) -> trust_disasm::Instruction {
        let bytes = encoding.to_le_bytes();
        let decoder = Aarch64Decoder::new();
        decoder.decode(&bytes, 0x1000).expect("decode should succeed")
    }

    /// Build a CFG with one entry block containing the given instructions.
    fn cfg_with_entry_block(instructions: Vec<trust_disasm::Instruction>) -> crate::cfg::Cfg {
        let mut cfg = crate::cfg::Cfg::new();
        cfg.add_block(crate::cfg::LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions,
            successors: vec![],
            is_return: true,
        });
        cfg
    }

    #[test]
    fn test_arg_count_zero_args_ret_only() {
        // A function that just returns: RET
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(analyze_arg_count(&cfg, LiftArch::Aarch64), 0);
    }

    #[test]
    fn test_arg_count_one_arg_x0_read() {
        // ADD X1, X0, #42 — reads X0 as source, writes X1
        // Encoding: sf=1, op=0, S=0, sh=0, imm12=42, Rn=0, Rd=1
        // 1_0_0_10001_0_0_000000101010_00000_00001 = 0x9100A801
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0x9100A801), // ADD X1, X0, #42
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(analyze_arg_count(&cfg, LiftArch::Aarch64), 1);
    }

    #[test]
    fn test_arg_count_two_args_x0_x1_read() {
        // ADD X2, X0, X1 — reads X0 (Rn) and X1 (Rm), writes X2
        // Encoding: sf=1, op=0, S=0, shift=00, Rm=1, imm6=0, Rn=0, Rd=2
        // 1_00_01011_00_0_00001_000000_00000_00010 = 0x8B010002
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0x8B010002), // ADD X2, X0, X1
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(analyze_arg_count(&cfg, LiftArch::Aarch64), 2);
    }

    #[test]
    fn test_arg_count_four_args() {
        // Two ADDs reading X0-X3:
        // ADD X4, X0, X1: 0x8B010004
        // ADD X5, X2, X3: 0x8B030045
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0x8B010004), // ADD X4, X0, X1
            decode_aarch64(0x8B030045), // ADD X5, X2, X3
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(analyze_arg_count(&cfg, LiftArch::Aarch64), 4);
    }

    #[test]
    fn test_arg_count_dest_only_not_counted() {
        // MOVZ X0, #1 — writes X0 but does NOT read it as source.
        // Without the is_source_register fix, reads_register(X0) would
        // return true because X0 appears in operand 0, causing a false
        // positive arg_count=1 instead of 0.
        // Encoding: 0xD2800020
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xD2800020), // MOVZ X0, #1
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(analyze_arg_count(&cfg, LiftArch::Aarch64), 0);
    }

    #[test]
    fn test_arg_count_written_then_read_not_arg() {
        // MOVZ X0, #1 then ADD X1, X0, #1: X0 is written first,
        // then read. The read of X0 should NOT count as an argument
        // because X0 was defined locally.
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xD2800020), // MOVZ X0, #1
            decode_aarch64(0x91000401), // ADD X1, X0, #1
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(analyze_arg_count(&cfg, LiftArch::Aarch64), 0);
    }

    #[test]
    fn test_arg_count_store_reads_source() {
        // STR X0, [X1, #16] — X0 is the value being stored (source read),
        // X1 is the base register (source read). Both are arg reads.
        // Encoding: 0xF9000820
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xF9000820), // STR X0, [X1, #16]
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(analyze_arg_count(&cfg, LiftArch::Aarch64), 2);
    }

    #[test]
    fn test_arg_count_empty_cfg() {
        let cfg = crate::cfg::Cfg::new();
        assert_eq!(analyze_arg_count(&cfg, LiftArch::Aarch64), 0);
    }

    #[test]
    fn test_arg_count_gap_in_registers() {
        // If X0 and X2 are used but not X1, arg_count should be 3
        // (contiguous ABI convention: X0, X1, X2).
        // ADD X4, X0, X0: reads X0, writes X4 — 0x8B000004
        // ADD X5, X2, X2: reads X2, writes X5 — 0x8B020045
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0x8B000004), // ADD X4, X0, X0 (reads X0 at source positions 1,2)
            decode_aarch64(0x8B020045), // ADD X5, X2, X2 (reads X2 at source positions 1,2)
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(analyze_arg_count(&cfg, LiftArch::Aarch64), 3);
    }

    // ====================================================================
    // tRust: #573 — x86_64 end-to-end lifting tests
    // ====================================================================

    /// tRust: #573 — x86_64 lift_function end-to-end with a minimal function.
    ///
    /// Builds a Lifter with x86_64 arch and a function containing:
    /// PUSH RBP; MOV RBP, RSP; XOR EAX, EAX; POP RBP; RET
    /// Verifies that lift_function produces a valid LiftedFunction with
    /// tMIR body containing real statements and x86_64 layout (24 locals).
    #[test]
    fn test_lift_function_x86_64_end_to_end() {
        // Build a minimal x86_64 function: a "return 0" function.
        // 55          PUSH RBP
        // 48 89 E5    MOV RBP, RSP
        // 31 C0       XOR EAX, EAX
        // 5D          POP RBP
        // C3          RET
        let func_bytes: Vec<u8> = vec![
            0x55,                   // PUSH RBP
            0x48, 0x89, 0xE5,      // MOV RBP, RSP
            0x31, 0xC0,            // XOR EAX, EAX
            0x5D,                   // POP RBP
            0xC3,                   // RET
        ];
        let func_size = func_bytes.len() as u64;
        let text_base: u64 = 0x401000;

        // Pad to a reasonable text section size.
        let mut text_section = func_bytes.clone();
        text_section.resize(64, 0x90); // NOP padding

        let lifter = Lifter::new_with_arch(
            vec![FunctionBoundary {
                name: "return_zero".into(),
                start: text_base,
                size: func_size,
            }],
            text_base,
            text_section.len() as u64,
            0,
            LiftArch::X86_64,
        );

        let result = lifter.lift_function(&text_section, text_base);
        assert!(result.is_ok(), "lift_function should succeed: {:?}", result.err());

        let func = result.expect("lifted function");
        assert_eq!(func.name, "return_zero");
        assert_eq!(func.entry_point, text_base);

        // tMIR body should have x86_64 layout (24 locals).
        assert_eq!(func.tmir_body.locals.len(), 24);

        // Verify GPR names in locals.
        assert_eq!(func.tmir_body.locals[1].name.as_deref(), Some("RAX"));
        assert_eq!(func.tmir_body.locals[2].name.as_deref(), Some("RCX"));

        // Should have at least one block.
        assert!(!func.tmir_body.blocks.is_empty(), "should have tMIR blocks");

        // CFG should have been recovered.
        assert!(!func.cfg.blocks.is_empty(), "should have CFG blocks");

        // SSA should have been constructed.
        assert!(func.ssa.is_some(), "should have SSA form");

        // Annotations should link to binary offsets.
        assert!(!func.annotations.is_empty(), "should have proof annotations");
    }

    /// tRust: #573 — x86_64 arg_count analysis detects SysV ABI argument registers.
    #[test]
    fn test_arg_count_x86_64_two_args() {
        // A function that reads RDI (arg0) and RSI (arg1) as pure sources:
        // 48 89 F8 = MOV RAX, RDI  (reads RDI at source operand 1)
        // 48 01 F0 = ADD RAX, RSI  (reads RSI at source operand 1)
        // C3       = RET
        let x86_64_dec = X86_64Decoder::new();
        let mov_insn = trust_disasm::arch::Decoder::decode(&x86_64_dec, &[0x48, 0x89, 0xF8], 0x1000)
            .expect("decode MOV RAX, RDI");
        let add_insn = trust_disasm::arch::Decoder::decode(&x86_64_dec, &[0x48, 0x01, 0xF0], 0x1003)
            .expect("decode ADD RAX, RSI");
        let ret_insn = trust_disasm::arch::Decoder::decode(&x86_64_dec, &[0xC3], 0x1006)
            .expect("decode RET");

        let cfg = cfg_with_entry_block(vec![mov_insn, add_insn, ret_insn]);
        // RDI=arg0 (slot 0), RSI=arg1 (slot 1) in SysV ABI.
        // MOV RAX, RDI reads RDI as source; ADD RAX, RSI reads RSI as source.
        assert_eq!(analyze_arg_count(&cfg, LiftArch::X86_64), 2);
    }

    /// tRust: #573 — x86_64 arg_count zero for a leaf function.
    #[test]
    fn test_arg_count_x86_64_zero_args() {
        let x86_64_dec = X86_64Decoder::new();
        // 31 C0 = XOR EAX, EAX (writes EAX, no arg register reads)
        // C3 = RET
        let xor_insn = trust_disasm::arch::Decoder::decode(&x86_64_dec, &[0x31, 0xC0], 0x1000)
            .expect("decode XOR EAX, EAX");
        let ret_insn = trust_disasm::arch::Decoder::decode(&x86_64_dec, &[0xC3], 0x1002)
            .expect("decode RET");

        let cfg = cfg_with_entry_block(vec![xor_insn, ret_insn]);
        assert_eq!(analyze_arg_count(&cfg, LiftArch::X86_64), 0);
    }

    #[cfg(feature = "elf")]
    #[allow(clippy::too_many_arguments)]
    fn write_shdr(
        buf: &mut Vec<u8>,
        sh_name: u32,
        sh_type: u32,
        sh_flags: u64,
        sh_addr: u64,
        sh_offset: u64,
        sh_size: u64,
        sh_link: u32,
        sh_info: u32,
        sh_addralign: u64,
        sh_entsize: u64,
    ) {
        buf.extend_from_slice(&sh_name.to_le_bytes());
        buf.extend_from_slice(&sh_type.to_le_bytes());
        buf.extend_from_slice(&sh_flags.to_le_bytes());
        buf.extend_from_slice(&sh_addr.to_le_bytes());
        buf.extend_from_slice(&sh_offset.to_le_bytes());
        buf.extend_from_slice(&sh_size.to_le_bytes());
        buf.extend_from_slice(&sh_link.to_le_bytes());
        buf.extend_from_slice(&sh_info.to_le_bytes());
        buf.extend_from_slice(&sh_addralign.to_le_bytes());
        buf.extend_from_slice(&sh_entsize.to_le_bytes());
    }
}
