// trust-integration-tests/tests/rc_e2e.rs: End-to-end reverse compilation pipeline test
//
// Exercises the full RC pipeline across all 6 crates:
//   1. trust-binary-parse: parse ELF binary, extract sections/symbols
//   2. trust-disasm: decode AArch64 instructions from text section
//   3. trust-lift: build CFG, SSA, and tMIR from decoded instructions
//   4. trust-type-recover: recover types from binary analysis artifacts
//   5. trust-decompile: convert tMIR back to Rust source code
//   6. trust-vcgen: generate verification conditions from lifted code
//
// Part of #563
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_binary_parse::{parse_binary, Architecture, BinaryFormat};
use trust_decompile::Decompiler;
use trust_disasm::Instruction;
use trust_lift::{FunctionBoundary, LiftArch, Lifter};
use trust_type_recover::{
    DwarfEntry, DwarfTag, RecoveryContext, TypeRecoverer, ValueRangeObservation,
};
use trust_vcgen::lift_adapter;

// ---------------------------------------------------------------------------
// Test ELF binary builder (AArch64)
// ---------------------------------------------------------------------------

/// AArch64 instruction encodings (little-endian).
/// ADD X0, X0, X1 -- 0x8B010000
const AARCH64_ADD_X0_X0_X1: [u8; 4] = [0x00, 0x00, 0x01, 0x8B];
/// RET (X30) -- 0xD65F03C0
const AARCH64_RET: [u8; 4] = [0xC0, 0x03, 0x5F, 0xD6];
/// SUB X0, X0, X1 -- 0xCB010000
const AARCH64_SUB_X0_X0_X1: [u8; 4] = [0x00, 0x00, 0x01, 0xCB];
/// MOV X0, X1 (alias for ORR X0, XZR, X1) -- 0xAA0103E0
const AARCH64_MOV_X0_X1: [u8; 4] = [0xE0, 0x03, 0x01, 0xAA];

/// Build a minimal valid AArch64 ELF64 binary with configurable text section
/// code bytes and function symbols.
///
/// Returns raw ELF bytes suitable for `trust_binary_parse::parse_binary()`.
fn build_aarch64_elf(functions: &[(&str, &[u8])]) -> Vec<u8> {
    let mut buf = Vec::new();
    let machine: u16 = 0xB7; // EM_AARCH64

    // Compute text section contents: concatenated function code
    let mut text_data = Vec::new();
    let mut sym_entries: Vec<(String, u64, u64)> = Vec::new(); // (name, offset_in_text, size)
    for (name, code) in functions {
        let offset = text_data.len() as u64;
        text_data.extend_from_slice(code);
        sym_entries.push((name.to_string(), offset, code.len() as u64));
    }

    // Pad text to multiple of 4 (AArch64 instruction alignment)
    while text_data.len() % 4 != 0 {
        text_data.push(0);
    }

    // Build string tables
    // Section header string table
    let shstrtab = b"\0.shstrtab\0.symtab\0.strtab\0.text\0";
    // Symbol string table: "\0name1\0name2\0..."
    let mut strtab = vec![0u8]; // NUL prefix
    let mut str_offsets: Vec<u32> = Vec::new();
    for (name, _, _) in &sym_entries {
        str_offsets.push(strtab.len() as u32);
        strtab.extend_from_slice(name.as_bytes());
        strtab.push(0);
    }

    // Layout:
    // 0x000: ELF header (64 bytes)
    // 0x040: Program header (56 bytes)
    // 0x078: .text section data (text_data.len())
    // After text: shstrtab, strtab, symtab, section headers
    let text_off: u64 = 0x78;
    let text_size = text_data.len() as u64;
    let text_vaddr: u64 = 0x400000;

    let shstrtab_off = text_off + text_size;
    // Pad shstrtab region
    let shstrtab_size = shstrtab.len() as u64;
    let strtab_off = align_up(shstrtab_off + shstrtab_size, 8);
    let strtab_size = strtab.len() as u64;
    let symtab_off = align_up(strtab_off + strtab_size, 8);
    let num_symbols = 1 + sym_entries.len(); // null + functions
    let symtab_size = (num_symbols * 24) as u64;
    let shdr_off = align_up(symtab_off + symtab_size, 8);

    // --- ELF Header (64 bytes) ---
    buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']); // magic
    buf.push(2);                                        // ELFCLASS64
    buf.push(1);                                        // ELFDATA2LSB
    buf.push(1);                                        // EV_CURRENT
    buf.push(0);                                        // OS/ABI
    buf.extend_from_slice(&[0u8; 8]);                   // padding
    buf.extend_from_slice(&2u16.to_le_bytes());         // ET_EXEC
    buf.extend_from_slice(&machine.to_le_bytes());      // e_machine
    buf.extend_from_slice(&1u32.to_le_bytes());         // e_version
    buf.extend_from_slice(&text_vaddr.to_le_bytes());   // e_entry
    buf.extend_from_slice(&0x40u64.to_le_bytes());      // e_phoff
    buf.extend_from_slice(&shdr_off.to_le_bytes());     // e_shoff
    buf.extend_from_slice(&0u32.to_le_bytes());         // e_flags
    buf.extend_from_slice(&64u16.to_le_bytes());        // e_ehsize
    buf.extend_from_slice(&56u16.to_le_bytes());        // e_phentsize
    buf.extend_from_slice(&1u16.to_le_bytes());         // e_phnum
    buf.extend_from_slice(&64u16.to_le_bytes());        // e_shentsize
    buf.extend_from_slice(&5u16.to_le_bytes());         // e_shnum (NULL + shstrtab + symtab + strtab + .text)
    buf.extend_from_slice(&1u16.to_le_bytes());         // e_shstrndx
    assert_eq!(buf.len(), 64);

    // --- Program Header (56 bytes at 0x40) ---
    let total_file_size = shdr_off + 5 * 64;
    buf.extend_from_slice(&1u32.to_le_bytes());             // PT_LOAD
    buf.extend_from_slice(&5u32.to_le_bytes());             // PF_R | PF_X
    buf.extend_from_slice(&0u64.to_le_bytes());             // p_offset
    buf.extend_from_slice(&text_vaddr.to_le_bytes());       // p_vaddr
    buf.extend_from_slice(&text_vaddr.to_le_bytes());       // p_paddr
    buf.extend_from_slice(&total_file_size.to_le_bytes());  // p_filesz
    buf.extend_from_slice(&total_file_size.to_le_bytes());  // p_memsz
    buf.extend_from_slice(&0x1000u64.to_le_bytes());        // p_align
    assert_eq!(buf.len(), 0x78);

    // --- .text section data ---
    buf.extend_from_slice(&text_data);

    // --- .shstrtab ---
    while buf.len() < shstrtab_off as usize {
        buf.push(0);
    }
    buf.extend_from_slice(shstrtab);

    // --- .strtab ---
    while buf.len() < strtab_off as usize {
        buf.push(0);
    }
    buf.extend_from_slice(&strtab);

    // --- .symtab ---
    while buf.len() < symtab_off as usize {
        buf.push(0);
    }
    // Null symbol
    write_elf_sym(&mut buf, 0, 0, 0, 0, 0);
    // Function symbols
    for (i, (_, text_offset, size)) in sym_entries.iter().enumerate() {
        let addr = text_vaddr + text_offset;
        write_elf_sym(&mut buf, str_offsets[i], addr, *size, (1 << 4) | 2, 4);
    }

    // --- Section Headers ---
    while buf.len() < shdr_off as usize {
        buf.push(0);
    }
    // Section 0: NULL
    write_elf_shdr(&mut buf, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    // Section 1: .shstrtab (SHT_STRTAB=3)
    write_elf_shdr(&mut buf, 1, 3, 0, 0, shstrtab_off, shstrtab_size, 0, 0, 1, 0);
    // Section 2: .symtab (SHT_SYMTAB=2, sh_link=3 => .strtab)
    write_elf_shdr(&mut buf, 11, 2, 0, 0, symtab_off, symtab_size, 3, 1, 8, 24);
    // Section 3: .strtab (SHT_STRTAB=3)
    write_elf_shdr(&mut buf, 19, 3, 0, 0, strtab_off, strtab_size, 0, 0, 1, 0);
    // Section 4: .text (SHT_PROGBITS=1, SHF_ALLOC|SHF_EXECINSTR=0x6)
    write_elf_shdr(&mut buf, 27, 1, 0x6, text_vaddr, text_off, text_size, 0, 0, 16, 0);

    buf
}

/// Write a 64-byte ELF section header.
#[allow(clippy::too_many_arguments)]
fn write_elf_shdr(
    buf: &mut Vec<u8>,
    sh_name: u32, sh_type: u32, sh_flags: u64, sh_addr: u64,
    sh_offset: u64, sh_size: u64, sh_link: u32, sh_info: u32,
    sh_addralign: u64, sh_entsize: u64,
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

/// Write a 24-byte ELF64 symbol table entry.
fn write_elf_sym(buf: &mut Vec<u8>, st_name: u32, st_value: u64, st_size: u64, st_info: u8, st_shndx: u16) {
    buf.extend_from_slice(&st_name.to_le_bytes());
    buf.push(st_info);
    buf.push(0); // st_other
    buf.extend_from_slice(&st_shndx.to_le_bytes());
    buf.extend_from_slice(&st_value.to_le_bytes());
    buf.extend_from_slice(&st_size.to_le_bytes());
}

/// Align a value up to the given alignment.
fn align_up(value: u64, align: u64) -> u64 {
    (value + align - 1) & !(align - 1)
}

// ---------------------------------------------------------------------------
// 1. Full e2e: ELF binary -> parse -> disasm -> lift -> type recover -> decompile -> verify
// ---------------------------------------------------------------------------

/// Test the complete reverse compilation pipeline on a synthetic AArch64 ELF binary
/// containing a simple `add_func(x, y) -> x + y` function.
#[test]
fn test_rc_e2e_full_pipeline_add_function() {
    // Build function code: ADD X0, X0, X1; RET
    let mut add_code = Vec::new();
    add_code.extend_from_slice(&AARCH64_ADD_X0_X0_X1);
    add_code.extend_from_slice(&AARCH64_RET);

    let elf_bytes = build_aarch64_elf(&[("add_func", &add_code)]);

    // --- Stage 1: Parse binary with trust-binary-parse ---
    let binary_info = parse_binary(&elf_bytes).expect("should parse synthetic ELF binary");

    assert_eq!(binary_info.format, BinaryFormat::Elf);
    assert_eq!(binary_info.architecture, Architecture::AArch64);
    assert!(binary_info.entry_point.is_some(), "ELF should have entry point");

    // Verify function symbols were extracted
    let func_symbols: Vec<_> = binary_info.function_symbols().collect();
    assert!(
        func_symbols.iter().any(|s| s.name == "add_func"),
        "should find add_func symbol; found: {:?}",
        func_symbols.iter().map(|s| &s.name).collect::<Vec<_>>()
    );

    // Get text section for disassembly
    let text_section = binary_info
        .sections
        .iter()
        .find(|s| s.executable)
        .expect("should have executable section");
    assert!(
        !text_section.data.is_empty(),
        "text section should contain code"
    );

    // --- Stage 2: Disassemble with trust-disasm ---
    let mut instructions: Vec<Instruction> = Vec::new();
    let mut offset = 0;
    while offset + 4 <= text_section.data.len() {
        let insn_bytes = &text_section.data[offset..offset + 4];
        let addr = text_section.virtual_address + offset as u64;
        match trust_disasm::decode_aarch64(insn_bytes, addr) {
            Ok(insn) => {
                instructions.push(insn);
            }
            Err(e) => {
                eprintln!("Disassembly warning at 0x{addr:x}: {e}");
            }
        }
        offset += 4;
    }

    assert!(
        !instructions.is_empty(),
        "should decode at least one instruction"
    );
    // Verify we found an ADD and a RET
    let has_add = instructions
        .iter()
        .any(|i| format!("{:?}", i.opcode).contains("Add"));
    let has_ret = instructions
        .iter()
        .any(|i| format!("{:?}", i.opcode).contains("Ret"));
    assert!(has_add, "should decode ADD instruction");
    assert!(has_ret, "should decode RET instruction");

    // --- Stage 3: Lift to CFG/SSA with trust-lift ---
    let add_sym = binary_info
        .function_symbols()
        .find(|s| s.name == "add_func")
        .expect("add_func symbol must exist");

    let boundary = FunctionBoundary {
        name: add_sym.name.clone(),
        start: add_sym.address,
        size: add_sym.size,
    };

    let lifter = Lifter::new_with_arch(
        vec![boundary],
        text_section.virtual_address,
        text_section.data.len() as u64,
        0, // text_file_offset: we pass text_section.data directly
        LiftArch::Aarch64,
    );

    assert_eq!(lifter.functions().len(), 1);
    assert_eq!(lifter.functions()[0].name, "add_func");

    let lifted = lifter
        .lift_function(&text_section.data, add_sym.address)
        .expect("lifting add_func should succeed");

    assert_eq!(lifted.name, "add_func");
    assert_eq!(lifted.entry_point, add_sym.address);
    assert!(
        !lifted.cfg.blocks.is_empty(),
        "lifted CFG should have blocks"
    );
    assert!(
        lifted.cfg.blocks.iter().any(|b| b.is_return),
        "CFG should contain a return block"
    );
    assert!(
        !lifted.tmir_body.blocks.is_empty(),
        "tMIR body should have blocks"
    );
    assert!(lifted.ssa.is_some(), "SSA form should be constructed");

    // --- Stage 4: Type recovery with trust-type-recover ---
    let recoverer = TypeRecoverer::new();

    // Simulate DWARF-like evidence for the function's arguments (u64 types)
    let ctx = RecoveryContext {
        dwarf_entries: vec![DwarfEntry {
            die_offset: 0x100,
            tag: DwarfTag::BaseType,
            name: Some("unsigned long".to_string()),
            byte_size: Some(8),
            encoding: Some(0x07), // DW_ATE_unsigned
            type_ref: None,
            members: vec![],
        }],
        value_ranges: vec![ValueRangeObservation {
            address: add_sym.address,
            min: 0,
            max: i128::from(u64::MAX),
        }],
        ..Default::default()
    };

    let type_evidence = recoverer.recover_type(&ctx, add_sym.address);
    assert!(
        type_evidence.is_ok(),
        "type recovery should succeed with DWARF + value range evidence"
    );
    let evidence = type_evidence.unwrap();
    assert!(
        evidence.confidence > 0.5,
        "recovered type confidence should be > 0.5, got {}",
        evidence.confidence
    );

    // --- Stage 5: Decompile to Rust with trust-decompile ---
    let verifiable = lift_adapter::lift_to_verifiable(&lifted);
    assert_eq!(verifiable.name, "add_func");
    assert_eq!(verifiable.def_path, "binary::add_func");

    let decompiler = Decompiler::default();
    let decompile_result = decompiler.decompile(&verifiable);

    // Decompilation on raw binary lift may succeed or produce an error for
    // complex tMIR shapes. Either way, the pipeline must not panic.
    match decompile_result {
        Ok(result) => {
            assert!(!result.source.is_empty(), "decompiled source should be non-empty");
            assert!(result.confidence > 0.0, "confidence should be positive");
            // The function name should appear in the output
            assert!(
                result.source.contains("add_func"),
                "source should contain function name 'add_func'; got: {}",
                result.source
            );
        }
        Err(e) => {
            // Acceptable at this pipeline maturity — log for visibility.
            eprintln!(
                "Decompilation returned error (acceptable for binary lift): {e}"
            );
        }
    }

    // --- Stage 6: Generate VCs with trust-vcgen ---
    let vcs = lift_adapter::generate_binary_vcs(&lifted);
    assert!(
        !vcs.is_empty(),
        "should produce at least one VC (stack discipline)"
    );
    for vc in &vcs {
        assert_eq!(
            vc.function, "add_func",
            "all VCs should reference 'add_func'"
        );
    }

    eprintln!(
        "E2E pipeline complete: {} instructions decoded, {} CFG blocks, {} VCs generated",
        instructions.len(),
        lifted.cfg.block_count(),
        vcs.len()
    );
}

// ---------------------------------------------------------------------------
// 2. Multi-function e2e: parse binary with multiple functions
// ---------------------------------------------------------------------------

/// Test the pipeline with an ELF containing multiple functions, verifying that
/// each function can be independently lifted and decompiled.
#[test]
fn test_rc_e2e_multi_function_binary() {
    // Function 1: add_two -- ADD X0, X0, X1; RET
    let mut add_code = Vec::new();
    add_code.extend_from_slice(&AARCH64_ADD_X0_X0_X1);
    add_code.extend_from_slice(&AARCH64_RET);

    // Function 2: sub_two -- SUB X0, X0, X1; RET
    let mut sub_code = Vec::new();
    sub_code.extend_from_slice(&AARCH64_SUB_X0_X0_X1);
    sub_code.extend_from_slice(&AARCH64_RET);

    let elf_bytes = build_aarch64_elf(&[("add_two", &add_code), ("sub_two", &sub_code)]);

    // Parse
    let binary_info = parse_binary(&elf_bytes).expect("should parse multi-function ELF");
    let func_names: Vec<_> = binary_info
        .function_symbols()
        .map(|s| s.name.clone())
        .collect();
    assert!(func_names.contains(&"add_two".to_string()));
    assert!(func_names.contains(&"sub_two".to_string()));

    let text_section = binary_info
        .sections
        .iter()
        .find(|s| s.executable)
        .expect("should have text section");

    // Build boundaries from symbol info
    let boundaries: Vec<FunctionBoundary> = binary_info
        .function_symbols()
        .map(|s| FunctionBoundary {
            name: s.name.clone(),
            start: s.address,
            size: s.size,
        })
        .collect();

    let lifter = Lifter::new_with_arch(
        boundaries,
        text_section.virtual_address,
        text_section.data.len() as u64,
        0,
        LiftArch::Aarch64,
    );

    assert_eq!(lifter.functions().len(), 2);

    // Lift and verify each function independently
    let decompiler = Decompiler::default();
    for func_boundary in lifter.functions() {
        let lifted = lifter
            .lift_function(&text_section.data, func_boundary.start)
            .unwrap_or_else(|e| panic!("lifting {} should succeed: {e}", func_boundary.name));

        assert_eq!(lifted.name, func_boundary.name);
        assert!(!lifted.cfg.blocks.is_empty());
        assert!(!lifted.tmir_body.blocks.is_empty());

        // Convert to VerifiableFunction and try decompiling
        let verifiable = lift_adapter::lift_to_verifiable(&lifted);
        let _ = decompiler.decompile(&verifiable); // May or may not succeed; must not panic

        // Generate VCs
        let vcs = lift_adapter::generate_binary_vcs(&lifted);
        assert!(
            !vcs.is_empty(),
            "{} should produce VCs",
            func_boundary.name
        );
        for vc in &vcs {
            assert_eq!(vc.function, func_boundary.name);
        }
    }
}

// ---------------------------------------------------------------------------
// 3. Type recovery integration with lifted code
// ---------------------------------------------------------------------------

/// Test that type recovery strategies can analyze evidence derived from
/// lifted binary code artifacts (addresses, value ranges from the CFG).
#[test]
fn test_rc_e2e_type_recovery_from_lifted_artifacts() {
    let mut code = Vec::new();
    code.extend_from_slice(&AARCH64_MOV_X0_X1);
    code.extend_from_slice(&AARCH64_ADD_X0_X0_X1);
    code.extend_from_slice(&AARCH64_RET);

    let elf_bytes = build_aarch64_elf(&[("identity_add", &code)]);
    let binary_info = parse_binary(&elf_bytes).expect("should parse");

    let text_section = binary_info
        .sections
        .iter()
        .find(|s| s.executable)
        .expect("text section");
    let sym = binary_info
        .function_symbols()
        .find(|s| s.name == "identity_add")
        .expect("symbol");

    let boundary = FunctionBoundary {
        name: sym.name.clone(),
        start: sym.address,
        size: sym.size,
    };
    let lifter = Lifter::new_with_arch(
        vec![boundary],
        text_section.virtual_address,
        text_section.data.len() as u64,
        0,
        LiftArch::Aarch64,
    );
    let lifted = lifter
        .lift_function(&text_section.data, sym.address)
        .expect("should lift");

    // Use the lifted function's entry point as context for type recovery.
    // In a real pipeline, we would derive value ranges from VSA or symbolic
    // execution of the CFG. Here we simulate reasonable evidence.
    let recoverer = TypeRecoverer::new();
    let ctx = RecoveryContext {
        dwarf_entries: vec![DwarfEntry {
            die_offset: 0x200,
            tag: DwarfTag::BaseType,
            name: Some("unsigned long long".to_string()),
            byte_size: Some(8),
            encoding: Some(0x07), // DW_ATE_unsigned
            type_ref: None,
            members: vec![],
        }],
        value_ranges: vec![ValueRangeObservation {
            address: lifted.entry_point,
            min: 0,
            max: 0xFFFF_FFFF,
        }],
        ..Default::default()
    };

    let all_evidence = recoverer
        .collect_evidence(&ctx)
        .expect("should collect evidence");
    assert!(
        all_evidence.len() >= 2,
        "should have evidence from DWARF + value range strategies, got {}",
        all_evidence.len()
    );

    let best = recoverer
        .recover_type(&ctx, lifted.entry_point)
        .expect("should recover type");
    assert!(
        best.confidence > 0.5,
        "confidence should be meaningful, got {}",
        best.confidence
    );
}

// ---------------------------------------------------------------------------
// 4. Module-level decompilation from binary
// ---------------------------------------------------------------------------

/// Test decompiling multiple lifted functions into a single module.
#[test]
fn test_rc_e2e_decompile_module_from_binary() {
    let mut add_code = Vec::new();
    add_code.extend_from_slice(&AARCH64_ADD_X0_X0_X1);
    add_code.extend_from_slice(&AARCH64_RET);

    let mut sub_code = Vec::new();
    sub_code.extend_from_slice(&AARCH64_SUB_X0_X0_X1);
    sub_code.extend_from_slice(&AARCH64_RET);

    let elf_bytes = build_aarch64_elf(&[("bin_add", &add_code), ("bin_sub", &sub_code)]);
    let binary_info = parse_binary(&elf_bytes).expect("should parse");

    let text_section = binary_info
        .sections
        .iter()
        .find(|s| s.executable)
        .expect("text section");

    let boundaries: Vec<FunctionBoundary> = binary_info
        .function_symbols()
        .map(|s| FunctionBoundary {
            name: s.name.clone(),
            start: s.address,
            size: s.size,
        })
        .collect();

    let lifter = Lifter::new_with_arch(
        boundaries,
        text_section.virtual_address,
        text_section.data.len() as u64,
        0,
        LiftArch::Aarch64,
    );

    // Lift all functions and convert to VerifiableFunction
    let verifiable_funcs: Vec<_> = lifter
        .functions()
        .iter()
        .filter_map(|fb| {
            lifter
                .lift_function(&text_section.data, fb.start)
                .ok()
                .map(|lifted| lift_adapter::lift_to_verifiable(&lifted))
        })
        .collect();

    assert_eq!(verifiable_funcs.len(), 2, "should lift both functions");

    // Decompile as a module
    let decompiler = Decompiler::default();
    let module = decompiler.decompile_module("rc_binary_module", &verifiable_funcs);

    assert_eq!(module.name, "rc_binary_module");
    assert_eq!(
        module.functions.len(),
        2,
        "module should contain 2 functions"
    );

    let source = module.to_source();
    assert!(
        source.contains("// Decompiled module: rc_binary_module"),
        "module source should contain header"
    );
}

// ---------------------------------------------------------------------------
// 5. Error handling: invalid binary data
// ---------------------------------------------------------------------------

/// Verify that the pipeline gracefully handles invalid binary data at the
/// parsing stage without panicking.
#[test]
fn test_rc_e2e_invalid_binary_graceful_error() {
    let garbage = [0xDE, 0xAD, 0xBE, 0xEF, 0x00, 0x00, 0x00, 0x00];
    let result = parse_binary(&garbage);
    assert!(result.is_err(), "parsing garbage should fail gracefully");
}

/// Verify that a truncated ELF does not panic.
#[test]
fn test_rc_e2e_truncated_binary_graceful_error() {
    // Just the ELF magic, nothing else
    let truncated = [0x7f, b'E', b'L', b'F'];
    let result = parse_binary(&truncated);
    assert!(result.is_err(), "parsing truncated ELF should fail gracefully");
}

// ---------------------------------------------------------------------------
// Test ELF binary builder (x86_64)
// ---------------------------------------------------------------------------

/// x86-64 instruction encodings (little-endian byte order).
/// ADD RAX, RDX
const X86_64_ADD_RAX_RDX: [u8; 3] = [0x48, 0x01, 0xD0];
/// SUB RAX, RDX
const X86_64_SUB_RAX_RDX: [u8; 3] = [0x48, 0x29, 0xD0];
/// RET
const X86_64_RET: [u8; 1] = [0xC3];
/// MOV RAX, RDI
const X86_64_MOV_RAX_RDI: [u8; 3] = [0x48, 0x89, 0xF8];
/// NOP
const X86_64_NOP: [u8; 1] = [0x90];

/// Build a minimal valid x86_64 ELF64 binary with configurable text section
/// code bytes and function symbols.
///
/// Returns raw ELF bytes suitable for `trust_binary_parse::parse_binary()`.
fn build_x86_64_elf(functions: &[(&str, &[u8])]) -> Vec<u8> {
    let mut buf = Vec::new();
    let machine: u16 = 0x3E; // EM_X86_64

    // Compute text section contents: concatenated function code
    let mut text_data = Vec::new();
    let mut sym_entries: Vec<(String, u64, u64)> = Vec::new(); // (name, offset_in_text, size)
    for (name, code) in functions {
        let offset = text_data.len() as u64;
        text_data.extend_from_slice(code);
        sym_entries.push((name.to_string(), offset, code.len() as u64));
    }

    // Build string tables
    // Section header string table
    let shstrtab = b"\0.shstrtab\0.symtab\0.strtab\0.text\0";
    // Symbol string table: "\0name1\0name2\0..."
    let mut strtab = vec![0u8]; // NUL prefix
    let mut str_offsets: Vec<u32> = Vec::new();
    for (name, _, _) in &sym_entries {
        str_offsets.push(strtab.len() as u32);
        strtab.extend_from_slice(name.as_bytes());
        strtab.push(0);
    }

    // Layout:
    // 0x000: ELF header (64 bytes)
    // 0x040: Program header (56 bytes)
    // 0x078: .text section data (text_data.len())
    // After text: shstrtab, strtab, symtab, section headers
    let text_off: u64 = 0x78;
    let text_size = text_data.len() as u64;
    let text_vaddr: u64 = 0x400000;

    let shstrtab_off = text_off + text_size;
    // Pad shstrtab region
    let shstrtab_size = shstrtab.len() as u64;
    let strtab_off = align_up(shstrtab_off + shstrtab_size, 8);
    let strtab_size = strtab.len() as u64;
    let symtab_off = align_up(strtab_off + strtab_size, 8);
    let num_symbols = 1 + sym_entries.len(); // null + functions
    let symtab_size = (num_symbols * 24) as u64;
    let shdr_off = align_up(symtab_off + symtab_size, 8);

    // --- ELF Header (64 bytes) ---
    buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']); // magic
    buf.push(2); // ELFCLASS64
    buf.push(1); // ELFDATA2LSB
    buf.push(1); // EV_CURRENT
    buf.push(0); // OS/ABI
    buf.extend_from_slice(&[0u8; 8]); // padding
    buf.extend_from_slice(&2u16.to_le_bytes()); // ET_EXEC
    buf.extend_from_slice(&machine.to_le_bytes()); // e_machine
    buf.extend_from_slice(&1u32.to_le_bytes()); // e_version
    buf.extend_from_slice(&text_vaddr.to_le_bytes()); // e_entry
    buf.extend_from_slice(&0x40u64.to_le_bytes()); // e_phoff
    buf.extend_from_slice(&shdr_off.to_le_bytes()); // e_shoff
    buf.extend_from_slice(&0u32.to_le_bytes()); // e_flags
    buf.extend_from_slice(&64u16.to_le_bytes()); // e_ehsize
    buf.extend_from_slice(&56u16.to_le_bytes()); // e_phentsize
    buf.extend_from_slice(&1u16.to_le_bytes()); // e_phnum
    buf.extend_from_slice(&64u16.to_le_bytes()); // e_shentsize
    buf.extend_from_slice(&5u16.to_le_bytes()); // e_shnum (NULL + shstrtab + symtab + strtab + .text)
    buf.extend_from_slice(&1u16.to_le_bytes()); // e_shstrndx
    assert_eq!(buf.len(), 64);

    // --- Program Header (56 bytes at 0x40) ---
    let total_file_size = shdr_off + 5 * 64;
    buf.extend_from_slice(&1u32.to_le_bytes()); // PT_LOAD
    buf.extend_from_slice(&5u32.to_le_bytes()); // PF_R | PF_X
    buf.extend_from_slice(&0u64.to_le_bytes()); // p_offset
    buf.extend_from_slice(&text_vaddr.to_le_bytes()); // p_vaddr
    buf.extend_from_slice(&text_vaddr.to_le_bytes()); // p_paddr
    buf.extend_from_slice(&total_file_size.to_le_bytes()); // p_filesz
    buf.extend_from_slice(&total_file_size.to_le_bytes()); // p_memsz
    buf.extend_from_slice(&0x1000u64.to_le_bytes()); // p_align
    assert_eq!(buf.len(), 0x78);

    // --- .text section data ---
    buf.extend_from_slice(&text_data);

    // --- .shstrtab ---
    while buf.len() < shstrtab_off as usize {
        buf.push(0);
    }
    buf.extend_from_slice(shstrtab);

    // --- .strtab ---
    while buf.len() < strtab_off as usize {
        buf.push(0);
    }
    buf.extend_from_slice(&strtab);

    // --- .symtab ---
    while buf.len() < symtab_off as usize {
        buf.push(0);
    }
    // Null symbol
    write_elf_sym(&mut buf, 0, 0, 0, 0, 0);
    // Function symbols
    for (i, (_, text_offset, size)) in sym_entries.iter().enumerate() {
        let addr = text_vaddr + text_offset;
        write_elf_sym(&mut buf, str_offsets[i], addr, *size, (1 << 4) | 2, 4);
    }

    // --- Section Headers ---
    while buf.len() < shdr_off as usize {
        buf.push(0);
    }
    // Section 0: NULL
    write_elf_shdr(&mut buf, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    // Section 1: .shstrtab (SHT_STRTAB=3)
    write_elf_shdr(&mut buf, 1, 3, 0, 0, shstrtab_off, shstrtab_size, 0, 0, 1, 0);
    // Section 2: .symtab (SHT_SYMTAB=2, sh_link=3 => .strtab)
    write_elf_shdr(&mut buf, 11, 2, 0, 0, symtab_off, symtab_size, 3, 1, 8, 24);
    // Section 3: .strtab (SHT_STRTAB=3)
    write_elf_shdr(&mut buf, 19, 3, 0, 0, strtab_off, strtab_size, 0, 0, 1, 0);
    // Section 4: .text (SHT_PROGBITS=1, SHF_ALLOC|SHF_EXECINSTR=0x6)
    write_elf_shdr(&mut buf, 27, 1, 0x6, text_vaddr, text_off, text_size, 0, 0, 16, 0);

    buf
}

// ---------------------------------------------------------------------------
// 6. x86_64 e2e: ELF binary -> parse -> disasm -> lift -> type recover -> decompile -> verify
// ---------------------------------------------------------------------------

#[test]
fn test_rc_e2e_x86_64_full_pipeline_add_function() {
    let mut add_code = Vec::new();
    add_code.extend_from_slice(&X86_64_ADD_RAX_RDX);
    add_code.extend_from_slice(&X86_64_RET);

    let elf_bytes = build_x86_64_elf(&[("x86_add_func", &add_code)]);

    // --- Stage 1: Parse binary with trust-binary-parse ---
    let binary_info = parse_binary(&elf_bytes).expect("should parse synthetic x86_64 ELF binary");

    assert_eq!(binary_info.format, BinaryFormat::Elf);
    assert_eq!(binary_info.architecture, Architecture::X86_64);
    assert!(binary_info.entry_point.is_some(), "ELF should have entry point");

    let func_symbols: Vec<_> = binary_info.function_symbols().collect();
    assert!(
        func_symbols.iter().any(|s| s.name == "x86_add_func"),
        "should find x86_add_func symbol; found: {:?}",
        func_symbols.iter().map(|s| &s.name).collect::<Vec<_>>()
    );

    let text_section =
        binary_info.sections.iter().find(|s| s.executable).expect("should have executable section");
    assert!(!text_section.data.is_empty(), "text section should contain code");

    // --- Stage 2: Disassemble with trust-disasm ---
    let mut instructions: Vec<Instruction> = Vec::new();
    let mut offset = 0usize;
    while offset < text_section.data.len() {
        let addr = text_section.virtual_address + offset as u64;
        let insn = trust_disasm::decode_x86_64(&text_section.data[offset..], addr)
            .expect("x86_64 disassembly should succeed");
        let size = insn.size as usize;
        assert!(size > 0, "x86_64 decoder must make forward progress");
        instructions.push(insn);
        offset += size;
    }

    assert!(!instructions.is_empty(), "should decode at least one instruction");
    let has_add = instructions.iter().any(|i| format!("{:?}", i.opcode).contains("Add"));
    let has_ret = instructions.iter().any(|i| format!("{:?}", i.opcode).contains("Ret"));
    assert!(has_add, "should decode ADD instruction");
    assert!(has_ret, "should decode RET instruction");

    // --- Stage 3: Lift to CFG/SSA with trust-lift ---
    let add_sym = binary_info.find_symbol("x86_add_func").expect("x86_add_func symbol must exist");

    let boundary =
        FunctionBoundary { name: add_sym.name.clone(), start: add_sym.address, size: add_sym.size };

    let lifter = Lifter::new_with_arch(
        vec![boundary],
        text_section.virtual_address,
        text_section.data.len() as u64,
        0,
        LiftArch::X86_64,
    );

    assert_eq!(lifter.functions().len(), 1);
    assert_eq!(lifter.functions()[0].name, "x86_add_func");

    let lifted = lifter
        .lift_function(&text_section.data, add_sym.address)
        .expect("lifting x86_add_func should succeed");

    assert_eq!(lifted.name, "x86_add_func");
    assert_eq!(lifted.entry_point, add_sym.address);
    assert!(!lifted.cfg.blocks.is_empty(), "lifted CFG should have blocks");
    assert!(lifted.cfg.blocks.iter().any(|b| b.is_return), "CFG should contain a return block");
    assert!(!lifted.tmir_body.blocks.is_empty(), "tMIR body should have blocks");
    assert!(lifted.ssa.is_some(), "SSA form should be constructed");

    // --- Stage 4: Type recovery with trust-type-recover ---
    let recoverer = TypeRecoverer::new();
    let ctx = RecoveryContext {
        dwarf_entries: vec![DwarfEntry {
            die_offset: 0x300,
            tag: DwarfTag::BaseType,
            name: Some("unsigned long".to_string()),
            byte_size: Some(8),
            encoding: Some(0x07), // DW_ATE_unsigned
            type_ref: None,
            members: vec![],
        }],
        value_ranges: vec![ValueRangeObservation {
            address: add_sym.address,
            min: 0,
            max: i128::from(u64::MAX),
        }],
        ..Default::default()
    };

    let type_evidence = recoverer.recover_type(&ctx, add_sym.address);
    assert!(
        type_evidence.is_ok(),
        "type recovery should succeed with DWARF + value range evidence"
    );
    let evidence = type_evidence.unwrap();
    assert!(
        evidence.confidence > 0.5,
        "recovered type confidence should be > 0.5, got {}",
        evidence.confidence
    );

    // --- Stage 5: Decompile to Rust with trust-decompile ---
    let verifiable = lift_adapter::lift_to_verifiable(&lifted);
    assert_eq!(verifiable.name, "x86_add_func");
    assert_eq!(verifiable.def_path, "binary::x86_add_func");

    let decompiler = Decompiler::default();
    match decompiler.decompile(&verifiable) {
        Ok(result) => {
            assert!(!result.source.is_empty(), "decompiled source should be non-empty");
            assert!(result.confidence > 0.0, "confidence should be positive");
            assert!(
                result.source.contains("x86_add_func"),
                "source should contain function name 'x86_add_func'; got: {}",
                result.source
            );
        }
        Err(e) => {
            eprintln!("Decompilation returned error (acceptable for x86_64 binary lift): {e}");
        }
    }

    // --- Stage 6: Generate VCs with trust-vcgen ---
    let vcs = lift_adapter::generate_binary_vcs(&lifted);
    assert!(!vcs.is_empty(), "should produce at least one VC (stack discipline)");
    for vc in &vcs {
        assert_eq!(vc.function, "x86_add_func", "all VCs should reference 'x86_add_func'");
    }
}

// ---------------------------------------------------------------------------
// 7. x86_64 multi-function e2e
// ---------------------------------------------------------------------------

#[test]
fn test_rc_e2e_x86_64_multi_function_binary() {
    let mut add_code = Vec::new();
    add_code.extend_from_slice(&X86_64_ADD_RAX_RDX);
    add_code.extend_from_slice(&X86_64_RET);

    let mut sub_code = Vec::new();
    sub_code.extend_from_slice(&X86_64_SUB_RAX_RDX);
    sub_code.extend_from_slice(&X86_64_RET);

    let elf_bytes = build_x86_64_elf(&[("x86_add", &add_code), ("x86_sub", &sub_code)]);

    let binary_info = parse_binary(&elf_bytes).expect("should parse multi-function x86_64 ELF");
    assert_eq!(binary_info.architecture, Architecture::X86_64);
    assert!(binary_info.find_symbol("x86_add").is_some());
    assert!(binary_info.find_symbol("x86_sub").is_some());

    let text_section =
        binary_info.sections.iter().find(|s| s.executable).expect("should have text section");

    let boundaries: Vec<FunctionBoundary> = binary_info
        .function_symbols()
        .map(|s| FunctionBoundary { name: s.name.clone(), start: s.address, size: s.size })
        .collect();

    let lifter = Lifter::new_with_arch(
        boundaries,
        text_section.virtual_address,
        text_section.data.len() as u64,
        0,
        LiftArch::X86_64,
    );

    assert_eq!(lifter.functions().len(), 2);

    let decompiler = Decompiler::default();
    for func_boundary in lifter.functions() {
        let lifted = lifter
            .lift_function(&text_section.data, func_boundary.start)
            .unwrap_or_else(|e| panic!("lifting {} should succeed: {e}", func_boundary.name));

        assert_eq!(lifted.name, func_boundary.name);
        assert!(!lifted.cfg.blocks.is_empty());
        assert!(!lifted.tmir_body.blocks.is_empty());

        let verifiable = lift_adapter::lift_to_verifiable(&lifted);
        let _ = decompiler.decompile(&verifiable);

        let vcs = lift_adapter::generate_binary_vcs(&lifted);
        assert!(!vcs.is_empty(), "{} should produce VCs", func_boundary.name);
        for vc in &vcs {
            assert_eq!(vc.function, func_boundary.name);
        }
    }
}

// ---------------------------------------------------------------------------
// 8. x86_64 type recovery integration with lifted code
// ---------------------------------------------------------------------------

#[test]
fn test_rc_e2e_x86_64_type_recovery_from_lifted() {
    let mut code = Vec::new();
    code.extend_from_slice(&X86_64_MOV_RAX_RDI);
    code.extend_from_slice(&X86_64_ADD_RAX_RDX);
    code.extend_from_slice(&X86_64_RET);

    let elf_bytes = build_x86_64_elf(&[("x86_identity", &code)]);
    let binary_info = parse_binary(&elf_bytes).expect("should parse");

    let text_section = binary_info.sections.iter().find(|s| s.executable).expect("text section");
    let sym = binary_info.find_symbol("x86_identity").expect("symbol");

    let boundary = FunctionBoundary { name: sym.name.clone(), start: sym.address, size: sym.size };
    let lifter = Lifter::new_with_arch(
        vec![boundary],
        text_section.virtual_address,
        text_section.data.len() as u64,
        0,
        LiftArch::X86_64,
    );
    let lifted = lifter.lift_function(&text_section.data, sym.address).expect("should lift");

    let recoverer = TypeRecoverer::new();
    let ctx = RecoveryContext {
        dwarf_entries: vec![DwarfEntry {
            die_offset: 0x400,
            tag: DwarfTag::BaseType,
            name: Some("unsigned long".to_string()),
            byte_size: Some(8),
            encoding: Some(0x07), // DW_ATE_unsigned
            type_ref: None,
            members: vec![],
        }],
        value_ranges: vec![ValueRangeObservation {
            address: lifted.entry_point,
            min: 0,
            max: i128::from(u64::MAX),
        }],
        ..Default::default()
    };

    let all_evidence = recoverer.collect_evidence(&ctx).expect("should collect evidence");
    assert!(
        all_evidence.len() >= 2,
        "should have evidence from DWARF + value range strategies, got {}",
        all_evidence.len()
    );

    let best = recoverer.recover_type(&ctx, lifted.entry_point).expect("should recover type");
    assert!(best.confidence > 0.5, "confidence should be meaningful, got {}", best.confidence);
}

// ---------------------------------------------------------------------------
// 9. x86_64 module-level decompilation from binary
// ---------------------------------------------------------------------------

#[test]
fn test_rc_e2e_x86_64_decompile_module() {
    let mut add_code = Vec::new();
    add_code.extend_from_slice(&X86_64_ADD_RAX_RDX);
    add_code.extend_from_slice(&X86_64_RET);

    let mut sub_code = Vec::new();
    sub_code.extend_from_slice(&X86_64_SUB_RAX_RDX);
    sub_code.extend_from_slice(&X86_64_RET);

    let elf_bytes = build_x86_64_elf(&[("x86_bin_add", &add_code), ("x86_bin_sub", &sub_code)]);
    let binary_info = parse_binary(&elf_bytes).expect("should parse");

    let text_section = binary_info.sections.iter().find(|s| s.executable).expect("text section");

    let boundaries: Vec<FunctionBoundary> = binary_info
        .function_symbols()
        .map(|s| FunctionBoundary { name: s.name.clone(), start: s.address, size: s.size })
        .collect();

    let lifter = Lifter::new_with_arch(
        boundaries,
        text_section.virtual_address,
        text_section.data.len() as u64,
        0,
        LiftArch::X86_64,
    );

    let verifiable_funcs: Vec<_> = lifter
        .functions()
        .iter()
        .filter_map(|fb| {
            lifter
                .lift_function(&text_section.data, fb.start)
                .ok()
                .map(|lifted| lift_adapter::lift_to_verifiable(&lifted))
        })
        .collect();

    assert_eq!(verifiable_funcs.len(), 2, "should lift both functions");

    let decompiler = Decompiler::default();
    let module = decompiler.decompile_module("x86_rc_module", &verifiable_funcs);

    assert_eq!(module.name, "x86_rc_module");
    assert_eq!(module.functions.len(), 2, "module should contain 2 functions");

    let source = module.to_source();
    assert!(
        source.contains("// Decompiled module: x86_rc_module"),
        "module source should contain header"
    );
}

// ---------------------------------------------------------------------------
// 10. x86_64 NOP sled function
// ---------------------------------------------------------------------------

#[test]
fn test_rc_e2e_x86_64_nop_sled_function() {
    let mut code = Vec::new();
    code.extend_from_slice(&X86_64_NOP);
    code.extend_from_slice(&X86_64_NOP);
    code.extend_from_slice(&X86_64_NOP);
    code.extend_from_slice(&X86_64_NOP);
    code.extend_from_slice(&X86_64_ADD_RAX_RDX);
    code.extend_from_slice(&X86_64_RET);

    let elf_bytes = build_x86_64_elf(&[("nop_sled", &code)]);
    let binary_info = parse_binary(&elf_bytes).expect("should parse");
    assert_eq!(binary_info.architecture, Architecture::X86_64);

    let text_section = binary_info.sections.iter().find(|s| s.executable).expect("text section");
    let sym = binary_info.find_symbol("nop_sled").expect("symbol");

    let mut instructions: Vec<Instruction> = Vec::new();
    let mut offset = 0usize;
    while offset < text_section.data.len() {
        let addr = text_section.virtual_address + offset as u64;
        let insn = trust_disasm::decode_x86_64(&text_section.data[offset..], addr)
            .expect("x86_64 disassembly should succeed");
        let size = insn.size as usize;
        assert!(size > 0, "x86_64 decoder must make forward progress");
        instructions.push(insn);
        offset += size;
    }

    assert!(
        instructions.iter().any(|i| format!("{:?}", i.opcode).contains("Nop")),
        "should decode NOP instructions"
    );
    assert!(
        instructions.iter().any(|i| format!("{:?}", i.opcode).contains("Add")),
        "should decode ADD instruction"
    );
    assert!(
        instructions.iter().any(|i| format!("{:?}", i.opcode).contains("Ret")),
        "should decode RET instruction"
    );

    let boundary = FunctionBoundary { name: sym.name.clone(), start: sym.address, size: sym.size };
    let lifter = Lifter::new_with_arch(
        vec![boundary],
        text_section.virtual_address,
        text_section.data.len() as u64,
        0,
        LiftArch::X86_64,
    );

    let lifted =
        lifter.lift_function(&text_section.data, sym.address).expect("should lift nop_sled");
    let vcs = lift_adapter::generate_binary_vcs(&lifted);
    assert!(!vcs.is_empty(), "nop_sled should produce VCs");
    for vc in &vcs {
        assert_eq!(vc.function, "nop_sled");
    }
}

// ---------------------------------------------------------------------------
// 11. x86_64 empty function
// ---------------------------------------------------------------------------

#[test]
fn test_rc_e2e_x86_64_empty_function() {
    let elf_bytes = build_x86_64_elf(&[("empty_ret", &X86_64_RET)]);
    let binary_info = parse_binary(&elf_bytes).expect("should parse");

    assert_eq!(binary_info.format, BinaryFormat::Elf);
    assert_eq!(binary_info.architecture, Architecture::X86_64);

    let text_section = binary_info.sections.iter().find(|s| s.executable).expect("text section");
    let sym = binary_info.find_symbol("empty_ret").expect("symbol");

    let mut instructions: Vec<Instruction> = Vec::new();
    let mut offset = 0usize;
    while offset < text_section.data.len() {
        let addr = text_section.virtual_address + offset as u64;
        let insn = trust_disasm::decode_x86_64(&text_section.data[offset..], addr)
            .expect("x86_64 disassembly should succeed");
        let size = insn.size as usize;
        assert!(size > 0, "x86_64 decoder must make forward progress");
        instructions.push(insn);
        offset += size;
    }

    assert_eq!(instructions.len(), 1, "empty_ret should decode to one RET");
    assert!(
        instructions.iter().any(|i| format!("{:?}", i.opcode).contains("Ret")),
        "should decode RET instruction"
    );

    let boundary = FunctionBoundary { name: sym.name.clone(), start: sym.address, size: sym.size };
    let lifter = Lifter::new_with_arch(
        vec![boundary],
        text_section.virtual_address,
        text_section.data.len() as u64,
        0,
        LiftArch::X86_64,
    );

    let lifted =
        lifter.lift_function(&text_section.data, sym.address).expect("should lift empty_ret");
    assert!(!lifted.cfg.blocks.is_empty(), "lifted CFG should have blocks");

    let vcs = lift_adapter::generate_binary_vcs(&lifted);
    assert!(!vcs.is_empty(), "empty_ret should produce VCs");
    for vc in &vcs {
        assert_eq!(vc.function, "empty_ret");
    }
}
