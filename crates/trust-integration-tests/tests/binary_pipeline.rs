// Integration tests: type recovery + disassembly pipeline
//
// Exercises the binary parsing, disassembly, and type recovery pipelines
// as cross-crate integration tests.
//
// Part of #818
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_binary_parse::{parse_binary, Architecture, BinaryFormat};
use trust_disasm::{decode_x86_64, ControlFlow, Opcode};
use trust_disasm::x86_64::X86_64Decoder;
use trust_disasm::Decoder;
use trust_type_recover::{
    DereferenceObservation, DwarfEntry, DwarfTag, PointerRecoveryStrategy, RecoveredType,
    RecoveryContext, TypeRecoverer, TypeRecoveryStrategy, ValueRangeObservation, ValueRangeStrategy,
};
use trust_types::Ty;

// ===========================================================================
// Test 1: ELF binary parsing via parse_binary()
// ===========================================================================

/// Build a minimal valid ELF64 x86-64 binary with .text, symbols, and entry point.
fn build_minimal_elf() -> Vec<u8> {
    let mut buf = Vec::new();

    let shstrtab = b"\0.shstrtab\0.symtab\0.strtab\0";
    let strtab = b"\0_start\0main\0";

    let phdr_off: u64 = 0x40;
    let shstrtab_off: u64 = 0x78;
    let strtab_off: u64 = 0x98;
    let symtab_off: u64 = 0xA8;
    let shdr_off: u64 = 0xF0;

    // ELF Header (64 bytes)
    buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']); // e_ident magic
    buf.push(2); // ELFCLASS64
    buf.push(1); // ELFDATA2LSB
    buf.push(1); // EV_CURRENT
    buf.push(0); // OS/ABI
    buf.extend_from_slice(&[0u8; 8]); // padding
    buf.extend_from_slice(&2u16.to_le_bytes()); // ET_EXEC
    buf.extend_from_slice(&0x3Eu16.to_le_bytes()); // EM_X86_64
    buf.extend_from_slice(&1u32.to_le_bytes()); // EV_CURRENT
    buf.extend_from_slice(&0x400000u64.to_le_bytes()); // e_entry
    buf.extend_from_slice(&phdr_off.to_le_bytes()); // e_phoff
    buf.extend_from_slice(&shdr_off.to_le_bytes()); // e_shoff
    buf.extend_from_slice(&0u32.to_le_bytes()); // e_flags
    buf.extend_from_slice(&64u16.to_le_bytes()); // e_ehsize
    buf.extend_from_slice(&56u16.to_le_bytes()); // e_phentsize
    buf.extend_from_slice(&1u16.to_le_bytes()); // e_phnum
    buf.extend_from_slice(&64u16.to_le_bytes()); // e_shentsize
    buf.extend_from_slice(&4u16.to_le_bytes()); // e_shnum
    buf.extend_from_slice(&1u16.to_le_bytes()); // e_shstrndx

    // Program header (PT_LOAD, RX)
    buf.extend_from_slice(&1u32.to_le_bytes()); // p_type = PT_LOAD
    buf.extend_from_slice(&5u32.to_le_bytes()); // p_flags = PF_R | PF_X
    buf.extend_from_slice(&0u64.to_le_bytes()); // p_offset
    buf.extend_from_slice(&0x400000u64.to_le_bytes()); // p_vaddr
    buf.extend_from_slice(&0x400000u64.to_le_bytes()); // p_paddr
    buf.extend_from_slice(&0x200u64.to_le_bytes()); // p_filesz
    buf.extend_from_slice(&0x200u64.to_le_bytes()); // p_memsz
    buf.extend_from_slice(&0x1000u64.to_le_bytes()); // p_align

    // .shstrtab data
    buf.extend_from_slice(shstrtab);
    while buf.len() < 0x98 {
        buf.push(0);
    }
    // .strtab data
    buf.extend_from_slice(strtab);
    while buf.len() < 0xA8 {
        buf.push(0);
    }

    // Symbol table entries (24 bytes each for ELF64)
    // Null symbol
    buf.extend_from_slice(&0u32.to_le_bytes()); // st_name
    buf.push(0); // st_info
    buf.push(0); // st_other
    buf.extend_from_slice(&0u16.to_le_bytes()); // st_shndx
    buf.extend_from_slice(&0u64.to_le_bytes()); // st_value
    buf.extend_from_slice(&0u64.to_le_bytes()); // st_size
    // _start (STB_GLOBAL | STT_FUNC)
    buf.extend_from_slice(&1u32.to_le_bytes()); // st_name = offset of "_start" in strtab
    buf.push((1 << 4) | 2); // st_info = STB_GLOBAL | STT_FUNC
    buf.push(0);
    buf.extend_from_slice(&1u16.to_le_bytes());
    buf.extend_from_slice(&0x400000u64.to_le_bytes()); // st_value
    buf.extend_from_slice(&16u64.to_le_bytes()); // st_size
    // main (STB_GLOBAL | STT_FUNC)
    buf.extend_from_slice(&8u32.to_le_bytes()); // st_name = offset of "main" in strtab
    buf.push((1 << 4) | 2);
    buf.push(0);
    buf.extend_from_slice(&1u16.to_le_bytes());
    buf.extend_from_slice(&0x400010u64.to_le_bytes()); // st_value
    buf.extend_from_slice(&32u64.to_le_bytes()); // st_size

    // Section headers (4 entries x 64 bytes each)
    #[allow(clippy::too_many_arguments)]
    fn write_shdr(
        buf: &mut Vec<u8>,
        name: u32,
        typ: u32,
        flags: u64,
        addr: u64,
        offset: u64,
        size: u64,
        link: u32,
        info: u32,
        align: u64,
        entsize: u64,
    ) {
        buf.extend_from_slice(&name.to_le_bytes());
        buf.extend_from_slice(&typ.to_le_bytes());
        buf.extend_from_slice(&flags.to_le_bytes());
        buf.extend_from_slice(&addr.to_le_bytes());
        buf.extend_from_slice(&offset.to_le_bytes());
        buf.extend_from_slice(&size.to_le_bytes());
        buf.extend_from_slice(&link.to_le_bytes());
        buf.extend_from_slice(&info.to_le_bytes());
        buf.extend_from_slice(&align.to_le_bytes());
        buf.extend_from_slice(&entsize.to_le_bytes());
    }

    // SHN_UNDEF
    write_shdr(&mut buf, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    // .shstrtab (SHT_STRTAB = 3)
    write_shdr(
        &mut buf,
        1,
        3,
        0,
        0,
        shstrtab_off,
        shstrtab.len() as u64,
        0,
        0,
        1,
        0,
    );
    // .symtab (SHT_SYMTAB = 2), link -> .strtab (index 3), info = 1 (first global)
    write_shdr(&mut buf, 11, 2, 0, 0, symtab_off, 72, 3, 1, 8, 24);
    // .strtab (SHT_STRTAB = 3)
    write_shdr(
        &mut buf,
        19,
        3,
        0,
        0,
        strtab_off,
        strtab.len() as u64,
        0,
        0,
        1,
        0,
    );

    buf
}

#[test]
fn test_binary_parse_elf_format_detection() {
    let elf_data = build_minimal_elf();
    let info = parse_binary(&elf_data).expect("should parse ELF binary");

    assert_eq!(info.format, BinaryFormat::Elf);
    assert_eq!(info.architecture, Architecture::X86_64);
    assert_eq!(info.entry_point, Some(0x400000));
}

#[test]
fn test_binary_parse_elf_symbols() {
    let elf_data = build_minimal_elf();
    let info = parse_binary(&elf_data).expect("should parse ELF binary");

    // Should have function symbols with correct addresses and sizes
    let funcs: Vec<_> = info.function_symbols().collect();
    assert_eq!(funcs.len(), 2, "expected _start and main");

    let start = info.find_symbol("_start").expect("should find _start");
    assert_eq!(start.address, 0x400000);
    assert_eq!(start.size, 16);
    assert!(start.is_function);

    let main = info.find_symbol("main").expect("should find main");
    assert_eq!(main.address, 0x400010);
    assert_eq!(main.size, 32);
    assert!(main.is_function);
}

#[test]
fn test_binary_parse_invalid_magic() {
    let garbage = [0xDE, 0xAD, 0xBE, 0xEF, 0x00, 0x00, 0x00, 0x00];
    let err = parse_binary(&garbage);
    assert!(err.is_err(), "should reject data with invalid magic bytes");
}

// ===========================================================================
// Test 2: x86-64 disassembly
// ===========================================================================

#[test]
fn test_disasm_x86_64_single_instruction() {
    // 0xC3 = RET
    let insn = decode_x86_64(&[0xC3], 0x1000).expect("should decode RET");
    assert_eq!(insn.opcode, Opcode::Ret);
    assert_eq!(insn.size, 1);
    assert_eq!(insn.flow, ControlFlow::Return);
    assert_eq!(insn.address, 0x1000);
}

#[test]
fn test_disasm_x86_64_function_prologue() {
    let decoder = X86_64Decoder::new();

    // Standard x86-64 function prologue:
    //   55              PUSH RBP
    //   48 89 E5        MOV RBP, RSP
    //   48 83 EC 20     SUB RSP, 0x20
    //   B8 2A 00 00 00  MOV EAX, 42
    //   C3              RET
    let code = [
        0x55u8,                         // PUSH RBP
        0x48, 0x89, 0xE5,               // MOV RBP, RSP
        0x48, 0x83, 0xEC, 0x20,         // SUB RSP, 0x20
        0xB8, 0x2A, 0x00, 0x00, 0x00,   // MOV EAX, 42
        0xC3,                           // RET
    ];

    let results = decoder.decode_all(&code, 0x401000);
    assert_eq!(results.len(), 5, "should decode 5 instructions");

    // Verify each instruction decoded correctly
    let opcodes: Vec<Opcode> = results
        .iter()
        .map(|r| r.as_ref().expect("all should decode").opcode)
        .collect();
    assert_eq!(
        opcodes,
        vec![Opcode::Push, Opcode::Mov, Opcode::Sub, Opcode::Mov, Opcode::Ret],
    );

    // Verify addresses are sequential
    let addrs: Vec<u64> = results
        .iter()
        .map(|r| r.as_ref().unwrap().address)
        .collect();
    assert_eq!(addrs, vec![0x401000, 0x401001, 0x401004, 0x401008, 0x40100D]);

    // Last instruction should be a return
    let last = results.last().unwrap().as_ref().unwrap();
    assert_eq!(last.flow, ControlFlow::Return);
}

#[test]
fn test_disasm_x86_64_branch_target() {
    // E8 10 00 00 00 = CALL +0x10 at address 0x2000
    // Target = 0x2000 + 5 + 0x10 = 0x2015
    let insn = decode_x86_64(&[0xE8, 0x10, 0x00, 0x00, 0x00], 0x2000)
        .expect("should decode CALL");
    assert_eq!(insn.opcode, Opcode::Call);
    assert_eq!(insn.flow, ControlFlow::Call);
    assert_eq!(insn.branch_target(), Some(0x2015));
}

// ===========================================================================
// Test 3: Type recovery from DWARF + value range evidence (integer types)
// ===========================================================================

#[test]
fn test_type_recover_integer_from_dwarf() {
    let recoverer = TypeRecoverer::new();

    // Provide DWARF evidence for an unsigned 32-bit integer
    let ctx = RecoveryContext {
        dwarf_entries: vec![DwarfEntry {
            die_offset: 0x200,
            tag: DwarfTag::BaseType,
            name: Some("unsigned int".to_string()),
            byte_size: Some(4),
            encoding: Some(0x07), // DW_ATE_unsigned
            type_ref: None,
            members: vec![],
        }],
        ..Default::default()
    };

    let evidence = recoverer
        .recover_type(&ctx, 0x1000)
        .expect("should recover type from DWARF");

    assert_eq!(
        evidence.recovered_type,
        RecoveredType::Primitive(Ty::Int {
            width: 32,
            signed: false,
        }),
    );
    assert!(
        evidence.confidence > 0.9,
        "DWARF evidence should have high confidence, got {}",
        evidence.confidence,
    );
}

#[test]
fn test_type_recover_agreement_boosts_confidence() {
    let recoverer = TypeRecoverer::new();

    // Both DWARF and value-range agree on u8
    let ctx = RecoveryContext {
        dwarf_entries: vec![DwarfEntry {
            die_offset: 0x300,
            tag: DwarfTag::BaseType,
            name: Some("unsigned char".to_string()),
            byte_size: Some(1),
            encoding: Some(0x08), // DW_ATE_unsigned_char
            type_ref: None,
            members: vec![],
        }],
        value_ranges: vec![ValueRangeObservation {
            address: 0x2000,
            min: 0,
            max: 200,
        }],
        ..Default::default()
    };

    let evidence = recoverer
        .recover_type(&ctx, 0x2000)
        .expect("should recover with agreement");

    // DWARF base confidence (0.95) boosted by agreement with value range
    assert!(
        evidence.confidence > 0.95,
        "agreement should boost confidence above 0.95, got {}",
        evidence.confidence,
    );
}

#[test]
fn test_type_recover_value_range_strategy_alone() {
    // Use only the ValueRangeStrategy to recover integer types from ranges
    let strategy = ValueRangeStrategy;

    let ctx = RecoveryContext {
        value_ranges: vec![ValueRangeObservation {
            address: 0x3000,
            min: -100,
            max: 100,
        }],
        ..Default::default()
    };

    let evidence = strategy
        .recover(&ctx)
        .expect("value range strategy should succeed");

    assert!(!evidence.is_empty(), "should produce evidence from value range");
    // Value range [-100, 100] fits in a signed integer
    let first = &evidence[0];
    match &first.recovered_type {
        RecoveredType::Primitive(Ty::Int { signed, .. }) => {
            assert!(*signed, "negative min should infer signed integer");
        }
        other => panic!("expected Primitive(Int), got: {other:?}"),
    }
}

// ===========================================================================
// Test 4: Type recovery from pointer dereference patterns
// ===========================================================================

#[test]
fn test_type_recover_pointer_from_dereference() {
    // Use the PointerRecoveryStrategy to recover pointer types
    let strategy = PointerRecoveryStrategy;

    let ctx = RecoveryContext {
        dereference_observations: vec![DereferenceObservation {
            load_addr: 0x4000,
            deref_addr: 0x4008,
            pointer_size: 8,            // 64-bit pointer
            pointee_access_size: 4,     // reads 4 bytes through the pointer
            is_store: false,
        }],
        ..Default::default()
    };

    let evidence = strategy
        .recover(&ctx)
        .expect("pointer strategy should succeed");

    assert!(!evidence.is_empty(), "should produce pointer evidence");

    let first = &evidence[0];
    match &first.recovered_type {
        RecoveredType::Pointer { mutable, pointee } => {
            // Read-only dereference => immutable pointer
            assert!(!mutable, "read dereference should infer immutable pointer");
            // Pointee: 4-byte access => i32 or u32
            match pointee.as_ref() {
                RecoveredType::Primitive(Ty::Int { width: 32, .. }) => {}
                other => panic!("expected 32-bit int pointee, got: {other:?}"),
            }
        }
        other => panic!("expected Pointer type, got: {other:?}"),
    }
}

#[test]
fn test_type_recover_mutable_pointer_from_store() {
    let strategy = PointerRecoveryStrategy;

    let ctx = RecoveryContext {
        dereference_observations: vec![DereferenceObservation {
            load_addr: 0x5000,
            deref_addr: 0x5010,
            pointer_size: 8,
            pointee_access_size: 8,     // writes 8 bytes through the pointer
            is_store: true,             // this is a store, so mutable
        }],
        ..Default::default()
    };

    let evidence = strategy
        .recover(&ctx)
        .expect("pointer strategy should succeed for store");

    assert!(!evidence.is_empty(), "should produce pointer evidence for store");

    let first = &evidence[0];
    match &first.recovered_type {
        RecoveredType::Pointer { mutable, pointee } => {
            assert!(*mutable, "store dereference should infer mutable pointer");
            match pointee.as_ref() {
                RecoveredType::Primitive(Ty::Int { width: 64, .. }) => {}
                other => panic!("expected 64-bit int pointee, got: {other:?}"),
            }
        }
        other => panic!("expected Pointer type, got: {other:?}"),
    }
}

// ===========================================================================
// Test 5: Full TypeRecoverer no-evidence error
// ===========================================================================

#[test]
fn test_type_recover_no_evidence_returns_error() {
    let recoverer = TypeRecoverer::new();
    let ctx = RecoveryContext::default(); // empty context
    let result = recoverer.recover_type(&ctx, 0xDEAD);
    assert!(
        result.is_err(),
        "empty context should produce NoEvidence error"
    );
}

// ===========================================================================
// Test 6: Combined pipeline — parse binary then disassemble its sections
// ===========================================================================

#[test]
fn test_binary_parse_then_disassemble() {
    // This test exercises the intended pipeline: parse a binary, then
    // disassemble instructions from its sections.
    //
    // We build a minimal ELF and then pretend to disassemble from its
    // entry point region (even though the test ELF doesn't have actual
    // code in its .text section — we inject known bytes and verify the
    // decode_x86_64 API works on them).

    // Verify the pipeline types compose: BinaryInfo -> bytes -> Instruction
    let elf_data = build_minimal_elf();
    let info = parse_binary(&elf_data).expect("should parse ELF");
    assert_eq!(info.architecture, Architecture::X86_64);

    // Simulate disassembling code bytes at the entry point
    // (in a real pipeline, we'd use info.bytes_at_va())
    let entry = info.entry_point.expect("should have entry point");
    let code_bytes = [0x55, 0xC3]; // PUSH RBP; RET

    let decoder = X86_64Decoder::new();
    let instructions = decoder.decode_all(&code_bytes, entry);
    assert_eq!(instructions.len(), 2);

    let push = instructions[0].as_ref().expect("push should decode");
    assert_eq!(push.opcode, Opcode::Push);
    assert_eq!(push.address, entry);

    let ret = instructions[1].as_ref().expect("ret should decode");
    assert_eq!(ret.opcode, Opcode::Ret);
    assert_eq!(ret.address, entry + 1);
}
