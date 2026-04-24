// trust-binary-parse: Unified binary abstraction
//
// Provides a format-agnostic view of parsed binaries. The `parse_binary`
// function auto-detects ELF, Mach-O, or PE format and returns a common
// `BinaryInfo` struct with architecture, sections, and symbols.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::detect::{BinaryFormat, detect_format};
use crate::error::ParseError;

/// Target architecture detected from binary headers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Architecture {
    /// ARM 64-bit (AArch64)
    AArch64,
    /// x86 64-bit (AMD64)
    X86_64,
    /// x86 32-bit
    X86,
    /// ARM 32-bit
    Arm,
    /// Unknown or unsupported architecture
    Unknown(u32),
}

impl Architecture {
    /// Human-readable name for the architecture.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::AArch64 => "AArch64",
            Self::X86_64 => "x86-64",
            Self::X86 => "x86",
            Self::Arm => "ARM",
            Self::Unknown(_) => "Unknown",
        }
    }
}

/// Information about an executable section/segment.
#[derive(Debug, Clone)]
pub struct SectionInfo {
    /// Section name (e.g., ".text", "__text")
    pub name: String,
    /// Virtual address when loaded
    pub virtual_address: u64,
    /// Raw bytes of the section
    pub data: Vec<u8>,
    /// Whether this section contains executable code
    pub executable: bool,
}

/// A symbol table entry with format-agnostic fields.
#[derive(Debug, Clone)]
pub struct SymbolInfo {
    /// Symbol name
    pub name: String,
    /// Symbol address (virtual)
    pub address: u64,
    /// Symbol size (0 if unknown)
    pub size: u64,
    /// Whether this symbol represents a function
    pub is_function: bool,
}

/// Format-agnostic representation of a parsed binary.
#[derive(Debug)]
pub struct BinaryInfo {
    /// Detected binary format
    pub format: BinaryFormat,
    /// Target architecture
    pub architecture: Architecture,
    /// Executable sections with their data and virtual addresses
    pub sections: Vec<SectionInfo>,
    /// Symbol table entries
    pub symbols: Vec<SymbolInfo>,
    /// Entry point address (if available)
    pub entry_point: Option<u64>,
}

impl BinaryInfo {
    /// Get all function symbols.
    pub fn function_symbols(&self) -> impl Iterator<Item = &SymbolInfo> {
        self.symbols.iter().filter(|s| s.is_function)
    }

    /// Find a symbol by name.
    #[must_use]
    pub fn find_symbol(&self, name: &str) -> Option<&SymbolInfo> {
        self.symbols.iter().find(|s| s.name == name)
    }

    /// Get the bytes at a virtual address from the appropriate section.
    ///
    /// Returns `None` if the address is not within any section.
    #[must_use]
    pub fn bytes_at_va(&self, va: u64, len: usize) -> Option<&[u8]> {
        for section in &self.sections {
            let section_end = section.virtual_address + section.data.len() as u64;
            if va >= section.virtual_address && va < section_end {
                let offset = (va - section.virtual_address) as usize;
                let available = section.data.len() - offset;
                let actual_len = len.min(available);
                return Some(&section.data[offset..offset + actual_len]);
            }
        }
        None
    }
}

/// Parse a binary from raw bytes, auto-detecting the format.
///
/// Returns a `BinaryInfo` with architecture, sections, symbols, and entry
/// point extracted from the binary.
///
/// # Errors
///
/// Returns `ParseError` if format detection fails or the binary cannot be
/// parsed by the detected format's parser.
pub fn parse_binary(data: &[u8]) -> Result<BinaryInfo, ParseError> {
    let format = detect_format(data).ok_or_else(|| {
        if data.len() < 4 {
            ParseError::UnexpectedEof(0)
        } else {
            let magic = u32::from_be_bytes([data[0], data[1], data[2], data[3]]);
            ParseError::InvalidMagic(magic)
        }
    })?;

    match format {
        BinaryFormat::Elf => parse_elf(data),
        BinaryFormat::MachO => parse_macho(data),
        BinaryFormat::FatMachO => parse_fat_macho(data),
        BinaryFormat::Pe => parse_pe(data),
    }
}

/// Parse an ELF binary into `BinaryInfo`.
fn parse_elf(data: &[u8]) -> Result<BinaryInfo, ParseError> {
    let elf = crate::elf::Elf64::parse(data)?;

    let architecture = match elf.header.e_machine {
        0xB7 => Architecture::AArch64, // EM_AARCH64
        0x3E => Architecture::X86_64,  // EM_X86_64
        0x03 => Architecture::X86,     // EM_386
        0x28 => Architecture::Arm,     // EM_ARM
        other => Architecture::Unknown(other as u32),
    };

    // Collect executable sections
    let mut sections = Vec::new();
    // SHF_EXECINSTR = 0x4
    for sh in &elf.sections {
        if sh.sh_flags & 0x4 != 0 && sh.sh_size > 0 {
            let name = elf.section_name(sh).unwrap_or("").to_owned();
            let section_data = elf.section_data(sh)?;
            sections.push(SectionInfo {
                name,
                virtual_address: sh.sh_addr,
                data: section_data.to_vec(),
                executable: true,
            });
        }
    }

    // Parse symbols
    let elf_symbols = elf.symbols().unwrap_or_default();
    let symbols = elf_symbols
        .iter()
        .filter(|s| !s.name.is_empty())
        .map(|s| SymbolInfo {
            name: s.name.to_owned(),
            address: s.st_value,
            size: s.st_size,
            is_function: s.is_function(),
        })
        .collect();

    Ok(BinaryInfo {
        format: BinaryFormat::Elf,
        architecture,
        sections,
        symbols,
        entry_point: Some(elf.entry_point()),
    })
}

/// Parse a thin Mach-O binary into `BinaryInfo`.
fn parse_macho(data: &[u8]) -> Result<BinaryInfo, ParseError> {
    let macho = crate::macho::MachO::parse(data)?;
    build_macho_info(&macho)
}

/// Parse a fat/universal Mach-O binary into `BinaryInfo`.
///
/// Prefers the AArch64 slice if available, otherwise falls back to the
/// first available slice.
fn parse_fat_macho(data: &[u8]) -> Result<BinaryInfo, ParseError> {
    let macho = crate::macho::MachO::parse_prefer_aarch64(data)?;
    let mut info = build_macho_info(&macho)?;
    info.format = BinaryFormat::FatMachO;
    Ok(info)
}

/// Build `BinaryInfo` from a parsed `MachO`.
fn build_macho_info(macho: &crate::macho::MachO<'_>) -> Result<BinaryInfo, ParseError> {
    use crate::constants::{CPU_TYPE_ARM64, CPU_TYPE_X86_64};

    let architecture = match macho.header.cputype {
        c if c == CPU_TYPE_ARM64 => Architecture::AArch64,
        c if c == CPU_TYPE_X86_64 => Architecture::X86_64,
        other => Architecture::Unknown(other as u32),
    };

    // Collect executable sections
    let mut sections = Vec::new();
    for (_seg, sect) in macho.sections() {
        if sect.is_executable() && !sect.data.is_empty() {
            sections.push(SectionInfo {
                name: format!("{},{}", sect.segname, sect.sectname),
                virtual_address: sect.addr,
                data: sect.data.to_vec(),
                executable: true,
            });
        }
    }

    // Parse symbols
    let macho_symbols = macho.symbols().unwrap_or_default();
    let symbols = macho_symbols
        .iter()
        .filter(|s| !s.name.is_empty() && s.is_defined_in_section())
        .map(|s| SymbolInfo {
            name: s.name.to_owned(),
            address: s.n_value,
            size: 0, // Mach-O nlist_64 has no size field
            is_function: s.is_external() && s.is_defined_in_section(),
        })
        .collect();

    let entry_point = macho.entry_point().map(|entryoff| {
        macho
            .find_segment("__TEXT")
            .map(|segment| segment.vmaddr.saturating_add(entryoff))
            .unwrap_or(entryoff)
    });

    Ok(BinaryInfo { format: BinaryFormat::MachO, architecture, sections, symbols, entry_point })
}

/// Parse a PE binary into `BinaryInfo`.
fn parse_pe(data: &[u8]) -> Result<BinaryInfo, ParseError> {
    let pe = crate::pe::Pe::parse(data)?;

    let architecture = match pe.coff_header.machine {
        crate::pe::IMAGE_FILE_MACHINE_AMD64 => Architecture::X86_64,
        crate::pe::IMAGE_FILE_MACHINE_ARM64 => Architecture::AArch64,
        crate::pe::IMAGE_FILE_MACHINE_I386 => Architecture::X86,
        crate::pe::IMAGE_FILE_MACHINE_ARM => Architecture::Arm,
        other => Architecture::Unknown(other as u32),
    };

    // Collect executable sections
    // IMAGE_SCN_MEM_EXECUTE = 0x2000_0000
    let mut sections = Vec::new();
    let image_base = pe.image_base();
    for sh in &pe.sections {
        if sh.characteristics & 0x2000_0000 != 0 && sh.size_of_raw_data > 0 {
            let section_data = pe.section_data(sh)?;
            sections.push(SectionInfo {
                name: sh.name.clone(),
                virtual_address: image_base + sh.virtual_address as u64,
                data: section_data.to_vec(),
                executable: true,
            });
        }
    }

    // Parse COFF symbols (usually only in object files / unstripped PEs)
    let pe_symbols = pe.symbols().unwrap_or_default();
    let symbols = pe_symbols
        .iter()
        .filter(|s| !s.name.is_empty())
        .map(|s| SymbolInfo {
            name: s.name.to_owned(),
            address: s.value as u64,
            size: 0, // COFF symbols have no size
            is_function: s.is_function(),
        })
        .collect();

    let entry_point =
        if pe.entry_point() != 0 { Some(image_base + pe.entry_point() as u64) } else { None };

    Ok(BinaryInfo { format: BinaryFormat::Pe, architecture, sections, symbols, entry_point })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_binary_auto_detect_elf() {
        // Reuse the ELF test binary builder from the elf module
        let data = build_test_elf();
        let info = parse_binary(&data).expect("should parse ELF via auto-detect");

        assert_eq!(info.format, BinaryFormat::Elf);
        assert_eq!(info.architecture, Architecture::X86_64);
        assert_eq!(info.entry_point, Some(0x400000));

        // Should have function symbols
        let funcs: Vec<_> = info.function_symbols().collect();
        assert_eq!(funcs.len(), 2);
        assert!(funcs.iter().any(|s| s.name == "_start"));
        assert!(funcs.iter().any(|s| s.name == "main"));
    }

    #[test]
    fn test_parse_binary_auto_detect_macho() {
        let data = build_test_macho();
        let info = parse_binary(&data).expect("should parse Mach-O via auto-detect");

        assert_eq!(info.format, BinaryFormat::MachO);
        assert_eq!(info.architecture, Architecture::AArch64);
        assert!(info.entry_point.is_some());

        // Should have executable sections
        assert!(!info.sections.is_empty());
        assert!(info.sections.iter().all(|s| s.executable));

        // Should have _main symbol
        let main_sym = info.find_symbol("_main");
        assert!(main_sym.is_some());
    }

    #[test]
    fn test_parse_binary_auto_detect_pe() {
        let data = build_test_pe();
        let info = parse_binary(&data).expect("should parse PE via auto-detect");

        assert_eq!(info.format, BinaryFormat::Pe);
        assert_eq!(info.architecture, Architecture::X86_64);
        assert!(info.entry_point.is_some());

        // Should have executable section (.text)
        assert!(info.sections.iter().any(|s| s.name == ".text"));
    }

    #[test]
    fn test_parse_binary_unknown_format() {
        let data = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let err = parse_binary(&data).unwrap_err();
        assert!(matches!(err, ParseError::InvalidMagic(_)));
    }

    #[test]
    fn test_parse_binary_too_short() {
        let err = parse_binary(&[0x7F]).unwrap_err();
        assert!(matches!(err, ParseError::UnexpectedEof(_)));
    }

    #[test]
    fn test_binary_info_bytes_at_va() {
        let data = build_test_macho();
        let info = parse_binary(&data).expect("should parse");

        // The __text section should have the RET instruction at its VA
        if let Some(text) = info.sections.first() {
            let bytes = info.bytes_at_va(text.virtual_address, 4);
            assert!(bytes.is_some());
            assert_eq!(bytes.unwrap().len(), 4);
        }
    }

    #[test]
    fn test_binary_info_bytes_at_invalid_va() {
        let data = build_test_macho();
        let info = parse_binary(&data).expect("should parse");
        assert!(info.bytes_at_va(0xDEAD_BEEF, 4).is_none());
    }

    #[test]
    fn test_architecture_name() {
        assert_eq!(Architecture::AArch64.name(), "AArch64");
        assert_eq!(Architecture::X86_64.name(), "x86-64");
        assert_eq!(Architecture::X86.name(), "x86");
        assert_eq!(Architecture::Arm.name(), "ARM");
        assert_eq!(Architecture::Unknown(0).name(), "Unknown");
    }

    #[test]
    fn test_elf_symbol_sizes() {
        let data = build_test_elf();
        let info = parse_binary(&data).expect("should parse");

        let start = info.find_symbol("_start").expect("should find _start");
        assert_eq!(start.size, 16);
        assert_eq!(start.address, 0x400000);
        assert!(start.is_function);

        let main = info.find_symbol("main").expect("should find main");
        assert_eq!(main.size, 32);
        assert_eq!(main.address, 0x400010);
        assert!(main.is_function);
    }

    // --- Test binary builders (copied from format-specific modules) ---

    /// Build a minimal valid ELF64 binary for testing.
    fn build_test_elf() -> Vec<u8> {
        let mut buf = Vec::new();

        let shstrtab = b"\0.shstrtab\0.symtab\0.strtab\0";
        let strtab = b"\0_start\0main\0";

        let phdr_off: u64 = 0x40;
        let shstrtab_off: u64 = 0x78;
        let strtab_off: u64 = 0x98;
        let symtab_off: u64 = 0xA8;
        let shdr_off: u64 = 0xF0;

        // ELF Header
        buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']);
        buf.push(2); // ELFCLASS64
        buf.push(1); // ELFDATA2LSB
        buf.push(1); // EV_CURRENT
        buf.push(0); // OS/ABI
        buf.extend_from_slice(&[0u8; 8]);
        buf.extend_from_slice(&2u16.to_le_bytes()); // ET_EXEC
        buf.extend_from_slice(&0x3Eu16.to_le_bytes()); // EM_X86_64
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.extend_from_slice(&0x400000u64.to_le_bytes());
        buf.extend_from_slice(&phdr_off.to_le_bytes());
        buf.extend_from_slice(&shdr_off.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&64u16.to_le_bytes());
        buf.extend_from_slice(&56u16.to_le_bytes());
        buf.extend_from_slice(&1u16.to_le_bytes());
        buf.extend_from_slice(&64u16.to_le_bytes());
        buf.extend_from_slice(&4u16.to_le_bytes());
        buf.extend_from_slice(&1u16.to_le_bytes());

        // Program header
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.extend_from_slice(&5u32.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&0x400000u64.to_le_bytes());
        buf.extend_from_slice(&0x400000u64.to_le_bytes());
        buf.extend_from_slice(&0x200u64.to_le_bytes());
        buf.extend_from_slice(&0x200u64.to_le_bytes());
        buf.extend_from_slice(&0x1000u64.to_le_bytes());

        buf.extend_from_slice(shstrtab);
        while buf.len() < 0x98 {
            buf.push(0);
        }
        buf.extend_from_slice(strtab);
        while buf.len() < 0xA8 {
            buf.push(0);
        }

        // Symbols
        // Null symbol
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.push(0);
        buf.push(0);
        buf.extend_from_slice(&0u16.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        // _start
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.push((1 << 4) | 2);
        buf.push(0);
        buf.extend_from_slice(&1u16.to_le_bytes());
        buf.extend_from_slice(&0x400000u64.to_le_bytes());
        buf.extend_from_slice(&16u64.to_le_bytes());
        // main
        buf.extend_from_slice(&8u32.to_le_bytes());
        buf.push((1 << 4) | 2);
        buf.push(0);
        buf.extend_from_slice(&1u16.to_le_bytes());
        buf.extend_from_slice(&0x400010u64.to_le_bytes());
        buf.extend_from_slice(&32u64.to_le_bytes());

        // Section headers
        write_elf_shdr(&mut buf, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
        write_elf_shdr(&mut buf, 1, 3, 0, 0, shstrtab_off, shstrtab.len() as u64, 0, 0, 1, 0);
        write_elf_shdr(&mut buf, 11, 2, 0, 0, symtab_off, 72, 3, 1, 8, 24);
        write_elf_shdr(&mut buf, 19, 3, 0, 0, strtab_off, strtab.len() as u64, 0, 0, 1, 0);

        buf
    }

    #[allow(clippy::too_many_arguments)]
    fn write_elf_shdr(
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

    /// Build a minimal Mach-O binary for testing.
    fn build_test_macho() -> Vec<u8> {
        use crate::constants::*;

        let mut buf = Vec::new();

        // Mach-O header (32 bytes)
        buf.extend_from_slice(&MH_MAGIC_64.to_le_bytes());
        buf.extend_from_slice(&(CPU_TYPE_ARM64 as u32).to_le_bytes());
        buf.extend_from_slice(&(CPU_SUBTYPE_ARM64_ALL as u32).to_le_bytes());
        buf.extend_from_slice(&MH_EXECUTE.to_le_bytes());
        buf.extend_from_slice(&3u32.to_le_bytes()); // ncmds: segment + symtab + main

        let sizeofcmds_offset = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes()); // placeholder
        buf.extend_from_slice(&0u32.to_le_bytes()); // flags
        buf.extend_from_slice(&0u32.to_le_bytes()); // reserved

        let cmds_start = buf.len();

        // LC_SEGMENT_64: __TEXT with __text section
        let segment_start = buf.len();
        buf.extend_from_slice(&LC_SEGMENT_64.to_le_bytes());
        let seg_cmdsize_offset = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes());

        let mut segname = [0u8; 16];
        segname[..6].copy_from_slice(b"__TEXT");
        buf.extend_from_slice(&segname);

        buf.extend_from_slice(&0x100000000u64.to_le_bytes());
        buf.extend_from_slice(&0x4000u64.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&0x4000u64.to_le_bytes());
        buf.extend_from_slice(&7i32.to_le_bytes());
        buf.extend_from_slice(&5i32.to_le_bytes());
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());

        let mut sectname = [0u8; 16];
        sectname[..6].copy_from_slice(b"__text");
        buf.extend_from_slice(&sectname);

        let mut sect_segname = [0u8; 16];
        sect_segname[..6].copy_from_slice(b"__TEXT");
        buf.extend_from_slice(&sect_segname);

        buf.extend_from_slice(&0x100001000u64.to_le_bytes());
        buf.extend_from_slice(&4u64.to_le_bytes());
        let sect_offset_pos = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&2u32.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&(S_ATTR_PURE_INSTRUCTIONS | S_REGULAR).to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());

        let segment_end = buf.len();
        let seg_cmdsize = (segment_end - segment_start) as u32;
        buf[seg_cmdsize_offset..seg_cmdsize_offset + 4].copy_from_slice(&seg_cmdsize.to_le_bytes());

        // LC_SYMTAB
        buf.extend_from_slice(&LC_SYMTAB.to_le_bytes());
        buf.extend_from_slice(&24u32.to_le_bytes());
        let symoff_pos = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&1u32.to_le_bytes());
        let stroff_pos = buf.len();
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&7u32.to_le_bytes());

        // LC_MAIN
        buf.extend_from_slice(&LC_MAIN.to_le_bytes());
        buf.extend_from_slice(&24u32.to_le_bytes());
        buf.extend_from_slice(&0x1000u64.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());

        let cmds_end = buf.len();
        let sizeofcmds = (cmds_end - cmds_start) as u32;
        buf[sizeofcmds_offset..sizeofcmds_offset + 4].copy_from_slice(&sizeofcmds.to_le_bytes());

        // Section data: RET instruction
        let text_data_offset = buf.len();
        buf.extend_from_slice(&[0xC0, 0x03, 0x5F, 0xD6]);
        buf[sect_offset_pos..sect_offset_pos + 4]
            .copy_from_slice(&(text_data_offset as u32).to_le_bytes());

        // String table
        let strtab_offset = buf.len();
        buf.extend_from_slice(b"\0_main\0");
        buf[stroff_pos..stroff_pos + 4].copy_from_slice(&(strtab_offset as u32).to_le_bytes());

        // Symbol table: one nlist_64 for _main
        let symtab_offset = buf.len();
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.push(N_SECT | N_EXT);
        buf.push(1);
        buf.extend_from_slice(&0u16.to_le_bytes());
        buf.extend_from_slice(&0x100001000u64.to_le_bytes());
        buf[symoff_pos..symoff_pos + 4].copy_from_slice(&(symtab_offset as u32).to_le_bytes());

        buf
    }

    /// Build a minimal PE binary for testing.
    fn build_test_pe() -> Vec<u8> {
        let mut buf = vec![0u8; 0x800];

        let pe_offset: u32 = 0x80;
        let text_rva: u32 = 0x1000;

        // DOS Header
        buf[0] = b'M';
        buf[1] = b'Z';
        buf[0x3C..0x40].copy_from_slice(&pe_offset.to_le_bytes());

        // PE Signature
        buf[0x80..0x84].copy_from_slice(&0x0000_4550u32.to_le_bytes());

        // COFF Header
        let coff = 0x84usize;
        buf[coff..coff + 2].copy_from_slice(&0x8664u16.to_le_bytes()); // AMD64
        buf[coff + 2..coff + 4].copy_from_slice(&1u16.to_le_bytes()); // 1 section
        buf[coff + 16..coff + 18].copy_from_slice(&240u16.to_le_bytes()); // opt hdr size
        buf[coff + 18..coff + 20].copy_from_slice(&0x0022u16.to_le_bytes());

        // Optional Header PE32+
        let opt = 0x98usize;
        buf[opt..opt + 2].copy_from_slice(&0x20Bu16.to_le_bytes()); // PE32+
        buf[opt + 2] = 14;
        buf[opt + 4..opt + 8].copy_from_slice(&0x200u32.to_le_bytes());
        buf[opt + 16..opt + 20].copy_from_slice(&text_rva.to_le_bytes()); // entry
        buf[opt + 20..opt + 24].copy_from_slice(&text_rva.to_le_bytes());
        buf[opt + 24..opt + 32].copy_from_slice(&0x140000000u64.to_le_bytes());
        buf[opt + 32..opt + 36].copy_from_slice(&0x1000u32.to_le_bytes());
        buf[opt + 36..opt + 40].copy_from_slice(&0x200u32.to_le_bytes());
        buf[opt + 40..opt + 42].copy_from_slice(&6u16.to_le_bytes());
        buf[opt + 48..opt + 50].copy_from_slice(&6u16.to_le_bytes());
        buf[opt + 56..opt + 60].copy_from_slice(&0x4000u32.to_le_bytes());
        buf[opt + 60..opt + 64].copy_from_slice(&0x200u32.to_le_bytes());
        buf[opt + 68..opt + 70].copy_from_slice(&3u16.to_le_bytes());
        buf[opt + 70..opt + 72].copy_from_slice(&0x8160u16.to_le_bytes());
        buf[opt + 72..opt + 80].copy_from_slice(&0x100000u64.to_le_bytes());
        buf[opt + 80..opt + 88].copy_from_slice(&0x1000u64.to_le_bytes());
        buf[opt + 88..opt + 96].copy_from_slice(&0x100000u64.to_le_bytes());
        buf[opt + 96..opt + 104].copy_from_slice(&0x1000u64.to_le_bytes());
        buf[opt + 108..opt + 112].copy_from_slice(&16u32.to_le_bytes());

        // Section header for .text at 0x188
        let sh = 0x188usize;
        buf[sh..sh + 8].copy_from_slice(b".text\0\0\0");
        buf[sh + 8..sh + 12].copy_from_slice(&0x200u32.to_le_bytes());
        buf[sh + 12..sh + 16].copy_from_slice(&text_rva.to_le_bytes());
        buf[sh + 16..sh + 20].copy_from_slice(&0x200u32.to_le_bytes());
        buf[sh + 20..sh + 24].copy_from_slice(&0x200u32.to_le_bytes());
        buf[sh + 36..sh + 40].copy_from_slice(&0x6000_0020u32.to_le_bytes());

        buf
    }
}
