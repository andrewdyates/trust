// trust-debug/binary.rs: Binary parsing and source mapping
//
// Parses ELF/Mach-O binaries, extracts symbols, sections, and DWARF debug
// info to provide source-level mapping for violations found in lifted code.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use trust_types::SourceSpan;

/// A source mapping from a binary address to a source location.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceMapping {
    /// Virtual address in the binary.
    pub address: u64,
    /// Function name at this address.
    pub function: String,
    /// Source file and line (from DWARF if available).
    pub source: Option<SourceSpan>,
}

/// Extracted symbol from a binary.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct BinarySymbol {
    pub name: String,
    pub address: u64,
    pub size: u64,
    pub kind: SymbolKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum SymbolKind {
    Function,
    Data,
    Unknown,
}

/// Metadata extracted from a binary file.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct BinaryMetadata {
    /// Binary format (ELF, Mach-O, PE).
    pub format: BinaryFormat,
    /// Architecture (x86_64, aarch64, etc.).
    pub arch: String,
    /// Whether the binary has debug info (DWARF).
    pub has_debug_info: bool,
    /// Extracted symbols.
    pub symbols: Vec<BinarySymbol>,
    /// Source mappings from DWARF.
    pub source_map: Vec<SourceMapping>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum BinaryFormat {
    Elf,
    MachO,
    Pe,
    Unknown,
}

/// Parse binary metadata from raw bytes.
///
/// This is the entry point for black-box mode. It extracts:
/// - File format and architecture
/// - Function symbols (names, addresses, sizes)
/// - DWARF debug info → source mappings
///
/// Future: integrate with `object` and `gimli` crates for full parsing.
/// For now, provides the structural types that the rest of trust-debug uses.
pub(crate) fn parse_binary_metadata(binary: &[u8]) -> BinaryMetadata {
    let format = detect_format(binary);
    BinaryMetadata {
        format,
        arch: detect_arch(binary, format),
        has_debug_info: false,
        symbols: vec![],
        source_map: vec![],
    }
}

fn detect_format(binary: &[u8]) -> BinaryFormat {
    if binary.len() < 4 {
        return BinaryFormat::Unknown;
    }
    match &binary[..4] {
        [0x7f, b'E', b'L', b'F'] => BinaryFormat::Elf,
        [0xfe, 0xed, 0xfa, 0xce] | [0xfe, 0xed, 0xfa, 0xcf] | [0xcf, 0xfa, 0xed, 0xfe] | [0xce, 0xfa, 0xed, 0xfe] => BinaryFormat::MachO,
        [b'M', b'Z', ..] => BinaryFormat::Pe,
        _ => BinaryFormat::Unknown,
    }
}

fn detect_arch(binary: &[u8], format: BinaryFormat) -> String {
    match format {
        BinaryFormat::Elf if binary.len() > 18 => {
            match (binary[4], u16::from_le_bytes([binary[18], binary[19]])) {
                (2, 0x3e) => "x86_64".to_string(),
                (2, 0xb7) => "aarch64".to_string(),
                (1, 0x03) => "x86".to_string(),
                (1, 0x28) => "arm".to_string(),
                _ => "unknown".to_string(),
            }
        }
        BinaryFormat::MachO if binary.len() > 8 => {
            let cputype = if binary[0] == 0xcf || binary[0] == 0xce {
                u32::from_le_bytes([binary[4], binary[5], binary[6], binary[7]])
            } else {
                u32::from_be_bytes([binary[4], binary[5], binary[6], binary[7]])
            };
            match cputype {
                0x0100_0007 => "x86_64".to_string(),
                0x0100_000c => "aarch64".to_string(),
                _ => "unknown".to_string(),
            }
        }
        _ => "unknown".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detect_elf() {
        let elf_header = [0x7f, b'E', b'L', b'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x3e, 0];
        let meta = parse_binary_metadata(&elf_header);
        assert_eq!(meta.format, BinaryFormat::Elf);
        assert_eq!(meta.arch, "x86_64");
    }

    #[test]
    fn test_detect_macho() {
        let mut macho = vec![0xcf, 0xfa, 0xed, 0xfe]; // MH_MAGIC_64 LE
        macho.extend_from_slice(&0x0100_000cu32.to_le_bytes()); // ARM64
        macho.extend_from_slice(&[0; 24]);
        let meta = parse_binary_metadata(&macho);
        assert_eq!(meta.format, BinaryFormat::MachO);
        assert_eq!(meta.arch, "aarch64");
    }

    #[test]
    fn test_detect_pe() {
        let pe = [b'M', b'Z', 0, 0];
        let meta = parse_binary_metadata(&pe);
        assert_eq!(meta.format, BinaryFormat::Pe);
    }

    #[test]
    fn test_detect_unknown() {
        let meta = parse_binary_metadata(&[0, 0, 0, 0]);
        assert_eq!(meta.format, BinaryFormat::Unknown);
    }

    #[test]
    fn test_empty_binary() {
        let meta = parse_binary_metadata(&[]);
        assert_eq!(meta.format, BinaryFormat::Unknown);
    }
}
