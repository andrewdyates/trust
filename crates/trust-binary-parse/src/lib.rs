//! trust-binary-parse: Binary format parsing for tRust reverse compilation
//!
//! Parses ELF, Mach-O, PE binaries, DWARF debug info, and symbol demangling
//! from first principles. Zero external dependencies.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]
#![allow(dead_code)]

pub(crate) mod constants;
pub(crate) mod cursor;
pub(crate) mod demangle;
pub(crate) mod detect;
pub(crate) mod dwarf;
pub(crate) mod elf;
pub(crate) mod elf_relocation;
pub(crate) mod error;
pub(crate) mod header;
pub(crate) mod leb128;
pub(crate) mod load_command;
pub(crate) mod macho;
pub(crate) mod pe;
pub(crate) mod read;
pub(crate) mod relocation;
pub(crate) mod symbol;
pub(crate) mod unified;

pub use detect::{detect_format, BinaryFormat};
pub use dwarf::DwarfInfo;
pub use elf::Elf64;
pub use elf_relocation::{Elf64Dyn, Elf64Rel, Elf64Rela, ResolvedRelocation};
pub use error::{DwarfError, ParseError};
pub use macho::MachO;
pub use pe::Pe;
pub use unified::{parse_binary, Architecture, BinaryInfo, SectionInfo, SymbolInfo};
