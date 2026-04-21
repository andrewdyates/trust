// trust-binary-parse: High-level DWARF parsing API
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::path::Path;

use self::constants::DW_AT_STMT_LIST;
use self::line::parse_line_program_with_size;

use crate::error::DwarfError;

pub(crate) mod abbrev;
pub(crate) mod constants;
pub(crate) mod info;
pub(crate) mod line;
pub(crate) mod str;
pub(crate) mod types;

pub use info::{AttributeValue, CompilationUnit, Die, parse_compilation_units};
pub use line::{LineProgramHeader, LineRow};
pub use types::{DwarfType, extract_types};

/// Parsed DWARF information assembled across sections.
#[derive(Debug, Clone, PartialEq)]
pub struct DwarfInfo<'a> {
    pub(crate) units: Vec<CompilationUnit<'a>>,
    pub(crate) line_programs: Vec<(LineProgramHeader, Vec<LineRow>)>,
    pub(crate) types: Vec<(usize, DwarfType)>,
}

impl<'a> DwarfInfo<'a> {
    /// Parse DWARF sections into compilation units, line programs, and types.
    pub fn parse(
        debug_info: &'a [u8],
        debug_abbrev: &'a [u8],
        debug_str: &'a [u8],
        debug_line: Option<&'a [u8]>,
    ) -> Result<Self, DwarfError> {
        let units = parse_compilation_units(debug_info, debug_abbrev, debug_str)?;
        let line_programs = match debug_line {
            Some(section) => parse_line_programs(section, &units)?,
            None => Vec::new(),
        };
        let types = extract_types(&units);

        Ok(Self { units, line_programs, types })
    }

    /// Find the closest line table entry for `address`.
    #[must_use]
    pub fn find_line_info(&self, address: u64) -> Option<(String, u64)> {
        self.line_programs.iter().find_map(|(header, rows)| {
            let row = find_row_for_address(rows, address)?;
            let file = header.file_names.get(row.file.checked_sub(1)?)?;
            let path = format_file_path(header, file);
            Some((path, row.line))
        })
    }

    /// Resolve a type DIE by absolute `.debug_info` offset.
    pub fn resolve_type(&self, die_offset: usize) -> Result<DwarfType, DwarfError> {
        crate::dwarf::types::resolve_type(&self.units, die_offset)
    }
}

fn parse_line_programs(
    debug_line: &[u8],
    units: &[CompilationUnit<'_>],
) -> Result<Vec<(LineProgramHeader, Vec<LineRow>)>, DwarfError> {
    let mut programs = Vec::new();
    let stmt_offsets = collect_stmt_list_offsets(units);

    if stmt_offsets.is_empty() {
        let mut offset = 0;
        while offset < debug_line.len() {
            let ((header, rows), consumed) = parse_line_program_with_size(&debug_line[offset..])?;
            programs.push((header, rows));
            if consumed == 0 {
                return Err(DwarfError::InvalidLineProgram);
            }
            offset += consumed;
        }
        return Ok(programs);
    }

    for offset in stmt_offsets {
        let ((header, rows), _) = parse_line_program_with_size(
            debug_line.get(offset..).ok_or(DwarfError::InvalidLineProgram)?,
        )?;
        programs.push((header, rows));
    }

    Ok(programs)
}

fn collect_stmt_list_offsets(units: &[CompilationUnit<'_>]) -> BTreeSet<usize> {
    let mut offsets = BTreeSet::new();
    for unit in units {
        collect_stmt_list_offsets_from_dies(&unit.dies, &mut offsets);
    }
    offsets
}

fn collect_stmt_list_offsets_from_dies(dies: &[Die<'_>], offsets: &mut BTreeSet<usize>) {
    for die in dies {
        if let Some(attribute) = die.attribute(DW_AT_STMT_LIST)
            && let AttributeValue::SecOffset(offset) = attribute.value
            && let Ok(offset) = usize::try_from(offset)
        {
            offsets.insert(offset);
        }
        collect_stmt_list_offsets_from_dies(&die.children, offsets);
    }
}

fn find_row_for_address<'a>(rows: &'a [LineRow], address: u64) -> Option<&'a LineRow> {
    let mut candidate: Option<&'a LineRow> = None;

    for row in rows {
        if row.end_sequence {
            if let Some(current) = candidate
                && address >= current.address && address < row.address
            {
                return Some(current);
            }
            candidate = None;
            continue;
        }

        if row.address > address {
            return candidate;
        }
        candidate = Some(row);
    }

    candidate.filter(|row| address >= row.address)
}

fn format_file_path(header: &LineProgramHeader, file: &crate::dwarf::line::FileEntry) -> String {
    if file.directory_index == 0 {
        return file.name.clone();
    }

    let Some(directory) = usize::try_from(file.directory_index)
        .ok()
        .and_then(|index| header.include_directories.get(index.saturating_sub(1)))
    else {
        return file.name.clone();
    };

    Path::new(directory).join(&file.name).display().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dwarf::info::{Attribute, AttributeValue, CompilationUnit, Die};
    use crate::dwarf::line::{FileEntry, LineRow, LineProgramHeader};

    fn make_header(dirs: Vec<String>, files: Vec<FileEntry>) -> LineProgramHeader {
        LineProgramHeader {
            minimum_instruction_length: 1,
            maximum_operations_per_instruction: 1,
            default_is_stmt: true,
            line_base: -5,
            line_range: 14,
            opcode_base: 13,
            standard_opcode_lengths: vec![0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1],
            include_directories: dirs,
            file_names: files,
        }
    }

    fn make_row(address: u64, file: usize, line: u64, end_sequence: bool) -> LineRow {
        LineRow {
            address,
            file,
            line,
            column: 0,
            is_stmt: true,
            basic_block: false,
            end_sequence,
            prologue_end: false,
            epilogue_begin: false,
        }
    }

    // --- find_row_for_address tests ---

    #[test]
    fn test_find_row_for_address_exact_match_returns_row() {
        let rows = vec![
            make_row(0x1000, 1, 10, false),
            make_row(0x1004, 1, 11, false),
            make_row(0x1010, 1, 0, true),
        ];
        let row = find_row_for_address(&rows, 0x1000).unwrap();
        assert_eq!(row.line, 10);
        assert_eq!(row.address, 0x1000);
    }

    #[test]
    fn test_find_row_for_address_between_rows_returns_previous() {
        let rows = vec![
            make_row(0x1000, 1, 10, false),
            make_row(0x1004, 1, 11, false),
            make_row(0x1010, 1, 0, true),
        ];
        let row = find_row_for_address(&rows, 0x1002).unwrap();
        assert_eq!(row.line, 10);
    }

    #[test]
    fn test_find_row_for_address_before_first_returns_none() {
        let rows = vec![
            make_row(0x1000, 1, 10, false),
            make_row(0x1010, 1, 0, true),
        ];
        assert!(find_row_for_address(&rows, 0x0FFF).is_none());
    }

    #[test]
    fn test_find_row_for_address_at_end_sequence_boundary_returns_none() {
        let rows = vec![
            make_row(0x1000, 1, 10, false),
            make_row(0x1010, 1, 0, true),
        ];
        // Address exactly at end_sequence boundary is outside the range
        assert!(find_row_for_address(&rows, 0x1010).is_none());
    }

    #[test]
    fn test_find_row_for_address_empty_rows_returns_none() {
        assert!(find_row_for_address(&[], 0x1000).is_none());
    }

    #[test]
    fn test_find_row_for_address_multiple_sequences() {
        let rows = vec![
            make_row(0x1000, 1, 10, false),
            make_row(0x1010, 1, 0, true),
            // Second sequence
            make_row(0x2000, 1, 20, false),
            make_row(0x2004, 1, 21, false),
            make_row(0x2010, 1, 0, true),
        ];
        // Address in second sequence
        let row = find_row_for_address(&rows, 0x2002).unwrap();
        assert_eq!(row.line, 20);
    }

    #[test]
    fn test_find_row_for_address_between_sequences_returns_none() {
        let rows = vec![
            make_row(0x1000, 1, 10, false),
            make_row(0x1010, 1, 0, true),
            make_row(0x2000, 1, 20, false),
            make_row(0x2010, 1, 0, true),
        ];
        // Address between two sequences (after first end, before second start)
        assert!(find_row_for_address(&rows, 0x1500).is_none());
    }

    // --- format_file_path tests ---

    #[test]
    fn test_format_file_path_directory_index_zero_returns_name() {
        let header = make_header(vec!["src".into()], vec![]);
        let file = FileEntry {
            name: "main.rs".into(),
            directory_index: 0,
            last_modified: 0,
            size: 0,
        };
        assert_eq!(format_file_path(&header, &file), "main.rs");
    }

    #[test]
    fn test_format_file_path_with_directory_returns_joined() {
        let header = make_header(vec!["src".into()], vec![]);
        let file = FileEntry {
            name: "main.rs".into(),
            directory_index: 1,
            last_modified: 0,
            size: 0,
        };
        assert_eq!(format_file_path(&header, &file), "src/main.rs");
    }

    #[test]
    fn test_format_file_path_out_of_range_directory_returns_name() {
        let header = make_header(vec!["src".into()], vec![]);
        let file = FileEntry {
            name: "main.rs".into(),
            directory_index: 99,
            last_modified: 0,
            size: 0,
        };
        assert_eq!(format_file_path(&header, &file), "main.rs");
    }

    #[test]
    fn test_format_file_path_no_directories_returns_name() {
        let header = make_header(vec![], vec![]);
        let file = FileEntry {
            name: "main.rs".into(),
            directory_index: 1,
            last_modified: 0,
            size: 0,
        };
        assert_eq!(format_file_path(&header, &file), "main.rs");
    }

    // --- collect_stmt_list_offsets tests ---

    #[test]
    fn test_collect_stmt_list_offsets_empty_units() {
        let offsets = collect_stmt_list_offsets(&[]);
        assert!(offsets.is_empty());
    }

    #[test]
    fn test_collect_stmt_list_offsets_extracts_from_dies() {
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![Die {
                offset: 0,
                tag: 0x11, // DW_TAG_COMPILE_UNIT
                has_children: false,
                attributes: vec![Attribute {
                    name: DW_AT_STMT_LIST,
                    value: AttributeValue::SecOffset(0x100),
                }],
                children: Vec::new(),
            }],
        };
        let offsets = collect_stmt_list_offsets(&[unit]);
        assert_eq!(offsets.len(), 1);
        assert!(offsets.contains(&0x100));
    }

    #[test]
    fn test_collect_stmt_list_offsets_deduplicates() {
        let make_die = |offset: usize, stmt_list: u64| Die {
            offset,
            tag: 0x11,
            has_children: false,
            attributes: vec![Attribute {
                name: DW_AT_STMT_LIST,
                value: AttributeValue::SecOffset(stmt_list),
            }],
            children: Vec::new(),
        };
        let unit = CompilationUnit {
            unit_length: 0,
            version: 4,
            abbrev_offset: 0,
            address_size: 8,
            header_size: 0,
            dies: vec![make_die(0, 0x100), make_die(10, 0x100)],
        };
        let offsets = collect_stmt_list_offsets(&[unit]);
        assert_eq!(offsets.len(), 1); // BTreeSet deduplicates
    }

    // --- DwarfInfo integration tests ---

    #[test]
    fn test_dwarf_info_parse_empty_sections_returns_empty() {
        let info = DwarfInfo::parse(&[], &[], &[], None).unwrap();
        assert!(info.units.is_empty());
        assert!(info.line_programs.is_empty());
        assert!(info.types.is_empty());
    }

    #[test]
    fn test_dwarf_info_find_line_info_no_programs_returns_none() {
        let info = DwarfInfo {
            units: Vec::new(),
            line_programs: Vec::new(),
            types: Vec::new(),
        };
        assert!(info.find_line_info(0x1000).is_none());
    }

    #[test]
    fn test_dwarf_info_find_line_info_with_matching_address() {
        let header = make_header(
            vec!["src".into()],
            vec![FileEntry {
                name: "main.rs".into(),
                directory_index: 1,
                last_modified: 0,
                size: 0,
            }],
        );
        let rows = vec![
            make_row(0x1000, 1, 42, false),
            make_row(0x1010, 1, 0, true),
        ];
        let info = DwarfInfo {
            units: Vec::new(),
            line_programs: vec![(header, rows)],
            types: Vec::new(),
        };
        let (path, line) = info.find_line_info(0x1004).unwrap();
        assert_eq!(path, "src/main.rs");
        assert_eq!(line, 42);
    }

    #[test]
    fn test_dwarf_info_find_line_info_no_match_returns_none() {
        let header = make_header(
            vec!["src".into()],
            vec![FileEntry {
                name: "main.rs".into(),
                directory_index: 1,
                last_modified: 0,
                size: 0,
            }],
        );
        let rows = vec![
            make_row(0x1000, 1, 42, false),
            make_row(0x1010, 1, 0, true),
        ];
        let info = DwarfInfo {
            units: Vec::new(),
            line_programs: vec![(header, rows)],
            types: Vec::new(),
        };
        assert!(info.find_line_info(0x2000).is_none());
    }

    #[test]
    fn test_dwarf_info_resolve_type_not_found_returns_error() {
        let info = DwarfInfo {
            units: Vec::new(),
            line_programs: Vec::new(),
            types: Vec::new(),
        };
        assert!(info.resolve_type(0x999).is_err());
    }
}
