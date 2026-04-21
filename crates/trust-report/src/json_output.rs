//! JSON file and streaming output for proof reports.
//!
//! Writes `JsonProofReport` to JSON files and NDJSON streams.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::Write;
use std::path::Path;

use trust_types::*;

/// Write the JSON proof report to a file in the output directory.
///
/// Creates `report.json` (pretty-printed) in the given directory.
pub fn write_json_report(report: &JsonProofReport, output_dir: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(output_dir)?;
    let json = serde_json::to_string_pretty(report)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    std::fs::write(output_dir.join("report.json"), json)?;
    Ok(())
}

/// Write the proof report as newline-delimited JSON (NDJSON) to a writer.
///
/// NDJSON format for streaming large crate results:
/// - Line 1: header record (metadata + crate_name)
/// - Lines 2..N: one record per function
/// - Last line: footer record (crate summary)
///
/// Each line is a self-contained JSON object. Consumers can process
/// function results incrementally without loading the entire report.
pub fn write_ndjson<W: Write>(report: &JsonProofReport, writer: &mut W) -> std::io::Result<()> {
    // Header
    let header = NdjsonHeader {
        record_type: "header".to_string(),
        metadata: report.metadata.clone(),
        crate_name: report.crate_name.clone(),
    };
    serde_json::to_writer(&mut *writer, &header)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    writer.write_all(b"\n")?;

    // Per-function records
    for func in &report.functions {
        let record = NdjsonFunctionRecord {
            record_type: "function".to_string(),
            crate_name: report.crate_name.clone(),
            function: func.clone(),
        };
        serde_json::to_writer(&mut *writer, &record)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        writer.write_all(b"\n")?;
    }

    // Footer
    let footer =
        NdjsonFooter { record_type: "footer".to_string(), summary: report.summary.clone() };
    serde_json::to_writer(&mut *writer, &footer)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    writer.write_all(b"\n")?;

    Ok(())
}

/// Write the proof report as NDJSON to a file.
pub fn write_ndjson_report(report: &JsonProofReport, output_dir: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(output_dir)?;
    let file = std::fs::File::create(output_dir.join("report.ndjson"))?;
    let mut writer = std::io::BufWriter::new(file);
    write_ndjson(report, &mut writer)?;
    writer.flush()?;
    Ok(())
}
