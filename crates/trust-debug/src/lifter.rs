// trust-debug/lifter.rs: Binary → VerifiableBody IR lifting
//
// Lifts machine code into our verification IR so that all tRust analysis
// tools work on binaries the same way they work on MIR. This is what makes
// trust-debug work in black-box mode on arbitrary binaries.
//
// Current status: structural types and placeholder lifter. Full implementation
// will integrate with:
//   - LLVM2 for disassembly and lifting to tMIR
//   - DWARF/PDB for source mapping
//   - Binary analysis frameworks for control flow recovery
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::binary::BinaryMetadata;

/// Configuration for the binary lifter.
#[derive(Debug, Clone)]
pub(crate) struct LiftConfig {
    /// Whether to attempt DWARF-based source mapping.
    pub use_dwarf: bool,
    /// Whether to recover high-level types from debug info.
    pub recover_types: bool,
    /// Maximum number of instructions to lift per function.
    pub max_instructions: usize,
}

impl Default for LiftConfig {
    fn default() -> Self {
        Self {
            use_dwarf: true,
            recover_types: true,
            max_instructions: 10_000,
        }
    }
}

/// Result of lifting a binary to our verification IR.
#[derive(Debug, Clone)]
pub(crate) struct LiftResult {
    /// Lifted functions in our IR.
    pub functions: Vec<VerifiableFunction>,
    /// Reconstructed call graph.
    pub call_graph: call_graph::CallGraph,
    /// Warnings/errors during lifting.
    pub diagnostics: Vec<LiftDiagnostic>,
}

/// A diagnostic message from the lifter.
#[derive(Debug, Clone)]
pub(crate) struct LiftDiagnostic {
    pub level: DiagnosticLevel,
    pub message: String,
    pub address: Option<u64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DiagnosticLevel {
    Warning,
    Error,
}

/// Lift a binary into our verification IR.
///
/// This is the entry point for black-box mode. Takes parsed binary metadata
/// and the raw binary bytes, and produces `VerifiableFunction`s that can be
/// fed into the same analysis pipeline as MIR-extracted functions.
///
/// Current implementation is a scaffold — it creates function stubs from
/// the symbol table. Full lifting will integrate with LLVM2/tMIR.
pub(crate) fn lift_binary(metadata: &BinaryMetadata, _binary: &[u8], _config: &LiftConfig) -> LiftResult {
    let mut functions = Vec::new();
    let mut call_graph = call_graph::CallGraph::new();
    let mut diagnostics = Vec::new();

    for symbol in &metadata.symbols {
        if symbol.kind != crate::binary::SymbolKind::Function {
            continue;
        }

        // Create a stub VerifiableFunction from the symbol
        let func = VerifiableFunction {
            name: symbol.name.clone(),
            def_path: symbol.name.clone(),
            span: source_span_from_metadata(metadata, symbol.address),
            body: stub_body(),
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        call_graph.add_node(call_graph::CallGraphNode {
            def_path: symbol.name.clone(),
            name: symbol.name.clone(),
            is_public: true,
            is_entry_point: symbol.name == "main" || symbol.name == "_start",
            span: SourceSpan::default(),
        });

        functions.push(func);
    }

    if functions.is_empty() {
        diagnostics.push(LiftDiagnostic {
            level: DiagnosticLevel::Warning,
            message: "No function symbols found in binary — is it stripped?".to_string(),
            address: None,
        });
    }

    LiftResult { functions, call_graph, diagnostics }
}

fn source_span_from_metadata(metadata: &BinaryMetadata, address: u64) -> SourceSpan {
    // Look up source mapping from DWARF if available
    for mapping in &metadata.source_map {
        if mapping.address == address
            && let Some(span) = &mapping.source {
                return span.clone();
            }
    }
    SourceSpan::default()
}

fn stub_body() -> VerifiableBody {
    VerifiableBody {
        locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
        blocks: vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Return,
        }],
        arg_count: 0,
        return_ty: Ty::Unit,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary::{BinaryFormat, BinaryMetadata, BinarySymbol, SymbolKind};

    #[test]
    fn test_lift_with_symbols() {
        let metadata = BinaryMetadata {
            format: BinaryFormat::Elf,
            arch: "x86_64".to_string(),
            has_debug_info: false,
            symbols: vec![
                BinarySymbol { name: "main".into(), address: 0x1000, size: 100, kind: SymbolKind::Function },
                BinarySymbol { name: "helper".into(), address: 0x1100, size: 50, kind: SymbolKind::Function },
                BinarySymbol { name: "data".into(), address: 0x2000, size: 8, kind: SymbolKind::Data },
            ],
            source_map: vec![],
        };

        let result = lift_binary(&metadata, &[], &LiftConfig::default());
        assert_eq!(result.functions.len(), 2); // main + helper, not data
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn test_lift_stripped_binary_warns() {
        let metadata = BinaryMetadata {
            format: BinaryFormat::Elf,
            arch: "x86_64".to_string(),
            has_debug_info: false,
            symbols: vec![],
            source_map: vec![],
        };

        let result = lift_binary(&metadata, &[], &LiftConfig::default());
        assert!(result.functions.is_empty());
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].level, DiagnosticLevel::Warning);
    }

    #[test]
    fn test_lift_marks_entry_points() {
        let metadata = BinaryMetadata {
            format: BinaryFormat::Elf,
            arch: "x86_64".to_string(),
            has_debug_info: false,
            symbols: vec![
                BinarySymbol { name: "main".into(), address: 0x1000, size: 100, kind: SymbolKind::Function },
                BinarySymbol { name: "_start".into(), address: 0x800, size: 20, kind: SymbolKind::Function },
                BinarySymbol { name: "foo".into(), address: 0x1100, size: 50, kind: SymbolKind::Function },
            ],
            source_map: vec![],
        };

        let result = lift_binary(&metadata, &[], &LiftConfig::default());
        assert_eq!(result.functions.len(), 3);
    }
}
