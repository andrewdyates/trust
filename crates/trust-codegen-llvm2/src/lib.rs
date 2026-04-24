//! trust-codegen-llvm2: LLVM2 codegen backend integration for rustc.
//!
//! This crate is the integration layer between the `trust-llvm2-bridge`
//! CodegenBackend implementation and the rustc compilation pipeline.
//!
//! # Architecture
//!
//! ```text
//! compiler/rustc_codegen_llvm2/  (future: thin adapter using rustc types)
//!     |
//!     v
//! trust-codegen-llvm2 (THIS CRATE: integration + configuration)
//!     |
//!     v
//! trust-llvm2-bridge::codegen_backend  (trait impl, lowering, optimization)
//!     |
//!     v
//! llvm2-lower / llvm2-codegen / llvm2-ir  (LLVM2 pipeline)
//! ```
//!
//! The `trust-llvm2-bridge` crate defines a `RustcCodegenBackend` trait that
//! mirrors the real `rustc_codegen_ssa::traits::CodegenBackend`. This crate:
//!
//! 1. Re-exports the bridge's backend types for consumers
//! 2. Provides `create_backend()` as the canonical entry point
//! 3. Adds codegen pipeline configuration (target, optimization level, etc.)
//! 4. Integrates `llvm2-codegen` for real machine code emission (TODO)
//!
//! When the `compiler/rustc_codegen_llvm2/` adapter is built, it will depend
//! on this crate and delegate the real rustc trait methods here.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// tRust: #829 — CodegenBackend scaffold for LLVM2 integration.

// ---------------------------------------------------------------------------
// Re-exports from trust-llvm2-bridge
// ---------------------------------------------------------------------------

pub use trust_llvm2_bridge::codegen_backend::{
    CodegenBackendError, CompiledModule, CompiledModules, CrateInfo, Llvm2CodegenBackend,
    Llvm2TargetArch, OngoingCodegen, OutputFilenames, RustcCodegenBackend, TargetConfig,
    WorkProduct,
};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors from the codegen integration layer.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CodegenError {
    /// Error from the bridge backend.
    #[error("backend error: {0}")]
    Backend(#[from] CodegenBackendError),

    /// Error from the llvm2-codegen pipeline.
    #[error("codegen pipeline error: {0}")]
    Pipeline(#[from] llvm2_codegen::CodegenError),

    /// Invalid configuration.
    #[error("invalid configuration: {0}")]
    Config(String),
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Optimization level for the LLVM2 codegen pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OptLevel {
    /// No optimizations (fastest compile time).
    #[default]
    None,
    /// Basic optimizations (dead block elimination).
    Basic,
    /// Full optimization pipeline (DCE, GVN, copy propagation).
    /// TODO: Wire llvm2-codegen optimization passes.
    Full,
}

/// Configuration for the LLVM2 codegen backend.
#[derive(Debug, Clone)]
pub struct CodegenConfig {
    /// Target architecture.
    pub target_arch: Llvm2TargetArch,
    /// Optimization level.
    pub opt_level: OptLevel,
    /// Whether to run translation validation after lowering.
    pub translation_validation: bool,
    /// Whether to emit debug info.
    pub emit_debug_info: bool,
}

impl Default for CodegenConfig {
    fn default() -> Self {
        Self {
            target_arch: Llvm2TargetArch::host(),
            opt_level: OptLevel::None,
            translation_validation: false,
            emit_debug_info: false,
        }
    }
}

// ---------------------------------------------------------------------------
// Backend construction
// ---------------------------------------------------------------------------

/// Create the LLVM2 codegen backend with default (host) configuration.
///
/// This is the canonical entry point for consumers that just need a working
/// backend without custom configuration.
#[must_use]
pub fn create_backend() -> Llvm2CodegenBackend {
    Llvm2CodegenBackend::host()
}

/// Create the LLVM2 codegen backend with the given configuration.
///
/// The `CodegenConfig` controls target arch, optimization level, and
/// whether translation validation is enabled.
#[must_use]
pub fn create_backend_with_config(config: &CodegenConfig) -> Llvm2CodegenBackend {
    Llvm2CodegenBackend::new(config.target_arch)
}

// ---------------------------------------------------------------------------
// Pipeline integration (future: wire llvm2-codegen)
// ---------------------------------------------------------------------------

/// Compile a crate through the full LLVM2 pipeline.
///
/// This is the high-level entry point that:
/// 1. Creates the backend
/// 2. Runs `codegen_crate` to lower MIR -> LIR
/// 3. Runs `join_codegen` to finalize
/// 4. Runs `link` to produce output
///
/// TODO: Wire `llvm2_codegen::Pipeline` for real machine code emission.
/// Currently delegates to the bridge's scaffold implementation (JSON serialization).
pub fn compile_crate(
    config: &CodegenConfig,
    crate_info: &CrateInfo,
    outputs: &OutputFilenames,
) -> Result<std::path::PathBuf, Box<CodegenError>> {
    let backend = create_backend_with_config(config);

    // Step 1: codegen_crate (MIR -> LIR)
    let ongoing = backend.codegen_crate(crate_info).map_err(|e| Box::new(CodegenError::from(e)))?;

    // Step 2: join_codegen (finalize)
    let (compiled, _work_products) =
        backend.join_codegen(ongoing, outputs).map_err(|e| Box::new(CodegenError::from(e)))?;

    // Step 3: link
    let output_path =
        backend.link(&compiled, outputs).map_err(|e| Box::new(CodegenError::from(e)))?;

    Ok(output_path)
}

/// Query the LLVM2 codegen pipeline for its capabilities.
///
/// Returns a summary of what the current backend supports. Useful for
/// the compiler driver to decide whether to fall back to LLVM.
#[must_use]
pub fn backend_capabilities() -> BackendCapabilities {
    BackendCapabilities {
        name: "llvm2",
        supported_targets: &["aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"],
        thin_lto: false,
        has_zstd: false,
        // TODO: Update as llvm2-codegen matures.
        real_machine_code: false,
        translation_validation: cfg!(feature = "transval"),
        z4_formal_proofs: cfg!(feature = "z4-proofs"),
    }
}

/// Summary of LLVM2 backend capabilities.
#[derive(Debug, Clone)]
pub struct BackendCapabilities {
    /// Backend name.
    pub name: &'static str,
    /// Supported target triples.
    pub supported_targets: &'static [&'static str],
    /// Whether ThinLTO is supported.
    pub thin_lto: bool,
    /// Whether zstd compression is available.
    pub has_zstd: bool,
    /// Whether real machine code emission is implemented (vs scaffold JSON).
    pub real_machine_code: bool,
    /// Whether translation validation is available.
    pub translation_validation: bool,
    /// Whether z4 formal proofs are available.
    pub z4_formal_proofs: bool,
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_backend() {
        let backend = create_backend();
        assert_eq!(backend.name(), "llvm2");
    }

    #[test]
    fn test_create_backend_with_config_aarch64() {
        let config =
            CodegenConfig { target_arch: Llvm2TargetArch::AArch64, ..CodegenConfig::default() };
        let backend = create_backend_with_config(&config);
        assert_eq!(backend.target_arch(), Llvm2TargetArch::AArch64);
        assert_eq!(backend.target_cpu(), "generic");
    }

    #[test]
    fn test_create_backend_with_config_x86_64() {
        let config =
            CodegenConfig { target_arch: Llvm2TargetArch::X86_64, ..CodegenConfig::default() };
        let backend = create_backend_with_config(&config);
        assert_eq!(backend.target_arch(), Llvm2TargetArch::X86_64);
    }

    #[test]
    fn test_backend_capabilities() {
        let caps = backend_capabilities();
        assert_eq!(caps.name, "llvm2");
        assert!(!caps.thin_lto);
        assert!(!caps.has_zstd);
        assert!(!caps.real_machine_code);
        assert_eq!(caps.supported_targets.len(), 2);
    }

    #[test]
    fn test_codegen_config_default() {
        let config = CodegenConfig::default();
        assert_eq!(config.opt_level, OptLevel::None);
        assert!(!config.translation_validation);
        assert!(!config.emit_debug_info);
    }

    #[test]
    fn test_opt_level_default() {
        assert_eq!(OptLevel::default(), OptLevel::None);
    }

    #[test]
    fn test_compile_crate_simple() {
        use trust_types::{
            BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
            Terminator, Ty, VerifiableBody, VerifiableFunction,
        };

        let config = CodegenConfig::default();
        let crate_info = CrateInfo {
            target_cpu: "generic".to_string(),
            crate_name: "test_crate".to_string(),
            functions: vec![VerifiableFunction {
                name: "add".to_string(),
                def_path: "test::add".to_string(),
                span: SourceSpan::default(),
                body: VerifiableBody {
                    locals: vec![
                        LocalDecl { index: 0, ty: Ty::i32(), name: None },
                        LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                        LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    ],
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    }],
                    arg_count: 2,
                    return_ty: Ty::i32(),
                },
                contracts: vec![],
                preconditions: vec![],
                postconditions: vec![],
                spec: Default::default(),
            }],
        };
        let outputs = OutputFilenames {
            out_dir: std::path::PathBuf::from("/tmp"),
            crate_stem: "test_crate".to_string(),
        };

        let result = compile_crate(&config, &crate_info, &outputs);
        assert!(result.is_ok(), "compile_crate should succeed: {:?}", result.err());
        assert_eq!(result.unwrap(), std::path::PathBuf::from("/tmp/test_crate.o"));
    }

    #[test]
    fn test_codegen_error_from_backend_error() {
        let backend_err = CodegenBackendError::Unavailable { reason: "not ready".to_string() };
        let err: CodegenError = backend_err.into();
        assert!(err.to_string().contains("not ready"));
    }

    #[test]
    fn test_re_exports_available() {
        // Verify key types are re-exported and usable.
        let _config = TargetConfig::default();
        let _arch = Llvm2TargetArch::host();
        let _backend = Llvm2CodegenBackend::host();
    }
}
