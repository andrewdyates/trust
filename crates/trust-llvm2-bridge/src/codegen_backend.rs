//! Scaffold implementation of `rustc_codegen_ssa::traits::CodegenBackend` for LLVM2.
//!
//! This module defines a trait and types that mirror the real rustc `CodegenBackend`
//! interface from `compiler/rustc_codegen_ssa/src/traits/backend.rs`. The trait
//! cannot directly reference rustc internals (they are not available via Cargo),
//! so we define parallel types that map 1:1 to the rustc structures.
//!
//! When the compiler plugin is wired (via `x.py`), a thin adapter in
//! `compiler/` will delegate from the real rustc trait to this implementation.
//!
//! # Architecture
//!
//! ```text
//! rustc_codegen_ssa::traits::CodegenBackend  (compiler-internal)
//!     │
//!     ▼
//! compiler/rustc_codegen_llvm2/  (future thin adapter, uses rustc types)
//!     │
//!     ▼
//! trust-llvm2-bridge::codegen_backend::RustcCodegenBackend  (this module)
//!     │
//!     ▼
//! trust-llvm2-bridge::lower_to_lir  (existing bridge)
//!     │
//!     ▼
//! llvm2-lower / llvm2-codegen  (LLVM2 pipeline)
//! ```
//!
//! # Reference
//!
//! The real rustc `CodegenBackend` trait (compiler/rustc_codegen_ssa/src/traits/backend.rs)
//! requires these methods:
//! - `name() -> &'static str`
//! - `init(&self, sess: &Session)`
//! - `target_config(&self, sess: &Session) -> TargetConfig`
//! - `target_cpu(&self, sess: &Session) -> String`
//! - `codegen_crate(&self, tcx: TyCtxt, crate_info: &CrateInfo) -> Box<dyn Any>`
//! - `join_codegen(...) -> (CompiledModules, FxIndexMap<WorkProductId, WorkProduct>)`
//! - `link(&self, ...)`
//!
//! Our trait mirrors these with our own types in place of rustc's.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::any::Any;
use std::collections::{BTreeSet, HashMap};
use std::path::PathBuf;

use llvm2_lower::function::{
    BasicBlock as LirBasicBlock, Function as LirFunction, Signature as LirSignature,
};
use llvm2_lower::instructions::{Block, Instruction as LirInstruction, Opcode, Value};
use llvm2_lower::types::Type as LirType;
use trust_types::VerifiableFunction;

use crate::{BridgeError, lower_to_lir};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors from the codegen backend.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CodegenBackendError {
    /// Bridge lowering failure.
    #[error("bridge error: {0}")]
    Bridge(#[from] BridgeError),

    /// Backend is not available or not initialized.
    #[error("backend unavailable: {reason}")]
    Unavailable { reason: String },

    /// A codegen unit failed to compile.
    #[error("codegen unit `{unit_name}` failed: {reason}")]
    CodegenUnitFailed { unit_name: String, reason: String },

    /// An optimization pass failed.
    #[error("optimization failed on `{func_name}`: {reason}")]
    OptimizationFailed { func_name: String, reason: String },

    /// Object emission failed.
    #[error("emit_object failed: {reason}")]
    EmitFailed { reason: String },

    /// llvm2-codegen pipeline failed while compiling a function.
    #[error("llvm2 pipeline failed for `{func_name}`: {reason}")]
    Pipeline { func_name: String, reason: String },

    /// Join/finalization failed.
    #[error("join failed: {reason}")]
    JoinFailed { reason: String },

    /// Link step failed.
    #[error("link failed: {reason}")]
    LinkFailed { reason: String },
}

// ---------------------------------------------------------------------------
// Types mirroring rustc_codegen_ssa structures
// ---------------------------------------------------------------------------

/// Target configuration, mirrors `rustc_codegen_ssa::TargetConfig`.
#[derive(Debug, Clone, Default)]
pub struct TargetConfig {
    /// Target features (e.g., "neon", "sse4.2").
    pub target_features: Vec<String>,
    /// Unstable target features.
    pub unstable_target_features: Vec<String>,
    /// Whether f16 basic arithmetic is reliable.
    pub has_reliable_f16: bool,
    /// Whether f16 math calls are reliable.
    pub has_reliable_f16_math: bool,
    /// Whether f128 basic arithmetic is reliable.
    pub has_reliable_f128: bool,
    /// Whether f128 math calls are reliable.
    pub has_reliable_f128_math: bool,
}

/// Crate-level information, mirrors `rustc_codegen_ssa::CrateInfo`.
///
/// Simplified for tRust's needs: we only need the target CPU and the list
/// of functions to compile.
#[derive(Debug, Clone)]
pub struct CrateInfo {
    /// Target CPU (e.g., "apple-m1", "generic").
    pub target_cpu: String,
    /// Crate name.
    pub crate_name: String,
    /// Functions to compile (extracted from MIR).
    pub functions: Vec<VerifiableFunction>,
}

/// A single compiled module (one codegen unit).
#[derive(Debug, Clone)]
pub struct CompiledModule {
    /// Module name (typically the codegen unit name).
    pub name: String,
    /// LIR functions produced by bridge lowering.
    pub lir_functions: Vec<LirFunction>,
    /// Object file path (if emitted).
    pub object_path: Option<PathBuf>,
    /// Number of functions in this module.
    pub function_count: usize,
}

/// Collection of all compiled modules for a crate.
#[derive(Debug, Clone)]
pub struct CompiledModules {
    /// Regular codegen unit modules.
    pub modules: Vec<CompiledModule>,
    /// Allocator module (if any).
    pub allocator_module: Option<CompiledModule>,
}

/// Allocator argument categories used by rustc shim wrappers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocatorArgKind {
    Layout,
    Ptr,
    Usize,
}

/// Allocator return categories used by rustc shim wrappers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocatorResultKind {
    Never,
    ResultPtr,
    Unit,
}

/// Known allocator shim wrapper kinds expected by rustc.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocatorFunctionKind {
    Alloc,
    AllocErrorHandler,
    AllocZeroed,
    Dealloc,
    Realloc,
}

/// Bridge-native description of one allocator shim wrapper.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AllocatorFunctionSpec {
    /// The rustc allocator method name (e.g. `alloc`, `realloc`).
    pub name: String,
    /// Mangled rustc-internal symbol for the wrapper exported by this module.
    pub wrapper_symbol_name: String,
    /// Mangled rustc-internal symbol this wrapper forwards to.
    pub callee_symbol_name: String,
    /// Semantic kind of the wrapper to be emitted.
    pub kind: AllocatorFunctionKind,
    /// Logical input shape before rustc ABI lowering.
    pub inputs: Vec<AllocatorArgKind>,
    /// Logical return shape before rustc ABI lowering.
    pub output: AllocatorResultKind,
}

/// Bridge-native description of a rustc allocator shim module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AllocatorModuleSpec {
    /// Stable name to use for the allocator module artifact.
    pub module_name: String,
    /// Allocator wrappers rustc expects in this module.
    pub functions: Vec<AllocatorFunctionSpec>,
    /// Mangled rustc-internal symbol for `__rust_no_alloc_shim_is_unstable_v2`.
    pub no_alloc_shim_is_unstable_symbol_name: Option<String>,
}

/// Output file names, mirrors `rustc_session::config::OutputFilenames`.
#[derive(Debug, Clone)]
pub struct OutputFilenames {
    /// Directory for output files.
    pub out_dir: PathBuf,
    /// Crate stem name.
    pub crate_stem: String,
}

impl OutputFilenames {
    /// Construct the path for an object file with a given extension.
    #[must_use]
    pub fn object_path(&self, ext: &str) -> PathBuf {
        self.out_dir.join(format!("{}.{ext}", self.crate_stem))
    }
}

/// Opaque ongoing codegen handle, returned by `codegen_crate`.
///
/// This is the `Box<dyn Any>` returned by the rustc trait's `codegen_crate`
/// and consumed by `join_codegen`. We make it typed here for clarity.
#[derive(Debug)]
pub struct OngoingCodegen {
    /// Compiled modules accumulated during codegen.
    pub(crate) modules: Vec<CompiledModule>,
    /// Allocator module lowered separately from regular codegen units.
    pub(crate) allocator_module: Option<CompiledModule>,
    /// Rustc allocator shim intent attached before native lowering exists.
    pub(crate) allocator_module_spec: Option<AllocatorModuleSpec>,
    /// Functions that failed to compile (name + error).
    pub(crate) failures: Vec<(String, String)>,
    /// Crate name being compiled.
    pub(crate) crate_name: String,
    /// Translation validation results collected during lowering.
    #[cfg(feature = "transval")]
    pub(crate) validation_results: Vec<crate::transval::LoweringValidationResult>,
}

impl OngoingCodegen {
    /// The name of the crate being compiled.
    #[must_use]
    pub fn crate_name(&self) -> &str {
        &self.crate_name
    }

    /// Number of successfully compiled functions.
    #[must_use]
    pub fn compiled_count(&self) -> usize {
        self.modules.iter().map(|m| m.function_count).sum::<usize>()
            + self.allocator_module.as_ref().map_or(0, |module| module.function_count)
    }

    /// Number of functions that failed to compile.
    #[must_use]
    pub fn failure_count(&self) -> usize {
        self.failures.len()
    }

    /// Allocator module lowered for this crate, if any.
    #[must_use]
    pub fn allocator_module(&self) -> Option<&CompiledModule> {
        self.allocator_module.as_ref()
    }

    /// Allocator module intent attached for later native lowering.
    #[must_use]
    pub fn allocator_module_spec(&self) -> Option<&AllocatorModuleSpec> {
        self.allocator_module_spec.as_ref()
    }

    /// Translation validation results produced during lowering.
    #[cfg(feature = "transval")]
    #[must_use]
    pub fn validation_results(&self) -> &[crate::transval::LoweringValidationResult] {
        &self.validation_results
    }
}

/// Work product tracking, mirrors `rustc_middle::dep_graph::WorkProduct`.
#[derive(Debug, Clone)]
pub struct WorkProduct {
    /// Path to the saved work product file.
    pub saved_file: PathBuf,
}

/// One object artifact emitted from a bridge compiled module.
#[derive(Debug, Clone)]
pub struct EmittedObject {
    /// Stable artifact name used for the object file path.
    pub artifact_name: String,
    /// Human-readable function name for diagnostics.
    pub source_name: String,
    /// Serialized object file bytes.
    pub bytes: Vec<u8>,
}

// ---------------------------------------------------------------------------
// The trait (mirrors rustc_codegen_ssa::traits::CodegenBackend)
// ---------------------------------------------------------------------------

/// Trait mirroring `rustc_codegen_ssa::traits::CodegenBackend`.
///
/// This is the interface that a codegen backend must implement to be usable
/// by the rustc compilation pipeline. Our types stand in for rustc's
/// `Session`, `TyCtxt`, etc.
///
/// When the compiler plugin adapter is built (in `compiler/rustc_codegen_llvm2/`),
/// it will implement the real rustc trait by delegating to this one.
// tRust: CodegenBackend scaffold for LLVM2 integration (#829).
pub trait RustcCodegenBackend {
    /// Human-readable name (e.g., "llvm2").
    fn name(&self) -> &'static str;

    /// Initialize the backend. Called once before codegen.
    fn init(&self) -> Result<(), CodegenBackendError> {
        Ok(())
    }

    /// Return target-specific configuration.
    fn target_config(&self) -> TargetConfig {
        TargetConfig::default()
    }

    /// Return the target CPU string.
    fn target_cpu(&self) -> String;

    /// Whether ThinLTO is supported.
    fn thin_lto_supported(&self) -> bool {
        false // LLVM2 does not implement LTO.
    }

    /// Whether zstd compression is available.
    fn has_zstd(&self) -> bool {
        false
    }

    /// Compile all functions in a crate, returning an opaque handle.
    ///
    /// Mirrors `codegen_crate(&self, tcx: TyCtxt, crate_info: &CrateInfo) -> Box<dyn Any>`.
    fn codegen_crate(&self, crate_info: &CrateInfo) -> Result<Box<dyn Any>, CodegenBackendError>;

    /// Finalize codegen: join threads, collect results.
    ///
    /// Mirrors `join_codegen(&self, ongoing: Box<dyn Any>, ...) -> (CompiledModules, ...)`.
    fn join_codegen(
        &self,
        ongoing: Box<dyn Any>,
        outputs: &OutputFilenames,
    ) -> Result<(CompiledModules, Vec<WorkProduct>), CodegenBackendError>;

    /// Link compiled modules into a final binary.
    fn link(
        &self,
        compiled: &CompiledModules,
        outputs: &OutputFilenames,
    ) -> Result<PathBuf, CodegenBackendError>;

    /// Supported crate types.
    fn supported_crate_types(&self) -> Vec<&'static str> {
        vec!["bin", "rlib", "staticlib"]
    }

    /// Print backend version info.
    fn print_version(&self) {}

    /// Print pass timing statistics.
    fn print_pass_timings(&self) {}

    /// Print general statistics.
    fn print_statistics(&self) {}
}

// ---------------------------------------------------------------------------
// LLVM2 implementation
// ---------------------------------------------------------------------------

/// LLVM2 codegen backend implementing `RustcCodegenBackend`.
///
/// This is the struct that will back the rustc `CodegenBackend` trait
/// implementation when the compiler plugin is wired.
// tRust: CodegenBackend scaffold for LLVM2 integration (#829).
#[derive(Debug, Clone)]
pub struct Llvm2CodegenBackend {
    /// Target architecture.
    target_arch: Llvm2TargetArch,
}

/// Target architectures supported by LLVM2.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Llvm2TargetArch {
    /// AArch64 (Apple Silicon, ARM64).
    AArch64,
    /// x86-64.
    X86_64,
}

impl Llvm2TargetArch {
    /// Map a rustc target architecture string to an LLVM2 target.
    #[must_use]
    pub fn from_rustc_arch(target_arch: &str) -> Option<Self> {
        match target_arch {
            "aarch64" => Some(Self::AArch64),
            "x86_64" => Some(Self::X86_64),
            _ => None,
        }
    }

    /// Auto-detect from compile-time target.
    #[must_use]
    pub fn host() -> Self {
        if cfg!(target_arch = "aarch64") { Self::AArch64 } else { Self::X86_64 }
    }

    /// Return the target CPU string for this architecture.
    #[must_use]
    fn cpu_string(self) -> &'static str {
        match self {
            Self::AArch64 => "generic",
            Self::X86_64 => "generic",
        }
    }

    /// Return the target triple.
    #[must_use]
    pub fn triple(self) -> &'static str {
        match self {
            Self::AArch64 => "aarch64-unknown-linux-gnu",
            Self::X86_64 => "x86_64-unknown-linux-gnu",
        }
    }
}

impl Llvm2CodegenBackend {
    /// Create a new LLVM2 codegen backend for the given target.
    #[must_use]
    pub fn new(target_arch: Llvm2TargetArch) -> Self {
        Self { target_arch }
    }

    /// Create a backend targeting the host architecture.
    #[must_use]
    pub fn host() -> Self {
        Self::new(Llvm2TargetArch::host())
    }

    /// Lower a single function through the bridge, returning the LIR.
    pub fn lower_function(
        &self,
        func: &VerifiableFunction,
    ) -> Result<LirFunction, CodegenBackendError> {
        Ok(lower_to_lir(func)?)
    }

    /// Lower a single function and validate that the lowering preserves semantics.
    ///
    /// When the `transval` feature is enabled, this performs:
    /// 1. MIR -> LIR lowering via `lower_to_lir`
    /// 2. LIR -> MIR lift-back via `lift_from_lir`
    /// 3. Structural refinement check (return type, arg count, block structure)
    ///
    /// Without the `transval` feature, this is equivalent to `lower_function`.
    pub fn lower_function_validated(
        &self,
        func: &VerifiableFunction,
    ) -> Result<LirFunction, CodegenBackendError> {
        let lir = lower_to_lir(func)?;

        #[cfg(feature = "transval")]
        {
            // tRust: #823 — run translation validation on the lowered LIR.
            use crate::transval::validate_lowering_with_lir;
            if let Err(e) = validate_lowering_with_lir(func, &lir) {
                return Err(CodegenBackendError::CodegenUnitFailed {
                    unit_name: func.name.clone(),
                    reason: format!("translation validation failed: {e}"),
                });
            }
        }

        Ok(lir)
    }

    /// Lower a batch of `VerifiableFunction`s into LIR, returning one
    /// `LirFunction` per input. Failures are collected per-function so that
    /// a single bad function does not prevent the rest from lowering.
    ///
    /// This is the module-level entry point that `codegen_crate` delegates to
    /// internally. Exposing it separately lets callers operate at the
    /// function-batch granularity without the full crate pipeline.
    pub fn lower_module(
        &self,
        functions: &[VerifiableFunction],
    ) -> Result<Vec<LirFunction>, CodegenBackendError> {
        let mut lir_fns = Vec::with_capacity(functions.len());
        let mut failures: Vec<(String, String)> = Vec::new();

        for func in functions {
            match self.lower_function(func) {
                Ok(lir) => lir_fns.push(lir),
                Err(e) => failures.push((func.name.clone(), e.to_string())),
            }
        }

        if failures.is_empty() {
            Ok(lir_fns)
        } else {
            let summary: String = failures
                .iter()
                .map(|(name, err)| format!("  {name}: {err}"))
                .collect::<Vec<_>>()
                .join("\n");
            Err(CodegenBackendError::CodegenUnitFailed {
                unit_name: "module".to_string(),
                reason: format!("{} function(s) failed to lower:\n{summary}", failures.len()),
            })
        }
    }

    /// Run scaffold optimizations on a single `LirFunction`.
    ///
    /// Currently performs dead-block elimination: removes blocks that are not
    /// reachable from the entry block. When LLVM2's `llvm2-opt` crate is wired
    /// as a dependency, this will delegate to its full pass pipeline (DCE, GVN,
    /// copy propagation, etc.).
    pub fn optimize(&self, func: &mut LirFunction) -> Result<(), CodegenBackendError> {
        // Scaffold: dead-block elimination.
        // Walk reachable blocks from entry via BFS.
        use std::collections::{HashSet, VecDeque};

        let mut reachable = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(func.entry_block);
        reachable.insert(func.entry_block);

        while let Some(block) = queue.pop_front() {
            if let Some(bb) = func.blocks.get(&block) {
                for instr in &bb.instructions {
                    for target in Self::branch_targets(&instr.opcode) {
                        if reachable.insert(target) {
                            queue.push_back(target);
                        }
                    }
                }
            }
        }

        // Remove unreachable blocks.
        func.blocks.retain(|blk, _| reachable.contains(blk));

        Ok(())
    }

    /// Collect all branch target blocks from an opcode.
    fn branch_targets(opcode: &Opcode) -> Vec<Block> {
        match opcode {
            Opcode::Jump { dest } => vec![*dest],
            Opcode::Brif { then_dest, else_dest, .. } => {
                vec![*then_dest, *else_dest]
            }
            Opcode::Switch { cases, default } => {
                let mut targets: Vec<Block> = cases.iter().map(|(_, blk)| *blk).collect();
                targets.push(*default);
                targets
            }
            Opcode::Invoke { normal_dest, unwind_dest, .. } => {
                vec![*normal_dest, *unwind_dest]
            }
            _ => Vec::new(),
        }
    }

    /// Emit a real object file for a single-function module.
    ///
    /// On Apple targets this uses the local Mach-O writer so named call
    /// relocations remain linkable; elsewhere it delegates to
    /// `llvm2_codegen::pipeline::compile_to_object`.
    pub fn emit_object(&self, module: &[LirFunction]) -> Result<Vec<u8>, CodegenBackendError> {
        if module.is_empty() {
            return Err(CodegenBackendError::EmitFailed {
                reason: "empty module: no functions to emit".to_string(),
            });
        }

        if module.len() > 1 {
            return Err(CodegenBackendError::EmitFailed {
                reason: "multi-function modules not yet supported by llvm2-codegen path; call emit_objects".to_string(),
            });
        }

        if cfg!(target_vendor = "apple") {
            self.emit_macho_object(module)
        } else {
            llvm2_codegen::pipeline::compile_to_object(
                &module[0],
                llvm2_codegen::pipeline::OptLevel::O0,
            )
            .map_err(|e| CodegenBackendError::Pipeline {
                func_name: module[0].name.clone(),
                reason: e.to_string(),
            })
        }
    }

    /// Emit one object file per function.
    ///
    /// On Apple targets this mirrors [`emit_object`] for each function so
    /// cross-object call sites keep their external Mach-O relocations.
    pub fn emit_objects(
        &self,
        module: &[LirFunction],
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenBackendError> {
        if module.is_empty() {
            return Err(CodegenBackendError::EmitFailed {
                reason: "empty module: no functions to emit".to_string(),
            });
        }

        module
            .iter()
            .map(|func| {
                if cfg!(target_vendor = "apple") {
                    self.emit_macho_object(std::slice::from_ref(func))
                } else {
                    llvm2_codegen::pipeline::compile_to_object(
                        func,
                        llvm2_codegen::pipeline::OptLevel::O0,
                    )
                    .map_err(|e| CodegenBackendError::Pipeline {
                        func_name: func.name.clone(),
                        reason: e.to_string(),
                    })
                }
                .map(|bytes| (func.name.clone(), bytes))
            })
            .collect()
    }

    /// Emit the object files required for one compiled module.
    ///
    /// Single-function modules produce a single artifact named after the module.
    /// Multi-function modules are split into one object per function with stable
    /// artifact names derived from the module name and function index.
    pub fn emit_module_objects(
        &self,
        module: &CompiledModule,
    ) -> Result<Vec<EmittedObject>, CodegenBackendError> {
        match module.lir_functions.len() {
            0 => Ok(Vec::new()),
            1 => {
                let func = &module.lir_functions[0];
                self.emit_object(&module.lir_functions).map(|bytes| {
                    vec![EmittedObject {
                        artifact_name: module.name.clone(),
                        source_name: func.name.clone(),
                        bytes,
                    }]
                })
            }
            _ => self.emit_objects(&module.lir_functions).map(|objects| {
                objects
                    .into_iter()
                    .enumerate()
                    .map(|(index, (func_name, bytes))| EmittedObject {
                        artifact_name: format!("{}.f{index}", module.name),
                        source_name: func_name,
                        bytes,
                    })
                    .collect()
            }),
        }
    }

    fn allocator_arg_types(kind: AllocatorArgKind) -> Vec<LirType> {
        match kind {
            // The bridge targets 64-bit architectures today, so rustc's
            // `(size, align)` layout pair and usize/pointer values lower to I64s.
            AllocatorArgKind::Layout => vec![LirType::I64, LirType::I64],
            AllocatorArgKind::Ptr | AllocatorArgKind::Usize => vec![LirType::I64],
        }
    }

    fn allocator_result_types(kind: AllocatorResultKind) -> Vec<LirType> {
        match kind {
            AllocatorResultKind::Never | AllocatorResultKind::Unit => Vec::new(),
            AllocatorResultKind::ResultPtr => vec![LirType::I64],
        }
    }

    fn allocator_wrapper_from_spec(spec: &AllocatorFunctionSpec) -> LirFunction {
        let param_types =
            spec.inputs.iter().copied().flat_map(Self::allocator_arg_types).collect::<Vec<_>>();
        let result_types = Self::allocator_result_types(spec.output);
        let param_count = param_types.len() as u32;
        let call_result = (!result_types.is_empty()).then_some(Value(param_count));

        let mut function = LirFunction::new(
            spec.wrapper_symbol_name.clone(),
            LirSignature { params: param_types, returns: result_types.clone() },
        );
        if let Some(result) = call_result {
            function.value_types.insert(result, result_types[0].clone());
        }

        let mut entry = LirBasicBlock::default();
        entry.instructions.push(LirInstruction {
            opcode: Opcode::Call { name: spec.callee_symbol_name.clone() },
            args: (0..param_count).map(Value).collect(),
            results: call_result.into_iter().collect(),
        });
        if spec.output != AllocatorResultKind::Never {
            entry.instructions.push(LirInstruction {
                opcode: Opcode::Return,
                args: call_result.into_iter().collect(),
                results: vec![],
            });
        }

        function.blocks.insert(Block(0), entry);
        function
    }

    fn allocator_marker_function(symbol_name: &str) -> LirFunction {
        let mut function = LirFunction::new(symbol_name.to_string(), LirSignature::default());
        let mut entry = LirBasicBlock::default();
        entry.instructions.push(LirInstruction {
            opcode: Opcode::Return,
            args: vec![],
            results: vec![],
        });
        function.blocks.insert(Block(0), entry);
        function
    }

    fn allocator_module_from_spec(
        spec: &AllocatorModuleSpec,
    ) -> Result<CompiledModule, CodegenBackendError> {
        let mut lir_functions =
            spec.functions.iter().map(Self::allocator_wrapper_from_spec).collect::<Vec<_>>();
        if let Some(symbol_name) = &spec.no_alloc_shim_is_unstable_symbol_name {
            lir_functions.push(Self::allocator_marker_function(symbol_name));
        }

        Ok(CompiledModule {
            name: spec.module_name.clone(),
            function_count: lir_functions.len(),
            lir_functions,
            object_path: None,
        })
    }

    /// Emit a Mach-O object while preserving named-call relocations.
    fn emit_macho_object(&self, functions: &[LirFunction]) -> Result<Vec<u8>, CodegenBackendError> {
        let pipeline =
            llvm2_codegen::pipeline::Pipeline::new(llvm2_codegen::pipeline::PipelineConfig {
                opt_level: llvm2_codegen::pipeline::OptLevel::O0,
                ..Default::default()
            });

        let mut prepared = Vec::with_capacity(functions.len());
        for func in functions {
            prepared.push(pipeline.prepare_function(func).map_err(|e| {
                CodegenBackendError::Pipeline {
                    func_name: func.name.clone(),
                    reason: e.to_string(),
                }
            })?);
        }

        use llvm2_codegen::macho::{FixupTarget, MachOWriter};

        let estimated_code_size = prepared.len() * 100;
        let mut combined_code = Vec::with_capacity(estimated_code_size);
        let mut combined_fixups = llvm2_codegen::macho::FixupList::new();
        let mut func_offsets: Vec<(String, u64)> = Vec::with_capacity(prepared.len());

        for func in &prepared {
            let func_start = combined_code.len() as u64;
            func_offsets.push((func.name.clone(), func_start));

            let (code, fixups) = llvm2_codegen::pipeline::encode_function_with_fixups(func)
                .map_err(|e| CodegenBackendError::EmitFailed { reason: e.to_string() })?;

            for fixup in fixups.iter() {
                let mut adjusted = fixup.clone();
                adjusted.offset += func_start as u32;
                combined_fixups.push(adjusted);
            }

            combined_code.extend_from_slice(&code);
        }

        let mut writer = MachOWriter::new();
        writer.add_text_section(&combined_code);

        let mut symbol_map: HashMap<String, u32> = HashMap::new();
        let mut next_symbol_index = 0u32;
        for (name, offset) in func_offsets {
            let symbol_name = format!("_{}", name);
            writer.add_symbol(&symbol_name, 1, offset, true);
            symbol_map.insert(name, next_symbol_index);
            symbol_map.insert(symbol_name, next_symbol_index);
            next_symbol_index += 1;
        }

        let external_names = combined_fixups
            .iter()
            .filter_map(|fixup| match &fixup.target {
                FixupTarget::NamedSymbol(name) if !symbol_map.contains_key(name) => {
                    Some(name.clone())
                }
                _ => None,
            })
            .collect::<BTreeSet<_>>();

        for name in external_names {
            let symbol_name = format!("_{}", name);
            writer.add_symbol(&symbol_name, 0, 0, true);
            symbol_map.insert(name, next_symbol_index);
            symbol_map.insert(symbol_name, next_symbol_index);
            next_symbol_index += 1;
        }

        combined_fixups
            .resolve_named_symbols(|name| symbol_map.get(name).copied())
            .map_err(|e| CodegenBackendError::EmitFailed { reason: e.to_string() })?;

        for reloc in combined_fixups
            .resolve_to_relocations()
            .map_err(|e| CodegenBackendError::EmitFailed { reason: e.to_string() })?
        {
            writer.add_relocation(0, reloc);
        }

        Ok(writer.write())
    }

    /// Emit a single allocator object, preserving cross-wrapper and external
    /// call relocations in one Mach-O artifact.
    pub fn emit_allocator_module_object(
        &self,
        module: &CompiledModule,
    ) -> Result<Option<EmittedObject>, CodegenBackendError> {
        if module.lir_functions.is_empty() {
            return Ok(None);
        }

        let bytes = self.emit_macho_object(&module.lir_functions)?;
        Ok(Some(EmittedObject {
            artifact_name: module.name.clone(),
            source_name: module.name.clone(),
            bytes,
        }))
    }

    /// Stable module name used for allocator shim codegen.
    #[must_use]
    pub fn allocator_module_name(crate_name: &str) -> String {
        format!("{crate_name}.allocator")
    }

    /// Lower allocator functions into a dedicated compiled module.
    ///
    /// This is a bridge-side scaffold for future allocator shim plumbing:
    /// callers can lower allocator functions independently of the main crate
    /// CGU and later attach the resulting module to an `OngoingCodegen`.
    pub fn lower_allocator_module(
        &self,
        crate_name: &str,
        functions: &[VerifiableFunction],
    ) -> Result<Option<CompiledModule>, CodegenBackendError> {
        if functions.is_empty() {
            return Ok(None);
        }

        let module_name = Self::allocator_module_name(crate_name);
        let mut lir_functions = Vec::with_capacity(functions.len());
        let mut failures = Vec::new();

        for func in functions {
            #[cfg(feature = "transval")]
            let lowered = self.lower_function_validated(func);
            #[cfg(not(feature = "transval"))]
            let lowered = self.lower_function(func);

            match lowered {
                Ok(lir) => lir_functions.push(lir),
                Err(e) => failures.push((func.name.clone(), e.to_string())),
            }
        }

        if !failures.is_empty() {
            let summary = failures
                .iter()
                .map(|(name, err)| format!("  {name}: {err}"))
                .collect::<Vec<_>>()
                .join("\n");
            return Err(CodegenBackendError::CodegenUnitFailed {
                unit_name: module_name,
                reason: format!(
                    "{} allocator function(s) failed to lower:\n{summary}",
                    failures.len()
                ),
            });
        }

        let function_count = lir_functions.len();
        Ok(Some(CompiledModule {
            name: Self::allocator_module_name(crate_name),
            lir_functions,
            object_path: None,
            function_count,
        }))
    }

    /// Attach a lowered allocator module to an in-flight codegen result.
    ///
    /// Future callers can use this to preserve allocator shims as a distinct
    /// module without changing the regular crate codegen path.
    pub fn attach_allocator_module(
        &self,
        ongoing: &mut dyn Any,
        allocator_module: CompiledModule,
    ) -> Result<(), CodegenBackendError> {
        let ongoing = ongoing.downcast_mut::<OngoingCodegen>().ok_or_else(|| {
            CodegenBackendError::JoinFailed {
                reason: "ongoing codegen has wrong type (not OngoingCodegen)".to_string(),
            }
        })?;
        ongoing.allocator_module = Some(allocator_module);
        Ok(())
    }

    /// Attach allocator shim intent to an in-flight codegen result.
    ///
    /// This lets rustc-side planning hand bridge-native allocator metadata down
    /// so `join_codegen` can synthesize native allocator wrapper LIR later.
    pub fn attach_allocator_module_spec(
        &self,
        ongoing: &mut dyn Any,
        allocator_module_spec: AllocatorModuleSpec,
    ) -> Result<(), CodegenBackendError> {
        let ongoing = ongoing.downcast_mut::<OngoingCodegen>().ok_or_else(|| {
            CodegenBackendError::JoinFailed {
                reason: "ongoing codegen has wrong type (not OngoingCodegen)".to_string(),
            }
        })?;
        ongoing.allocator_module_spec = Some(allocator_module_spec);
        Ok(())
    }

    /// Validate that a batch of lowered LIR functions preserves the semantics of
    /// their source `VerifiableFunction`s.
    ///
    /// Performs a per-function structural refinement check (return type, arg count,
    /// block structure) by lifting each LIR back to MIR and comparing with the source.
    ///
    /// This is the integration point that wires the `transval` module into the
    /// codegen pipeline: lower -> validate -> report.
    ///
    /// Requires the `transval` feature.
    #[cfg(feature = "transval")]
    pub fn validate_lowering_result(
        &self,
        funcs: &[VerifiableFunction],
        lir_fns: &[LirFunction],
    ) -> Vec<crate::transval::LoweringValidationResult> {
        funcs
            .iter()
            .zip(lir_fns.iter())
            .map(|(src, lir)| {
                match crate::transval::validate_lowering_with_lir(src, lir) {
                    Ok(result) => result,
                    Err(e) => {
                        // If validation itself fails (e.g., lift-back error),
                        // produce a result with Unknown verdict.
                        crate::transval::LoweringValidationResult {
                            function_name: src.name.clone(),
                            verdict: crate::transval::LoweringVerdict::Unknown {
                                reason: format!("validation error: {e}"),
                            },
                            checks: vec![],
                            checks_total: 0,
                            checks_passed: 0,
                        }
                    }
                }
            })
            .collect()
    }

    /// The target architecture this backend is configured for.
    #[must_use]
    pub fn target_arch(&self) -> Llvm2TargetArch {
        self.target_arch
    }

    /// Whether this backend emits real machine code objects.
    #[must_use]
    pub fn real_machine_code(&self) -> bool {
        true
    }
}

impl Default for Llvm2CodegenBackend {
    fn default() -> Self {
        Self::host()
    }
}

impl RustcCodegenBackend for Llvm2CodegenBackend {
    fn name(&self) -> &'static str {
        "llvm2"
    }

    fn target_cpu(&self) -> String {
        self.target_arch.cpu_string().to_string()
    }

    fn target_config(&self) -> TargetConfig {
        TargetConfig {
            target_features: match self.target_arch {
                Llvm2TargetArch::AArch64 => vec!["neon".to_string()],
                Llvm2TargetArch::X86_64 => vec!["sse2".to_string()],
            },
            // LLVM2 does not yet support extended float types.
            has_reliable_f16: false,
            has_reliable_f16_math: false,
            has_reliable_f128: false,
            has_reliable_f128_math: false,
            ..TargetConfig::default()
        }
    }

    fn codegen_crate(&self, crate_info: &CrateInfo) -> Result<Box<dyn Any>, CodegenBackendError> {
        let mut modules = Vec::new();
        let mut failures = Vec::new();

        // Group all functions into a single codegen unit for now.
        // Real implementation will partition by CGU name from TyCtxt.
        let mut lir_functions = Vec::with_capacity(crate_info.functions.len());
        #[cfg(feature = "transval")]
        let mut lowered_functions = Vec::with_capacity(crate_info.functions.len());

        for func in &crate_info.functions {
            #[cfg(feature = "transval")]
            let lowered = self.lower_function_validated(func);
            #[cfg(not(feature = "transval"))]
            let lowered = self.lower_function(func);

            match lowered {
                Ok(lir) => {
                    #[cfg(feature = "transval")]
                    lowered_functions.push(func.clone());
                    lir_functions.push(lir);
                }
                Err(e) => failures.push((func.name.clone(), e.to_string())),
            }
        }

        #[cfg(feature = "transval")]
        let validation_results = self.validate_lowering_result(&lowered_functions, &lir_functions);

        let function_count = lir_functions.len();
        modules.push(CompiledModule {
            name: format!("{}.codegen_unit.0", crate_info.crate_name),
            lir_functions,
            object_path: None,
            function_count,
        });

        Ok(Box::new(OngoingCodegen {
            modules,
            allocator_module: None,
            allocator_module_spec: None,
            failures,
            crate_name: crate_info.crate_name.clone(),
            #[cfg(feature = "transval")]
            validation_results,
        }))
    }

    fn join_codegen(
        &self,
        ongoing: Box<dyn Any>,
        _outputs: &OutputFilenames,
    ) -> Result<(CompiledModules, Vec<WorkProduct>), CodegenBackendError> {
        let ongoing =
            ongoing.downcast::<OngoingCodegen>().map_err(|_| CodegenBackendError::JoinFailed {
                reason: "ongoing codegen has wrong type (not OngoingCodegen)".to_string(),
            })?;

        #[cfg(feature = "transval")]
        let validation_warning = {
            let validation_failures: Vec<String> = ongoing
                .validation_results()
                .iter()
                .filter(|result| !result.is_valid())
                .map(|result| match &result.verdict {
                    crate::transval::LoweringVerdict::Mismatch { expected, found } => {
                        format!("  {}: expected {expected}, found {found}", result.function_name)
                    }
                    crate::transval::LoweringVerdict::Unknown { reason } => {
                        format!("  {}: {reason}", result.function_name)
                    }
                    crate::transval::LoweringVerdict::Validated => unreachable!(),
                })
                .collect();

            (!validation_failures.is_empty()).then(|| {
                format!(
                    "warning: translation validation reported {} issue(s):\n{}",
                    validation_failures.len(),
                    validation_failures.join("\n")
                )
            })
        };

        if !ongoing.failures.is_empty() {
            let failure_summary: Vec<String> =
                ongoing.failures.iter().map(|(name, err)| format!("  {name}: {err}")).collect();
            return Err(CodegenBackendError::JoinFailed {
                reason: format!(
                    "{} function(s) failed to compile:\n{}",
                    ongoing.failures.len(),
                    failure_summary.join("\n")
                ),
            });
        }

        #[cfg(feature = "transval")]
        if let Some(warning) = validation_warning {
            eprintln!("{warning}");
        }

        let OngoingCodegen {
            modules,
            allocator_module,
            allocator_module_spec,
            failures: _,
            crate_name: _,
            #[cfg(feature = "transval")]
                validation_results: _,
        } = *ongoing;

        let allocator_module = match (allocator_module, allocator_module_spec) {
            (Some(module), _) => Some(module),
            (None, Some(spec)) => Some(Self::allocator_module_from_spec(&spec)?),
            (None, None) => None,
        };

        let compiled = CompiledModules { modules, allocator_module };

        // No incremental work products in the scaffold.
        Ok((compiled, Vec::new()))
    }

    fn link(
        &self,
        compiled: &CompiledModules,
        outputs: &OutputFilenames,
    ) -> Result<PathBuf, CodegenBackendError> {
        // Scaffold: report what would be linked but don't produce a real binary.
        // The real implementation will invoke llvm2-codegen target pipelines.
        let total_functions: usize = compiled.modules.iter().map(|m| m.function_count).sum();

        let output_path = outputs.object_path("o");

        if total_functions == 0 {
            return Err(CodegenBackendError::LinkFailed {
                reason: "no functions to link".to_string(),
            });
        }

        // In the scaffold, we just return the path that would be produced.
        // Real implementation: llvm2-codegen emits object files, then we link.
        Ok(output_path)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use trust_types::{
        BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
        Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    /// Build `add(a: i32, b: i32) -> i32` for testing.
    fn make_add() -> VerifiableFunction {
        VerifiableFunction {
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
        }
    }

    /// Build `identity(x: i64) -> i64` -- single arg, single block.
    fn make_identity() -> VerifiableFunction {
        VerifiableFunction {
            name: "identity".to_string(),
            def_path: "test::identity".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i64(), name: None },
                    LocalDecl { index: 1, ty: Ty::i64(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i64(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn make_allocator_spec(module_name: &str) -> AllocatorModuleSpec {
        AllocatorModuleSpec {
            module_name: module_name.to_string(),
            functions: vec![
                AllocatorFunctionSpec {
                    name: "alloc".to_string(),
                    wrapper_symbol_name: "_Rshim_alloc".to_string(),
                    callee_symbol_name: "_Rdefault_alloc".to_string(),
                    kind: AllocatorFunctionKind::Alloc,
                    inputs: vec![AllocatorArgKind::Layout],
                    output: AllocatorResultKind::ResultPtr,
                },
                AllocatorFunctionSpec {
                    name: "alloc_error_handler".to_string(),
                    wrapper_symbol_name: "_Rshim_alloc_error_handler".to_string(),
                    callee_symbol_name: "_Rdefault_alloc_error_handler".to_string(),
                    kind: AllocatorFunctionKind::AllocErrorHandler,
                    inputs: vec![AllocatorArgKind::Layout],
                    output: AllocatorResultKind::Never,
                },
            ],
            no_alloc_shim_is_unstable_symbol_name: Some("_Rshim_no_alloc_marker".to_string()),
        }
    }

    fn make_shared_callee_allocator_spec(module_name: &str) -> AllocatorModuleSpec {
        AllocatorModuleSpec {
            module_name: module_name.to_string(),
            functions: vec![
                AllocatorFunctionSpec {
                    name: "alloc".to_string(),
                    wrapper_symbol_name: "_Rshim_alloc".to_string(),
                    callee_symbol_name: "_Rshared_alloc".to_string(),
                    kind: AllocatorFunctionKind::Alloc,
                    inputs: vec![AllocatorArgKind::Layout],
                    output: AllocatorResultKind::ResultPtr,
                },
                AllocatorFunctionSpec {
                    name: "alloc_zeroed".to_string(),
                    wrapper_symbol_name: "_Rshim_alloc_zeroed".to_string(),
                    callee_symbol_name: "_Rshared_alloc".to_string(),
                    kind: AllocatorFunctionKind::AllocZeroed,
                    inputs: vec![AllocatorArgKind::Layout],
                    output: AllocatorResultKind::ResultPtr,
                },
            ],
            no_alloc_shim_is_unstable_symbol_name: Some("_Rshim_no_alloc_marker".to_string()),
        }
    }

    fn make_internal_call_module(module_name: &str) -> CompiledModule {
        let mut caller = LirFunction::new("_Rshim_caller".to_string(), LirSignature::default());
        let mut caller_entry = LirBasicBlock::default();
        caller_entry.instructions.push(LirInstruction {
            opcode: Opcode::Call { name: "_Rshim_callee".to_string() },
            args: vec![],
            results: vec![],
        });
        caller_entry.instructions.push(LirInstruction {
            opcode: Opcode::Return,
            args: vec![],
            results: vec![],
        });
        caller.blocks.insert(Block(0), caller_entry);

        let mut callee = LirFunction::new("_Rshim_callee".to_string(), LirSignature::default());
        let mut callee_entry = LirBasicBlock::default();
        callee_entry.instructions.push(LirInstruction {
            opcode: Opcode::Return,
            args: vec![],
            results: vec![],
        });
        callee.blocks.insert(Block(0), callee_entry);

        CompiledModule {
            name: module_name.to_string(),
            function_count: 2,
            lir_functions: vec![caller, callee],
            object_path: None,
        }
    }

    fn read_u32(bytes: &[u8], offset: usize) -> u32 {
        u32::from_le_bytes(bytes[offset..offset + 4].try_into().expect("u32 should fit"))
    }

    fn mach_o_symbols(bytes: &[u8]) -> Vec<(String, llvm2_codegen::macho::NList64)> {
        const MACH_HEADER_64_SIZE: usize = 32;
        const LC_SYMTAB: u32 = 0x02;
        const NLIST_64_SIZE: usize = 16;

        let ncmds = read_u32(bytes, 16) as usize;
        let mut command_offset = MACH_HEADER_64_SIZE;
        let mut symtab = None;

        for _ in 0..ncmds {
            let cmd = read_u32(bytes, command_offset);
            let cmdsize = read_u32(bytes, command_offset + 4) as usize;
            if cmd == LC_SYMTAB {
                symtab = Some((
                    read_u32(bytes, command_offset + 8) as usize,
                    read_u32(bytes, command_offset + 12) as usize,
                    read_u32(bytes, command_offset + 16) as usize,
                ));
                break;
            }
            command_offset += cmdsize;
        }

        let (symoff, nsyms, stroff) = symtab.expect("Mach-O object should contain LC_SYMTAB");
        (0..nsyms)
            .map(|index| {
                let entry_offset = symoff + index * NLIST_64_SIZE;
                let entry = llvm2_codegen::macho::NList64::decode(
                    bytes[entry_offset..entry_offset + NLIST_64_SIZE]
                        .try_into()
                        .expect("nlist_64 entry should be 16 bytes"),
                );
                let name_offset = stroff + entry.strx as usize;
                let name_end = bytes[name_offset..]
                    .iter()
                    .position(|&byte| byte == 0)
                    .expect("symbol name should be NUL-terminated")
                    + name_offset;
                let name = std::str::from_utf8(&bytes[name_offset..name_end])
                    .expect("symbol names should be UTF-8")
                    .to_string();
                (name, entry)
            })
            .collect()
    }

    #[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
    fn mach_o_name(bytes: &[u8]) -> String {
        let end = bytes.iter().position(|&byte| byte == 0).unwrap_or(bytes.len());
        std::str::from_utf8(&bytes[..end]).expect("Mach-O names should be UTF-8").to_string()
    }

    #[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
    fn mach_o_text_relocations(bytes: &[u8]) -> Vec<llvm2_codegen::macho::Relocation> {
        const MACH_HEADER_64_SIZE: usize = 32;
        const LC_SEGMENT_64: u32 = 0x19;
        const SEGMENT_COMMAND_64_SIZE: usize = 72;
        const SECTION_64_SIZE: usize = 80;
        const RELOCATION_SIZE: usize = 8;

        let ncmds = read_u32(bytes, 16) as usize;
        let mut command_offset = MACH_HEADER_64_SIZE;

        for _ in 0..ncmds {
            let cmd = read_u32(bytes, command_offset);
            let cmdsize = read_u32(bytes, command_offset + 4) as usize;
            if cmd == LC_SEGMENT_64 {
                let nsects = read_u32(bytes, command_offset + 64) as usize;
                let mut section_offset = command_offset + SEGMENT_COMMAND_64_SIZE;
                for _ in 0..nsects {
                    let sectname = mach_o_name(&bytes[section_offset..section_offset + 16]);
                    let segname = mach_o_name(&bytes[section_offset + 16..section_offset + 32]);
                    if sectname == "__text" && segname == "__TEXT" {
                        let reloff = read_u32(bytes, section_offset + 56) as usize;
                        let nreloc = read_u32(bytes, section_offset + 60) as usize;
                        return (0..nreloc)
                            .map(|index| {
                                let entry_offset = reloff + index * RELOCATION_SIZE;
                                llvm2_codegen::macho::reloc::decode_relocation(
                                    bytes[entry_offset..entry_offset + RELOCATION_SIZE]
                                        .try_into()
                                        .expect("relocation entry should be 8 bytes"),
                                )
                                .expect("text relocation should decode")
                            })
                            .collect();
                    }
                    section_offset += SECTION_64_SIZE;
                }
            }
            command_offset += cmdsize;
        }

        panic!("Mach-O object should contain a __TEXT,__text section");
    }

    // -- Llvm2CodegenBackend basic tests --

    #[test]
    fn test_backend_name() {
        let backend = Llvm2CodegenBackend::host();
        assert_eq!(backend.name(), "llvm2");
    }

    #[test]
    fn test_backend_target_cpu() {
        let backend = Llvm2CodegenBackend::new(Llvm2TargetArch::AArch64);
        assert_eq!(backend.target_cpu(), "generic");
    }

    #[test]
    fn test_backend_target_config() {
        let backend = Llvm2CodegenBackend::new(Llvm2TargetArch::AArch64);
        let config = backend.target_config();
        assert!(config.target_features.contains(&"neon".to_string()));
        assert!(!config.has_reliable_f16);
    }

    #[test]
    fn test_backend_target_config_x86() {
        let backend = Llvm2CodegenBackend::new(Llvm2TargetArch::X86_64);
        let config = backend.target_config();
        assert!(config.target_features.contains(&"sse2".to_string()));
    }

    #[test]
    fn test_backend_thin_lto_not_supported() {
        let backend = Llvm2CodegenBackend::host();
        assert!(!backend.thin_lto_supported());
    }

    #[test]
    fn test_backend_default_is_host() {
        let backend = Llvm2CodegenBackend::default();
        assert_eq!(backend.target_arch(), Llvm2TargetArch::host());
    }

    #[test]
    fn test_backend_emits_real_machine_code() {
        let backend = Llvm2CodegenBackend::host();
        assert!(backend.real_machine_code());
    }

    #[test]
    fn test_target_arch_triple() {
        assert_eq!(Llvm2TargetArch::AArch64.triple(), "aarch64-unknown-linux-gnu");
        assert_eq!(Llvm2TargetArch::X86_64.triple(), "x86_64-unknown-linux-gnu");
    }

    #[test]
    fn test_target_arch_from_rustc_arch() {
        assert_eq!(Llvm2TargetArch::from_rustc_arch("aarch64"), Some(Llvm2TargetArch::AArch64));
        assert_eq!(Llvm2TargetArch::from_rustc_arch("x86_64"), Some(Llvm2TargetArch::X86_64));
        assert_eq!(Llvm2TargetArch::from_rustc_arch("riscv64"), None);
    }

    // -- lower_function tests --

    #[test]
    fn test_lower_function_add() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_add();
        let lir = backend.lower_function(&func).expect("should lower add function");
        assert_eq!(lir.name, "add");
        assert_eq!(lir.signature.params.len(), 2);
        assert_eq!(lir.signature.returns.len(), 1);
    }

    #[test]
    fn test_lower_function_identity() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_identity();
        let lir = backend.lower_function(&func).expect("should lower identity function");
        assert_eq!(lir.name, "identity");
        assert_eq!(lir.signature.params.len(), 1);
    }

    // -- RustcCodegenBackend trait tests --

    #[test]
    fn test_codegen_crate_single_function() {
        let backend = Llvm2CodegenBackend::host();
        let info = CrateInfo {
            target_cpu: "generic".to_string(),
            crate_name: "test_crate".to_string(),
            functions: vec![make_add()],
        };

        let ongoing = backend.codegen_crate(&info).expect("codegen_crate should succeed");

        // Verify the ongoing codegen can be downcast.
        let ongoing_ref =
            ongoing.downcast_ref::<OngoingCodegen>().expect("should be OngoingCodegen");
        assert_eq!(ongoing_ref.crate_name, "test_crate");
        assert_eq!(ongoing_ref.modules.len(), 1);
        assert_eq!(ongoing_ref.modules[0].function_count, 1);
        assert!(ongoing_ref.failures.is_empty());
    }

    #[test]
    fn test_codegen_crate_multiple_functions() {
        let backend = Llvm2CodegenBackend::host();
        let info = CrateInfo {
            target_cpu: "generic".to_string(),
            crate_name: "multi".to_string(),
            functions: vec![make_add(), make_identity()],
        };

        let ongoing = backend.codegen_crate(&info).expect("codegen_crate should succeed");

        let ongoing_ref =
            ongoing.downcast_ref::<OngoingCodegen>().expect("should be OngoingCodegen");
        assert_eq!(ongoing_ref.modules[0].function_count, 2);
        assert_eq!(ongoing_ref.modules[0].lir_functions.len(), 2);
    }

    #[test]
    fn test_codegen_crate_empty() {
        let backend = Llvm2CodegenBackend::host();
        let info = CrateInfo {
            target_cpu: "generic".to_string(),
            crate_name: "empty".to_string(),
            functions: vec![],
        };

        let ongoing = backend.codegen_crate(&info).expect("empty crate should succeed");

        let ongoing_ref =
            ongoing.downcast_ref::<OngoingCodegen>().expect("should be OngoingCodegen");
        assert_eq!(ongoing_ref.modules[0].function_count, 0);
    }

    #[test]
    fn test_join_codegen_success() {
        let backend = Llvm2CodegenBackend::host();
        let info = CrateInfo {
            target_cpu: "generic".to_string(),
            crate_name: "test".to_string(),
            functions: vec![make_add()],
        };
        let outputs =
            OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "test".to_string() };

        let ongoing = backend.codegen_crate(&info).expect("codegen should succeed");
        let (compiled, work_products) =
            backend.join_codegen(ongoing, &outputs).expect("join should succeed");

        assert_eq!(compiled.modules.len(), 1);
        assert_eq!(compiled.modules[0].function_count, 1);
        assert!(compiled.allocator_module.is_none());
        assert!(work_products.is_empty());
    }

    #[test]
    fn test_join_codegen_preserves_attached_allocator_module() {
        let backend = Llvm2CodegenBackend::host();
        let info = CrateInfo {
            target_cpu: "generic".to_string(),
            crate_name: "test".to_string(),
            functions: vec![make_add()],
        };
        let outputs =
            OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "test".to_string() };

        let mut ongoing = backend.codegen_crate(&info).expect("codegen should succeed");
        let allocator_module = backend
            .lower_allocator_module("test", &[make_identity()])
            .expect("allocator lowering should succeed")
            .expect("allocator module should be produced");
        let allocator_module_name = Llvm2CodegenBackend::allocator_module_name("test");

        backend
            .attach_allocator_module(ongoing.as_mut(), allocator_module)
            .expect("attach_allocator_module should accept OngoingCodegen");

        let ongoing_ref = ongoing.downcast_ref::<OngoingCodegen>().expect("should downcast");
        assert_eq!(ongoing_ref.compiled_count(), 2);
        assert_eq!(
            ongoing_ref.allocator_module().expect("allocator module should be attached").name,
            allocator_module_name
        );

        let (compiled, work_products) =
            backend.join_codegen(ongoing, &outputs).expect("join should succeed");

        let allocator_module =
            compiled.allocator_module.as_ref().expect("join should preserve allocator module");
        assert_eq!(allocator_module.name, allocator_module_name);
        assert_eq!(allocator_module.function_count, 1);
        assert!(work_products.is_empty());

        let emitted = backend
            .emit_module_objects(allocator_module)
            .expect("attached allocator module should emit object artifacts");
        assert_eq!(emitted.len(), 1);
        assert_eq!(emitted[0].artifact_name, allocator_module_name);
    }

    #[test]
    fn test_allocator_module_from_spec_builds_wrapper_lir_and_marker() {
        let module =
            Llvm2CodegenBackend::allocator_module_from_spec(&make_allocator_spec("test.allocator"))
                .expect("allocator spec lowering should succeed");

        assert_eq!(module.name, "test.allocator");
        assert_eq!(module.function_count, 3);
        assert_eq!(module.lir_functions.len(), 3);

        let alloc = &module.lir_functions[0];
        assert_eq!(alloc.name, "_Rshim_alloc");
        assert_eq!(alloc.signature.params, vec![LirType::I64, LirType::I64]);
        assert_eq!(alloc.signature.returns, vec![LirType::I64]);
        assert_eq!(alloc.value_types.get(&Value(2)), Some(&LirType::I64));
        let alloc_entry = alloc.blocks.get(&Block(0)).expect("wrapper should have an entry block");
        assert_eq!(alloc_entry.instructions.len(), 2);
        assert_eq!(
            alloc_entry.instructions[0],
            LirInstruction {
                opcode: Opcode::Call { name: "_Rdefault_alloc".to_string() },
                args: vec![Value(0), Value(1)],
                results: vec![Value(2)],
            }
        );
        assert_eq!(
            alloc_entry.instructions[1],
            LirInstruction { opcode: Opcode::Return, args: vec![Value(2)], results: vec![] }
        );

        let oom = &module.lir_functions[1];
        assert_eq!(oom.name, "_Rshim_alloc_error_handler");
        assert!(oom.signature.returns.is_empty());
        let oom_entry = oom.blocks.get(&Block(0)).expect("noreturn wrapper should have an entry");
        assert_eq!(oom_entry.instructions.len(), 1);
        assert_eq!(
            oom_entry.instructions[0],
            LirInstruction {
                opcode: Opcode::Call { name: "_Rdefault_alloc_error_handler".to_string() },
                args: vec![Value(0), Value(1)],
                results: vec![],
            }
        );

        let marker = &module.lir_functions[2];
        assert_eq!(marker.name, "_Rshim_no_alloc_marker");
        assert_eq!(marker.signature.params, Vec::<LirType>::new());
        assert_eq!(marker.signature.returns, Vec::<LirType>::new());
        let marker_entry =
            marker.blocks.get(&Block(0)).expect("marker function should have an entry");
        assert_eq!(
            marker_entry.instructions,
            vec![LirInstruction { opcode: Opcode::Return, args: vec![], results: vec![] }]
        );
    }

    #[test]
    fn test_emit_allocator_module_object_keeps_allocator_wrappers_in_one_artifact() {
        let backend = Llvm2CodegenBackend::host();
        let module =
            Llvm2CodegenBackend::allocator_module_from_spec(&make_allocator_spec("test.allocator"))
                .expect("allocator spec lowering should succeed");

        let emitted = backend
            .emit_allocator_module_object(&module)
            .expect("allocator emission should succeed")
            .expect("allocator module should produce one object");

        assert_eq!(emitted.artifact_name, "test.allocator");
        assert_eq!(emitted.source_name, "test.allocator");
        assert!(!emitted.bytes.is_empty());

        let symbols = mach_o_symbols(&emitted.bytes);
        #[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
        let branch26_relocations = mach_o_text_relocations(&emitted.bytes)
            .into_iter()
            .filter_map(|reloc| {
                matches!(reloc.kind, llvm2_codegen::macho::AArch64RelocKind::Branch26)
                    .then_some((reloc.pc_relative, reloc.is_extern))
            })
            .collect::<Vec<_>>();
        let defined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_defined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        let undefined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_undefined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();

        assert_eq!(
            defined,
            BTreeSet::from([
                "__Rshim_alloc".to_string(),
                "__Rshim_alloc_error_handler".to_string(),
                "__Rshim_no_alloc_marker".to_string(),
            ])
        );
        assert_eq!(
            undefined,
            BTreeSet::from([
                "__Rdefault_alloc".to_string(),
                "__Rdefault_alloc_error_handler".to_string(),
            ])
        );
        #[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
        assert_eq!(branch26_relocations, vec![(true, true), (true, true)]);
    }

    #[cfg(target_vendor = "apple")]
    #[test]
    fn test_emit_allocator_module_object_deduplicates_shared_external_callee_symbol() {
        let backend = Llvm2CodegenBackend::host();
        let module = Llvm2CodegenBackend::allocator_module_from_spec(
            &make_shared_callee_allocator_spec("test.shared_allocator"),
        )
        .expect("allocator spec lowering should succeed");

        let emitted = backend
            .emit_allocator_module_object(&module)
            .expect("allocator emission should succeed")
            .expect("allocator module should produce one object");

        assert_eq!(emitted.artifact_name, "test.shared_allocator");
        assert_eq!(emitted.source_name, "test.shared_allocator");

        let symbols = mach_o_symbols(&emitted.bytes);
        #[cfg(target_arch = "aarch64")]
        let branch26_relocations = mach_o_text_relocations(&emitted.bytes)
            .into_iter()
            .filter_map(|reloc| {
                matches!(reloc.kind, llvm2_codegen::macho::AArch64RelocKind::Branch26)
                    .then_some(reloc)
            })
            .collect::<Vec<_>>();
        let defined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_defined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        let undefined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_undefined())
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();

        assert_eq!(
            defined,
            BTreeSet::from([
                "__Rshim_alloc".to_string(),
                "__Rshim_alloc_zeroed".to_string(),
                "__Rshim_no_alloc_marker".to_string(),
            ])
        );
        assert_eq!(undefined, vec!["__Rshared_alloc".to_string()]);
        #[cfg(target_arch = "aarch64")]
        {
            let branch26_symbol_indices = branch26_relocations
                .iter()
                .map(|reloc| {
                    assert!(reloc.pc_relative);
                    assert!(reloc.is_extern);
                    reloc.symbol_index as usize
                })
                .collect::<Vec<_>>();
            assert_eq!(branch26_symbol_indices.len(), 2);

            let unique_branch26_symbol_indices =
                branch26_symbol_indices.iter().copied().collect::<BTreeSet<_>>();
            assert_eq!(unique_branch26_symbol_indices.len(), 1);

            let branch26_symbol_names = unique_branch26_symbol_indices
                .into_iter()
                .map(|index| {
                    symbols
                        .get(index)
                        .map(|(name, _)| name.clone())
                        .expect("branch relocation symbol index should resolve in the symtab")
                })
                .collect::<Vec<_>>();
            assert_eq!(branch26_symbol_names, vec!["__Rshared_alloc".to_string()]);
        }
    }

    #[cfg(target_vendor = "apple")]
    #[test]
    fn test_emit_allocator_module_object_preserves_defined_internal_call_relocation() {
        let backend = Llvm2CodegenBackend::host();
        let module = make_internal_call_module("test.internal_allocator");

        let emitted = backend
            .emit_allocator_module_object(&module)
            .expect("allocator emission should succeed")
            .expect("internal-call module should produce one object");

        assert_eq!(emitted.artifact_name, "test.internal_allocator");
        assert_eq!(emitted.source_name, "test.internal_allocator");

        let symbols = mach_o_symbols(&emitted.bytes);
        #[cfg(target_arch = "aarch64")]
        let branch26_relocations = mach_o_text_relocations(&emitted.bytes)
            .into_iter()
            .filter_map(|reloc| {
                matches!(reloc.kind, llvm2_codegen::macho::AArch64RelocKind::Branch26)
                    .then_some(reloc)
            })
            .collect::<Vec<_>>();
        let defined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_defined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        let undefined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_undefined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();

        assert_eq!(
            defined,
            BTreeSet::from(["__Rshim_callee".to_string(), "__Rshim_caller".to_string(),])
        );
        assert!(undefined.is_empty());
        #[cfg(target_arch = "aarch64")]
        {
            assert_eq!(branch26_relocations.len(), 1);
            assert!(branch26_relocations[0].pc_relative);
            assert!(branch26_relocations[0].is_extern);
            assert_eq!(
                symbols
                    .get(branch26_relocations[0].symbol_index as usize)
                    .map(|(name, _)| name.clone()),
                Some("__Rshim_callee".to_string())
            );
        }
    }

    #[cfg(target_vendor = "apple")]
    #[test]
    fn test_emit_object_preserves_undefined_external_call_symbol() {
        let backend = Llvm2CodegenBackend::host();
        let module =
            Llvm2CodegenBackend::allocator_module_from_spec(&make_allocator_spec("test.allocator"))
                .expect("allocator spec lowering should succeed");
        let wrapper = module.lir_functions[0].clone();

        let emitted = backend.emit_object(&[wrapper]).expect("single wrapper object should emit");
        let symbols = mach_o_symbols(&emitted);
        let defined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_defined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        let undefined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_undefined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();

        assert_eq!(defined, BTreeSet::from(["__Rshim_alloc".to_string()]));
        assert_eq!(undefined, BTreeSet::from(["__Rdefault_alloc".to_string()]));
    }

    #[cfg(target_vendor = "apple")]
    #[test]
    fn test_emit_module_objects_single_function_preserves_undefined_external_call_symbol() {
        let backend = Llvm2CodegenBackend::host();
        let module =
            Llvm2CodegenBackend::allocator_module_from_spec(&make_allocator_spec("test.allocator"))
                .expect("allocator spec lowering should succeed");
        let wrapper = module.lir_functions[0].clone();
        let compiled_module = CompiledModule {
            name: "single_wrapper.codegen_unit.0".to_string(),
            lir_functions: vec![wrapper],
            object_path: None,
            function_count: 1,
        };

        let emitted = backend
            .emit_module_objects(&compiled_module)
            .expect("single wrapper module should emit")
            .into_iter()
            .next()
            .expect("single wrapper module should emit one object");

        assert_eq!(emitted.artifact_name, "single_wrapper.codegen_unit.0");
        assert_eq!(emitted.source_name, "_Rshim_alloc");

        let symbols = mach_o_symbols(&emitted.bytes);
        #[cfg(target_arch = "aarch64")]
        let branch26_relocations = mach_o_text_relocations(&emitted.bytes)
            .into_iter()
            .filter_map(|reloc| {
                matches!(reloc.kind, llvm2_codegen::macho::AArch64RelocKind::Branch26)
                    .then_some((reloc.pc_relative, reloc.is_extern))
            })
            .collect::<Vec<_>>();
        let undefined = symbols
            .iter()
            .filter(|(_, entry)| entry.is_undefined())
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        #[cfg(target_arch = "aarch64")]
        assert_eq!(branch26_relocations, vec![(true, true)]);
        assert_eq!(undefined, BTreeSet::from(["__Rdefault_alloc".to_string()]));
    }

    #[test]
    fn test_join_codegen_preserves_attached_allocator_module_spec() {
        let backend = Llvm2CodegenBackend::host();
        let info = CrateInfo {
            target_cpu: "generic".to_string(),
            crate_name: "test".to_string(),
            functions: vec![make_add()],
        };
        let outputs =
            OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "test".to_string() };
        let mut ongoing = backend.codegen_crate(&info).expect("codegen should succeed");
        let allocator_module_name = Llvm2CodegenBackend::allocator_module_name("test");

        backend
            .attach_allocator_module_spec(
                ongoing.as_mut(),
                make_allocator_spec(&allocator_module_name),
            )
            .expect("attach_allocator_module_spec should accept OngoingCodegen");

        let ongoing_ref = ongoing.downcast_ref::<OngoingCodegen>().expect("should downcast");
        assert_eq!(
            ongoing_ref
                .allocator_module_spec()
                .expect("allocator module spec should be attached")
                .module_name,
            allocator_module_name
        );

        let (compiled, work_products) =
            backend.join_codegen(ongoing, &outputs).expect("join should succeed");
        let allocator_module =
            compiled.allocator_module.as_ref().expect("join should preserve allocator module");

        assert_eq!(allocator_module.name, allocator_module_name);
        assert_eq!(allocator_module.function_count, 3);
        assert_eq!(allocator_module.lir_functions.len(), 3);
        assert!(work_products.is_empty());

        let emitted = backend
            .emit_allocator_module_object(allocator_module)
            .expect("spec-backed allocator module should emit")
            .expect("spec-backed allocator module should produce one object");
        assert_eq!(emitted.artifact_name, allocator_module_name);
        assert!(!emitted.bytes.is_empty());
    }

    #[test]
    fn test_join_codegen_wrong_type_fails() {
        let backend = Llvm2CodegenBackend::host();
        let outputs =
            OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "test".to_string() };

        // Pass a wrong type to join_codegen.
        let wrong: Box<dyn Any> = Box::new(42_u32);
        let err = backend.join_codegen(wrong, &outputs).unwrap_err();
        assert!(matches!(err, CodegenBackendError::JoinFailed { .. }));
    }

    #[test]
    fn test_full_pipeline_codegen_join_link() {
        let backend = Llvm2CodegenBackend::host();
        let info = CrateInfo {
            target_cpu: "generic".to_string(),
            crate_name: "pipeline_test".to_string(),
            functions: vec![make_add(), make_identity()],
        };
        let outputs = OutputFilenames {
            out_dir: PathBuf::from("/tmp"),
            crate_stem: "pipeline_test".to_string(),
        };

        // Step 1: codegen_crate
        let ongoing = backend.codegen_crate(&info).expect("codegen should succeed");

        // Step 2: join_codegen
        let (compiled, _) = backend.join_codegen(ongoing, &outputs).expect("join should succeed");

        // Step 3: link
        let output_path = backend.link(&compiled, &outputs).expect("link should succeed");
        assert_eq!(output_path, PathBuf::from("/tmp/pipeline_test.o"));
    }

    #[test]
    fn test_link_empty_crate_fails() {
        let backend = Llvm2CodegenBackend::host();
        let compiled = CompiledModules {
            modules: vec![CompiledModule {
                name: "empty".to_string(),
                lir_functions: vec![],
                object_path: None,
                function_count: 0,
            }],
            allocator_module: None,
        };
        let outputs =
            OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "empty".to_string() };

        let err = backend.link(&compiled, &outputs).unwrap_err();
        assert!(matches!(err, CodegenBackendError::LinkFailed { .. }));
    }

    #[test]
    fn test_output_filenames_object_path() {
        let outputs = OutputFilenames {
            out_dir: PathBuf::from("/build/out"),
            crate_stem: "my_crate".to_string(),
        };
        assert_eq!(outputs.object_path("o"), PathBuf::from("/build/out/my_crate.o"));
        assert_eq!(outputs.object_path("rlib"), PathBuf::from("/build/out/my_crate.rlib"));
    }

    #[test]
    fn test_supported_crate_types() {
        let backend = Llvm2CodegenBackend::host();
        let types = backend.supported_crate_types();
        assert!(types.contains(&"bin"));
        assert!(types.contains(&"rlib"));
        assert!(types.contains(&"staticlib"));
    }

    #[test]
    fn test_init_succeeds() {
        let backend = Llvm2CodegenBackend::host();
        backend.init().expect("init should succeed");
    }

    // -- Verify LIR output structure through the backend --

    #[test]
    fn test_codegen_produces_valid_lir_blocks() {
        let backend = Llvm2CodegenBackend::host();
        let info = CrateInfo {
            target_cpu: "generic".to_string(),
            crate_name: "lir_check".to_string(),
            functions: vec![make_add()],
        };

        let ongoing = backend.codegen_crate(&info).expect("codegen should succeed");
        let ongoing_ref = ongoing.downcast_ref::<OngoingCodegen>().expect("downcast");

        let lir = &ongoing_ref.modules[0].lir_functions[0];
        assert_eq!(lir.name, "add");
        // The entry block should have instructions (Iadd at minimum).
        let entry = &lir.blocks[&lir.entry_block];
        assert!(!entry.instructions.is_empty(), "entry block should have instructions");
    }

    // -- lower_module tests --

    #[test]
    fn test_lower_module_single_function() {
        let backend = Llvm2CodegenBackend::host();
        let funcs = vec![make_add()];
        let lir_fns =
            backend.lower_module(&funcs).expect("lower_module should succeed for single function");
        assert_eq!(lir_fns.len(), 1);
        assert_eq!(lir_fns[0].name, "add");
    }

    #[test]
    fn test_lower_module_multiple_functions() {
        let backend = Llvm2CodegenBackend::host();
        let funcs = vec![make_add(), make_identity()];
        let lir_fns = backend
            .lower_module(&funcs)
            .expect("lower_module should succeed for multiple functions");
        assert_eq!(lir_fns.len(), 2);
        assert_eq!(lir_fns[0].name, "add");
        assert_eq!(lir_fns[1].name, "identity");
    }

    #[test]
    fn test_lower_module_empty() {
        let backend = Llvm2CodegenBackend::host();
        let lir_fns =
            backend.lower_module(&[]).expect("lower_module should succeed for empty slice");
        assert!(lir_fns.is_empty());
    }

    // -- optimize tests --

    #[test]
    fn test_optimize_preserves_reachable_blocks() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_add();
        let mut lir = backend.lower_function(&func).expect("should lower add function");
        let blocks_before = lir.blocks.len();

        backend.optimize(&mut lir).expect("optimize should succeed");

        // All blocks in a simple add function are reachable from entry.
        assert_eq!(lir.blocks.len(), blocks_before);
        assert!(lir.blocks.contains_key(&lir.entry_block));
    }

    #[test]
    fn test_optimize_removes_unreachable_block() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_add();
        let mut lir = backend.lower_function(&func).expect("should lower add function");

        // Inject an unreachable block.
        use llvm2_lower::function::BasicBlock as LirBlock;
        let dead_block = Block(999);
        lir.blocks.insert(dead_block, LirBlock::default());
        let blocks_before = lir.blocks.len();

        backend.optimize(&mut lir).expect("optimize should succeed");

        // The dead block should be removed.
        assert_eq!(lir.blocks.len(), blocks_before - 1);
        assert!(!lir.blocks.contains_key(&dead_block));
        assert!(lir.blocks.contains_key(&lir.entry_block));
    }

    #[test]
    fn test_optimize_identity_function() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_identity();
        let mut lir = backend.lower_function(&func).expect("should lower identity function");

        backend.optimize(&mut lir).expect("optimize should succeed on identity function");

        // Entry block should still exist with instructions.
        let entry = &lir.blocks[&lir.entry_block];
        assert!(!entry.instructions.is_empty());
    }

    fn assert_object_magic(bytes: &[u8]) {
        assert!(bytes.len() >= 4, "object must be at least 4 bytes");
        let magic = &bytes[..4];
        let is_macho = magic == [0xCF, 0xFA, 0xED, 0xFE];
        let is_elf = magic == [0x7F, b'E', b'L', b'F'];
        assert!(is_macho || is_elf, "expected Mach-O or ELF magic, got {magic:02X?}",);
    }

    // -- emit_object tests --

    #[test]
    fn test_emit_object_single_function_produces_macho() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_add();
        let lir = backend.lower_function(&func).expect("should lower add function");

        let bytes = backend.emit_object(&[lir]).expect("emit_object should succeed");
        assert!(!bytes.is_empty());
        assert!(bytes.len() > 32, "object should have a real header/body");
        assert_object_magic(&bytes);
    }

    #[test]
    fn test_emit_object_multi_function_rejected() {
        let backend = Llvm2CodegenBackend::host();
        let funcs = vec![make_add(), make_identity()];
        let lir_fns = backend.lower_module(&funcs).expect("lower_module should succeed");

        let err = backend.emit_object(&lir_fns).unwrap_err();
        assert!(matches!(err, CodegenBackendError::EmitFailed { .. }));
    }

    #[test]
    fn test_emit_object_empty_module_fails() {
        let backend = Llvm2CodegenBackend::host();
        let err = backend.emit_object(&[]).unwrap_err();
        assert!(matches!(err, CodegenBackendError::EmitFailed { .. }));
    }

    #[test]
    fn test_emit_objects_multi_function() {
        let backend = Llvm2CodegenBackend::host();
        let funcs = vec![make_add(), make_identity()];
        let lir_fns = backend.lower_module(&funcs).expect("lower_module should succeed");

        let objects = backend.emit_objects(&lir_fns).expect("emit_objects should succeed");
        assert_eq!(objects.len(), 2);
        assert_eq!(objects[0].0, "add");
        assert!(!objects[0].1.is_empty());
        assert_eq!(objects[1].0, "identity");
        assert!(!objects[1].1.is_empty());
    }

    #[test]
    fn test_emit_module_objects_multi_function_splits_module() {
        let backend = Llvm2CodegenBackend::host();
        let funcs = vec![make_add(), make_identity()];
        let lir_functions = backend.lower_module(&funcs).expect("lower_module should succeed");
        let module = CompiledModule {
            name: "multi.codegen_unit.0".to_string(),
            lir_functions,
            object_path: None,
            function_count: 2,
        };

        let objects =
            backend.emit_module_objects(&module).expect("emit_module_objects should succeed");
        assert_eq!(objects.len(), 2);
        assert_eq!(objects[0].artifact_name, "multi.codegen_unit.0.f0");
        assert_eq!(objects[0].source_name, "add");
        assert_object_magic(&objects[0].bytes);
        assert_eq!(objects[1].artifact_name, "multi.codegen_unit.0.f1");
        assert_eq!(objects[1].source_name, "identity");
        assert_object_magic(&objects[1].bytes);
    }

    // -- Many-block function tests --

    /// Build a linear chain of `n` basic blocks: bb0 -> bb1 -> ... -> bb(n-1) Return.
    /// Each block assigns to a temp, then gotos next.
    fn make_chain_function(n: usize) -> VerifiableFunction {
        assert!(n >= 1, "need at least 1 block");
        let mut locals = vec![
            LocalDecl { index: 0, ty: Ty::i64(), name: None }, // return
            LocalDecl { index: 1, ty: Ty::i64(), name: Some("x".into()) }, // arg
        ];
        // Temps for intermediate results: locals[2..2+n-1]
        for i in 0..n {
            locals.push(LocalDecl { index: 2 + i, ty: Ty::i64(), name: None });
        }

        let mut blocks = Vec::with_capacity(n);
        for i in 0..n {
            let stmt = Statement::Assign {
                place: Place::local(2 + i),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            };
            let terminator = if i == n - 1 {
                // Last block: assign return and return.
                Terminator::Return
            } else {
                Terminator::Goto(BlockId(i + 1))
            };
            blocks.push(BasicBlock { id: BlockId(i), stmts: vec![stmt], terminator });
        }

        // Override last block to assign to return local.
        if let Some(last) = blocks.last_mut() {
            last.stmts = vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            }];
        }

        VerifiableFunction {
            name: format!("chain_{n}"),
            def_path: format!("test::chain_{n}"),
            span: SourceSpan::default(),
            body: VerifiableBody { locals, blocks, arg_count: 1, return_ty: Ty::i64() },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_lower_module_many_blocks_10() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_chain_function(10);
        let lir_fns =
            backend.lower_module(&[func]).expect("lower_module should succeed for 10-block chain");
        assert_eq!(lir_fns.len(), 1);
        // Should have at least 10 blocks (may have an extra panic block).
        assert!(
            lir_fns[0].blocks.len() >= 10,
            "expected >= 10 blocks, got {}",
            lir_fns[0].blocks.len()
        );
    }

    #[test]
    fn test_lower_module_many_blocks_20() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_chain_function(20);
        let lir_fns =
            backend.lower_module(&[func]).expect("lower_module should succeed for 20-block chain");
        assert_eq!(lir_fns.len(), 1);
        assert!(
            lir_fns[0].blocks.len() >= 20,
            "expected >= 20 blocks, got {}",
            lir_fns[0].blocks.len()
        );
    }

    #[test]
    fn test_optimize_many_blocks_all_reachable() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_chain_function(15);
        let mut lir = backend.lower_function(&func).expect("should lower 15-block chain");
        let blocks_before = lir.blocks.len();

        backend.optimize(&mut lir).expect("optimize should succeed on 15-block chain");

        // All blocks in a linear chain are reachable, so none removed.
        assert_eq!(lir.blocks.len(), blocks_before);
    }

    #[test]
    fn test_optimize_removes_multiple_dead_blocks() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_add();
        let mut lir = backend.lower_function(&func).expect("should lower add function");

        // Inject 5 unreachable blocks.
        use llvm2_lower::function::BasicBlock as LirBlock;
        for i in 900..905 {
            lir.blocks.insert(Block(i), LirBlock::default());
        }
        let blocks_before = lir.blocks.len();

        backend.optimize(&mut lir).expect("optimize should succeed");

        assert_eq!(lir.blocks.len(), blocks_before - 5, "should remove exactly 5 dead blocks");
        for i in 900..905 {
            assert!(!lir.blocks.contains_key(&Block(i)));
        }
    }

    // -- Complex control flow: nested SwitchInt --

    /// Build a function with a multi-way SwitchInt (simulating a match on i32).
    /// match x { 0 => bb1, 1 => bb2, 2 => bb3, _ => bb4 }
    /// Each arm block returns.
    fn make_switch_function() -> VerifiableFunction {
        let locals = vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
        ];
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(1)),
                    targets: vec![(0, BlockId(1)), (1, BlockId(2)), (2, BlockId(3))],
                    otherwise: BlockId(4),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(20))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(30))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(4),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ];

        VerifiableFunction {
            name: "switch_fn".to_string(),
            def_path: "test::switch_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody { locals, blocks, arg_count: 1, return_ty: Ty::i32() },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_lower_switch_multi_way() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_switch_function();
        let lir = backend.lower_function(&func).expect("should lower switch function");

        // Should have at least 5 blocks (bb0-bb4, possibly a panic block).
        assert!(lir.blocks.len() >= 5, "expected >= 5 blocks, got {}", lir.blocks.len());

        // Entry block should contain a Switch opcode (3 targets = multi-way).
        let entry = &lir.blocks[&lir.entry_block];
        let has_switch =
            entry.instructions.iter().any(|i| matches!(i.opcode, Opcode::Switch { .. }));
        assert!(has_switch, "entry block should have a Switch opcode for multi-way SwitchInt");
    }

    #[test]
    fn test_optimize_switch_preserves_all_arms() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_switch_function();
        let mut lir = backend.lower_function(&func).expect("should lower switch function");
        let blocks_before = lir.blocks.len();

        backend.optimize(&mut lir).expect("optimize should succeed");

        // All arms are reachable via the switch, so no blocks removed.
        assert_eq!(lir.blocks.len(), blocks_before);
    }

    // -- Nested SwitchInt + loop-like structure --

    /// Build a function with a back-edge (loop-like):
    /// bb0: if x == 0 goto bb2 else bb1
    /// bb1: x = x - 1; goto bb0   (back-edge)
    /// bb2: return x
    fn make_loop_function() -> VerifiableFunction {
        let locals = vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
        ];
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(1)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Sub,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(1)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(BlockId(0)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ];

        VerifiableFunction {
            name: "loop_fn".to_string(),
            def_path: "test::loop_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody { locals, blocks, arg_count: 1, return_ty: Ty::i32() },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_lower_loop_function() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_loop_function();
        let lir = backend.lower_function(&func).expect("should lower loop function");

        assert!(
            lir.blocks.len() >= 3,
            "expected >= 3 blocks for loop function, got {}",
            lir.blocks.len()
        );
    }

    #[test]
    fn test_optimize_loop_preserves_back_edge() {
        let backend = Llvm2CodegenBackend::host();
        let func = make_loop_function();
        let mut lir = backend.lower_function(&func).expect("should lower loop function");

        // Add a dead block that is NOT part of the loop.
        use llvm2_lower::function::BasicBlock as LirBlock;
        lir.blocks.insert(Block(888), LirBlock::default());

        backend.optimize(&mut lir).expect("optimize should succeed");

        // Dead block removed, but loop blocks (with back-edge) preserved.
        assert!(!lir.blocks.contains_key(&Block(888)));
        assert!(lir.blocks.len() >= 3, "loop blocks should be preserved after optimize");
    }

    // -- Error case tests --

    #[test]
    fn test_codegen_backend_error_display() {
        let e = CodegenBackendError::Unavailable { reason: "not initialized".to_string() };
        assert_eq!(e.to_string(), "backend unavailable: not initialized");

        let e = CodegenBackendError::CodegenUnitFailed {
            unit_name: "foo".to_string(),
            reason: "bad type".to_string(),
        };
        assert_eq!(e.to_string(), "codegen unit `foo` failed: bad type");

        let e = CodegenBackendError::OptimizationFailed {
            func_name: "bar".to_string(),
            reason: "loop detected".to_string(),
        };
        assert_eq!(e.to_string(), "optimization failed on `bar`: loop detected");

        let e = CodegenBackendError::EmitFailed { reason: "no functions".to_string() };
        assert_eq!(e.to_string(), "emit_object failed: no functions");

        let e = CodegenBackendError::Pipeline {
            func_name: "baz".to_string(),
            reason: "bad instruction".to_string(),
        };
        assert_eq!(e.to_string(), "llvm2 pipeline failed for `baz`: bad instruction");

        let e = CodegenBackendError::JoinFailed { reason: "wrong type".to_string() };
        assert_eq!(e.to_string(), "join failed: wrong type");

        let e = CodegenBackendError::LinkFailed { reason: "missing symbols".to_string() };
        assert_eq!(e.to_string(), "link failed: missing symbols");
    }

    #[test]
    fn test_ongoing_codegen_accessors() {
        let ongoing = OngoingCodegen {
            modules: vec![
                CompiledModule {
                    name: "m1".to_string(),
                    lir_functions: vec![],
                    object_path: None,
                    function_count: 3,
                },
                CompiledModule {
                    name: "m2".to_string(),
                    lir_functions: vec![],
                    object_path: None,
                    function_count: 2,
                },
            ],
            allocator_module: Some(CompiledModule {
                name: "alloc".to_string(),
                lir_functions: vec![],
                object_path: None,
                function_count: 1,
            }),
            allocator_module_spec: Some(AllocatorModuleSpec {
                module_name: "alloc.spec".to_string(),
                functions: vec![AllocatorFunctionSpec {
                    name: "alloc".to_string(),
                    wrapper_symbol_name: "_Rshim_alloc".to_string(),
                    callee_symbol_name: "_Rdefault_alloc".to_string(),
                    kind: AllocatorFunctionKind::Alloc,
                    inputs: vec![AllocatorArgKind::Layout],
                    output: AllocatorResultKind::ResultPtr,
                }],
                no_alloc_shim_is_unstable_symbol_name: Some("_Rshim_no_alloc_marker".to_string()),
            }),
            failures: vec![("bad_fn".to_string(), "type error".to_string())],
            crate_name: "my_crate".to_string(),
            #[cfg(feature = "transval")]
            validation_results: Vec::new(),
        };

        assert_eq!(ongoing.crate_name(), "my_crate");
        assert_eq!(ongoing.compiled_count(), 6);
        assert_eq!(ongoing.failure_count(), 1);
        assert_eq!(
            ongoing.allocator_module().expect("allocator module should exist").name,
            "alloc"
        );
        assert_eq!(
            ongoing
                .allocator_module_spec()
                .expect("allocator module spec should exist")
                .module_name,
            "alloc.spec"
        );
    }

    #[test]
    fn test_join_codegen_with_failures_reports_error() {
        let backend = Llvm2CodegenBackend::host();
        let outputs =
            OutputFilenames { out_dir: PathBuf::from("/tmp"), crate_stem: "test".to_string() };

        // Manually construct OngoingCodegen with failures.
        let ongoing: Box<dyn Any> = Box::new(OngoingCodegen {
            modules: vec![],
            allocator_module: None,
            allocator_module_spec: None,
            failures: vec![("broken_fn".to_string(), "bad IR".to_string())],
            crate_name: "test".to_string(),
            #[cfg(feature = "transval")]
            validation_results: Vec::new(),
        });

        let err = backend.join_codegen(ongoing, &outputs).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("broken_fn"), "error should mention the failing function");
        assert!(msg.contains("bad IR"), "error should include the error reason");
    }

    #[test]
    fn test_bridge_error_converts_to_codegen_backend_error() {
        let bridge_err = crate::BridgeError::UnsupportedType("Fn".to_string());
        let codegen_err: CodegenBackendError = bridge_err.into();
        assert!(
            matches!(codegen_err, CodegenBackendError::Bridge(_)),
            "BridgeError should convert to CodegenBackendError::Bridge"
        );
        assert!(codegen_err.to_string().contains("unsupported type: Fn"));
    }

    // -- Transval integration tests (lower -> validate -> report) --

    #[cfg(feature = "transval")]
    mod transval_integration {
        use super::*;

        #[test]
        fn test_validate_lowering_result_single_function() {
            let backend = Llvm2CodegenBackend::host();
            let funcs = vec![make_add()];
            let lir_fns = backend.lower_module(&funcs).expect("lower_module should succeed");

            let results = backend.validate_lowering_result(&funcs, &lir_fns);
            assert_eq!(results.len(), 1);
            assert_eq!(results[0].function_name, "add");
            assert!(
                results[0].is_valid(),
                "add function should validate: {:?}",
                results[0].verdict
            );
            assert!(results[0].checks_total > 0);
            assert_eq!(results[0].checks_passed, results[0].checks_total);
        }

        #[test]
        fn test_validate_lowering_result_multiple_functions() {
            let backend = Llvm2CodegenBackend::host();
            let funcs = vec![make_add(), make_identity()];
            let lir_fns = backend.lower_module(&funcs).expect("lower_module should succeed");

            let results = backend.validate_lowering_result(&funcs, &lir_fns);
            assert_eq!(results.len(), 2);
            assert_eq!(results[0].function_name, "add");
            assert_eq!(results[1].function_name, "identity");
            for result in &results {
                assert!(
                    result.is_valid(),
                    "{} should validate: {:?}",
                    result.function_name,
                    result.verdict
                );
            }
        }

        #[test]
        fn test_validate_lowering_result_empty_batch() {
            let backend = Llvm2CodegenBackend::host();
            let results = backend.validate_lowering_result(&[], &[]);
            assert!(results.is_empty());
        }

        #[test]
        fn test_validate_lowering_result_chain_function() {
            let backend = Llvm2CodegenBackend::host();
            let funcs = vec![make_chain_function(5)];
            let lir_fns = backend.lower_module(&funcs).expect("lower_module should succeed");

            let results = backend.validate_lowering_result(&funcs, &lir_fns);
            assert_eq!(results.len(), 1);
            assert_eq!(results[0].function_name, "chain_5");
            // Chain functions should have many checks due to multiple blocks.
            assert!(
                results[0].checks_total >= 5,
                "expected >= 5 checks for chain function, got {}",
                results[0].checks_total
            );
        }

        #[test]
        fn test_validate_lowering_result_switch_function() {
            let backend = Llvm2CodegenBackend::host();
            let funcs = vec![make_switch_function()];
            let lir_fns = backend.lower_module(&funcs).expect("lower_module should succeed");

            let results = backend.validate_lowering_result(&funcs, &lir_fns);
            assert_eq!(results.len(), 1);
            assert_eq!(results[0].function_name, "switch_fn");
        }

        #[test]
        fn test_full_pipeline_lower_validate_report() {
            // Integration test: lower -> validate -> report
            let backend = Llvm2CodegenBackend::host();
            let funcs = vec![make_add(), make_identity(), make_chain_function(3)];

            // Step 1: Lower
            let lir_fns = backend.lower_module(&funcs).expect("lower_module should succeed");
            assert_eq!(lir_fns.len(), 3);

            // Step 2: Validate
            let results = backend.validate_lowering_result(&funcs, &lir_fns);
            assert_eq!(results.len(), 3);

            // Step 3: Report (check all validated)
            let all_valid = results.iter().all(|r| r.is_valid());
            assert!(
                all_valid,
                "all functions should validate. Failures: {:?}",
                results
                    .iter()
                    .filter(|r| !r.is_valid())
                    .map(|r| (&r.function_name, &r.verdict))
                    .collect::<Vec<_>>()
            );

            // Verify total check counts are reasonable
            let total_checks: usize = results.iter().map(|r| r.checks_total).sum();
            assert!(
                total_checks >= 15,
                "expected >= 15 total checks across 3 functions, got {total_checks}"
            );
        }

        #[test]
        fn test_lower_function_validated_integration() {
            // Tests the lower_function_validated path (single-function transval).
            let backend = Llvm2CodegenBackend::host();
            let func = make_add();

            let lir = backend
                .lower_function_validated(&func)
                .expect("lower_function_validated should succeed for add");
            assert_eq!(lir.name, "add");
            assert_eq!(lir.signature.params.len(), 2);
        }

        #[test]
        fn test_lower_function_validated_identity() {
            let backend = Llvm2CodegenBackend::host();
            let func = make_identity();

            let lir = backend
                .lower_function_validated(&func)
                .expect("lower_function_validated should succeed for identity");
            assert_eq!(lir.name, "identity");
            assert_eq!(lir.signature.params.len(), 1);
        }

        #[test]
        fn test_codegen_pipeline_with_transval() {
            // Full codegen pipeline exercising transval at each stage.
            let backend = Llvm2CodegenBackend::host();
            let funcs = vec![make_add(), make_identity()];

            // Lower
            let lir_fns = backend.lower_module(&funcs).expect("lower_module should succeed");

            // Validate lowering
            let validation_results = backend.validate_lowering_result(&funcs, &lir_fns);
            for result in &validation_results {
                assert!(
                    result.is_valid(),
                    "Pre-optimization: {} should validate",
                    result.function_name
                );
            }

            // Optimize
            let mut opt_lir = lir_fns;
            for lir in &mut opt_lir {
                backend.optimize(lir).expect("optimize should succeed");
            }

            // Emit
            let objects = backend.emit_objects(&opt_lir).expect("emit_objects should succeed");
            assert_eq!(objects.len(), 2);
            assert!(objects.iter().all(|(_, bytes)| !bytes.is_empty()));
        }

        #[test]
        fn test_codegen_pipeline_with_validation_results() {
            let backend = Llvm2CodegenBackend::host();
            let info = CrateInfo {
                target_cpu: "generic".to_string(),
                crate_name: "validated".to_string(),
                functions: vec![make_add(), make_identity()],
            };

            let ongoing = backend.codegen_crate(&info).expect("codegen_crate should succeed");
            let ongoing = ongoing.downcast::<OngoingCodegen>().expect("should be OngoingCodegen");

            assert!(
                !ongoing.validation_results().is_empty(),
                "codegen_crate should record validation results",
            );
            assert!(
                ongoing.validation_results().iter().all(|result| result.is_valid()),
                "all validation results should be valid: {:?}",
                ongoing.validation_results(),
            );
        }
    }
}
