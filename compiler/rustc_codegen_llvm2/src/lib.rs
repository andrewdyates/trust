//! rustc_codegen_llvm2: LLVM2 codegen backend for rustc.
//!
//! This crate implements `rustc_codegen_ssa::traits::CodegenBackend` for the
//! LLVM2 verified codegen pipeline. It is a thin adapter that delegates the
//! actual MIR-to-LIR lowering to `trust-llvm2-bridge`.
//!
//! # Architecture
//!
//! ```text
//! rustc driver (-Z codegen-backend=llvm2)
//!     |
//!     v
//! rustc_codegen_llvm2::Llvm2CodegenBackend  (this crate)
//!     |  implements rustc_codegen_ssa::traits::CodegenBackend
//!     |  converts rustc types <-> bridge types
//!     v
//! trust_llvm2_bridge::codegen_backend::Llvm2CodegenBackend
//!     |  MIR lowering, optimization, emission
//!     v
//! llvm2-lower / llvm2-codegen
//! ```
//!
//! # Usage
//!
//! Select this backend via `-Z codegen-backend=llvm2` when invoking rustc
//! built with the `llvm2` feature enabled in `rustc_interface`.
//!
//! Part of #829 (CodegenBackend for LLVM2).
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// tRust: We need rustc_private to access compiler-internal crates.
#![feature(rustc_private)]

extern crate rustc_codegen_ssa;
extern crate rustc_data_structures;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate tracing;

use std::any::Any;
use std::fmt::Write as _;
use std::fs;
use std::hash::Hasher as _;

use rustc_codegen_ssa::back::archive::ArArchiveBuilderBuilder;
use rustc_codegen_ssa::back::link::link_binary;
use rustc_codegen_ssa::base::{allocator_kind_for_codegen, allocator_shim_contents};
use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_codegen_ssa::{CompiledModule, CompiledModules, CrateInfo, ModuleKind, TargetConfig};
use rustc_data_structures::base_n::{ALPHANUMERIC_ONLY, ToBaseN};
use rustc_data_structures::fx::{FxHashMap, FxIndexMap};
use rustc_data_structures::stable_hasher::{FromStableHash, StableHasher, StableHasherHash};
use rustc_metadata::EncodedMetadata;
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};
use rustc_middle::util::Providers;
use rustc_session::Session;
use rustc_session::config::{OutputFilenames, OutputType};
use rustc_span::def_id::LocalDefId;
use rustc_span::{Symbol, sym};
use trust_types::Terminator as VerifiableTerminator;
use trust_types::VerifiableFunction;

use trust_llvm2_bridge::codegen_backend::{
    self as bridge_backend, Llvm2CodegenBackend as BridgeBackend, Llvm2TargetArch,
    RustcCodegenBackend as BridgeCodegenBackend,
};

// ---------------------------------------------------------------------------
// The rustc adapter
// ---------------------------------------------------------------------------

/// LLVM2 codegen backend for rustc.
///
/// Implements the real `rustc_codegen_ssa::traits::CodegenBackend` trait by
/// delegating to the bridge crate's `Llvm2CodegenBackend`.
// tRust: CodegenBackend adapter for LLVM2 integration (#829).
pub struct Llvm2CodegenBackend;

impl Llvm2CodegenBackend {
    /// Create a new LLVM2 backend adapter.
    pub fn new() -> Box<dyn CodegenBackend> {
        Box::new(Self)
    }

    fn bridge_for_target_arch(&self, target_arch: &str) -> Option<BridgeBackend> {
        Llvm2TargetArch::from_rustc_arch(target_arch).map(BridgeBackend::new)
    }

    fn bridge_for_session(&self, sess: &Session) -> BridgeBackend {
        let target_arch = sess.target.arch.desc();
        match self.bridge_for_target_arch(target_arch) {
            Some(bridge) => bridge,
            None => sess.dcx().fatal(format!(
                "LLVM2 backend does not support target architecture `{target_arch}`"
            )),
        }
    }

    fn bridge_for_tcx<'tcx>(&self, tcx: TyCtxt<'tcx>) -> BridgeBackend {
        self.bridge_for_session(tcx.sess)
    }

    fn emit_rustc_modules_for_bridge_module(
        &self,
        bridge: &BridgeBackend,
        bridge_module: &bridge_backend::CompiledModule,
        sess: &Session,
        outputs: &OutputFilenames,
    ) -> Vec<CompiledModule> {
        let emitted_objects = match bridge.emit_module_objects(bridge_module) {
            Ok(objects) => objects,
            Err(e) => sess.dcx().fatal(format!(
                "LLVM2: failed to emit object(s) for `{}`: {e}",
                bridge_module.name
            )),
        };

        if emitted_objects.is_empty() {
            return vec![CompiledModule {
                name: bridge_module.name.clone(),
                kind: ModuleKind::Regular,
                object: None,
                dwarf_object: None,
                bytecode: None,
                assembly: None,
                llvm_ir: None,
                links_from_incr_cache: Vec::new(),
            }];
        }

        emitted_objects
            .into_iter()
            .map(|emitted| {
                let object_path = outputs.temp_path_for_cgu(
                    OutputType::Object,
                    &emitted.artifact_name,
                    sess.invocation_temp.as_deref(),
                );

                if let Err(e) = fs::write(&object_path, &emitted.bytes) {
                    sess.dcx().fatal(format!(
                        "LLVM2: failed to write object `{}` for `{}`: {e}",
                        emitted.artifact_name, emitted.source_name
                    ));
                }

                CompiledModule {
                    name: emitted.artifact_name,
                    kind: ModuleKind::Regular,
                    object: Some(object_path),
                    dwarf_object: None,
                    bytecode: None,
                    assembly: None,
                    llvm_ir: None,
                    links_from_incr_cache: Vec::new(),
                }
            })
            .collect()
    }

    fn emit_rustc_allocator_module_for_bridge_module(
        &self,
        bridge: &BridgeBackend,
        bridge_module: &bridge_backend::CompiledModule,
        sess: &Session,
        outputs: &OutputFilenames,
    ) -> CompiledModule {
        let emitted_object = match bridge.emit_allocator_module_object(bridge_module) {
            Ok(object) => object,
            Err(e) => sess.dcx().fatal(format!(
                "LLVM2: failed to emit allocator object(s) for `{}`: {e}",
                bridge_module.name
            )),
        };

        match emitted_object {
            None => CompiledModule {
                name: bridge_module.name.clone(),
                kind: ModuleKind::Allocator,
                object: None,
                dwarf_object: None,
                bytecode: None,
                assembly: None,
                llvm_ir: None,
                links_from_incr_cache: Vec::new(),
            },
            Some(emitted) => {
                let object_path = outputs.temp_path_for_cgu(
                    OutputType::Object,
                    &emitted.artifact_name,
                    sess.invocation_temp.as_deref(),
                );

                if let Err(e) = fs::write(&object_path, &emitted.bytes) {
                    sess.dcx().fatal(format!(
                        "LLVM2: failed to write allocator object `{}` for `{}`: {e}",
                        emitted.artifact_name, emitted.source_name
                    ));
                }

                CompiledModule {
                    name: bridge_module.name.clone(),
                    kind: ModuleKind::Allocator,
                    object: Some(object_path),
                    dwarf_object: None,
                    bytecode: None,
                    assembly: None,
                    llvm_ir: None,
                    links_from_incr_cache: Vec::new(),
                }
            }
        }
    }
}

fn filter_then_map<T, U, I, P, M>(items: I, mut should_map: P, mut map: M) -> Vec<U>
where
    I: IntoIterator<Item = T>,
    T: Copy,
    P: FnMut(T) -> bool,
    M: FnMut(T) -> U,
{
    items.into_iter().filter_map(|item| should_map(item).then(|| map(item))).collect()
}

fn direct_call_name_override<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    terminator: &mir::Terminator<'tcx>,
    local_function_names: &FxHashMap<LocalDefId, String>,
) -> Option<String> {
    let mir::TerminatorKind::Call { func, .. } = &terminator.kind else {
        return None;
    };
    let mir::Operand::Constant(const_op) = func else {
        return None;
    };
    let ty::FnDef(def_id, args) = *const_op.const_.ty().kind() else {
        return None;
    };

    if let Some(local_def_id) = def_id.as_local() {
        return local_function_names.get(&local_def_id).cloned();
    }

    let instance = ty::Instance::expect_resolve(
        tcx,
        body.typing_env(tcx),
        def_id,
        args,
        terminator.source_info.span,
    );
    Some(tcx.symbol_name(instance).name.to_string())
}

fn collect_direct_call_name_overrides<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    local_function_names: &FxHashMap<LocalDefId, String>,
) -> Vec<Option<String>> {
    body.basic_blocks
        .iter()
        .map(|mir_block| {
            direct_call_name_override(tcx, body, mir_block.terminator(), local_function_names)
        })
        .collect()
}

fn apply_direct_call_name_overrides(func: &mut VerifiableFunction, overrides: &[Option<String>]) {
    for (extracted_block, override_name) in func.body.blocks.iter_mut().zip(overrides.iter()) {
        let Some(symbol_name) = override_name else {
            continue;
        };
        if let VerifiableTerminator::Call { func: callee, .. } = &mut extracted_block.terminator {
            *callee = symbol_name.clone();
        }
    }
}

struct InternalSymbolVersionHash(u64);

impl FromStableHash for InternalSymbolVersionHash {
    type Hash = StableHasherHash;

    fn from(StableHasherHash([hash, _]): Self::Hash) -> Self {
        Self(hash)
    }
}

fn push_integer_62(x: u64, output: &mut String) {
    if let Some(x) = x.checked_sub(1) {
        output.push_str(x.to_base(ALPHANUMERIC_ONLY).as_ref());
    }
    output.push('_');
}

fn push_disambiguator(x: u64, output: &mut String) {
    if let Some(x) = x.checked_sub(1) {
        output.push('s');
        push_integer_62(x + 1, output);
    }
}

fn push_symbol_ident(ident: &str, output: &mut String) {
    assert!(
        ident.bytes().all(|byte| byte == b'_' || byte.is_ascii_alphanumeric()),
        "allocator shim symbols must be ASCII identifiers, got `{ident}`"
    );

    let _ = write!(output, "{}", ident.len());
    if let Some('_' | '0'..='9') = ident.chars().next() {
        output.push('_');
    }
    output.push_str(ident);
}

fn rustc_internal_symbol_name(cfg_version: &str, item_name: &str) -> String {
    match item_name {
        "rust_eh_personality" | "__isPlatformVersionAtLeast" | "__isOSVersionAtLeast" => {
            return item_name.to_owned();
        }
        _ => {}
    }

    let mut hasher = StableHasher::new();
    hasher.write(cfg_version.as_bytes());
    let InternalSymbolVersionHash(version_hash) = hasher.finish::<InternalSymbolVersionHash>();

    let mut symbol = String::from("_R");
    symbol.push('N');
    symbol.push('v');
    symbol.push('C');
    push_disambiguator(version_hash, &mut symbol);
    push_symbol_ident("__rustc", &mut symbol);
    push_symbol_ident(item_name, &mut symbol);
    symbol
}

fn global_allocator_symbol_name(base: Symbol) -> String {
    format!("__rust_{base}")
}

fn default_allocator_symbol_name(base: Symbol) -> String {
    format!("__rdl_{base}")
}

fn allocator_function_spec_from_name(
    cfg_version: &str,
    name: Symbol,
) -> Option<bridge_backend::AllocatorFunctionSpec> {
    let (kind, inputs, output) = match name {
        sym::alloc => (
            bridge_backend::AllocatorFunctionKind::Alloc,
            vec![bridge_backend::AllocatorArgKind::Layout],
            bridge_backend::AllocatorResultKind::ResultPtr,
        ),
        sym::dealloc => (
            bridge_backend::AllocatorFunctionKind::Dealloc,
            vec![bridge_backend::AllocatorArgKind::Ptr, bridge_backend::AllocatorArgKind::Layout],
            bridge_backend::AllocatorResultKind::Unit,
        ),
        sym::realloc => (
            bridge_backend::AllocatorFunctionKind::Realloc,
            vec![
                bridge_backend::AllocatorArgKind::Ptr,
                bridge_backend::AllocatorArgKind::Layout,
                bridge_backend::AllocatorArgKind::Usize,
            ],
            bridge_backend::AllocatorResultKind::ResultPtr,
        ),
        sym::alloc_zeroed => (
            bridge_backend::AllocatorFunctionKind::AllocZeroed,
            vec![bridge_backend::AllocatorArgKind::Layout],
            bridge_backend::AllocatorResultKind::ResultPtr,
        ),
        sym::alloc_error_handler => (
            bridge_backend::AllocatorFunctionKind::AllocErrorHandler,
            vec![bridge_backend::AllocatorArgKind::Layout],
            bridge_backend::AllocatorResultKind::Never,
        ),
        _ => return None,
    };

    Some(bridge_backend::AllocatorFunctionSpec {
        name: name.to_string(),
        wrapper_symbol_name: rustc_internal_symbol_name(
            cfg_version,
            &global_allocator_symbol_name(name),
        ),
        callee_symbol_name: rustc_internal_symbol_name(
            cfg_version,
            &default_allocator_symbol_name(name),
        ),
        kind,
        inputs,
        output,
    })
}

fn allocator_module_spec_from_names<I>(
    crate_name: &str,
    cfg_version: &str,
    names: I,
) -> Result<bridge_backend::AllocatorModuleSpec, String>
where
    I: IntoIterator<Item = Symbol>,
{
    let functions = names
        .into_iter()
        .map(|name| {
            allocator_function_spec_from_name(cfg_version, name)
                .ok_or_else(|| format!("unsupported allocator shim method `{name}`"))
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(bridge_backend::AllocatorModuleSpec {
        module_name: BridgeBackend::allocator_module_name(crate_name),
        functions,
        no_alloc_shim_is_unstable_symbol_name: Some(rustc_internal_symbol_name(
            cfg_version,
            "__rust_no_alloc_shim_is_unstable_v2",
        )),
    })
}

fn allocator_module_spec_for_tcx<'tcx>(
    tcx: TyCtxt<'tcx>,
    crate_name: &str,
) -> Result<Option<bridge_backend::AllocatorModuleSpec>, String> {
    let Some(kind) = allocator_kind_for_codegen(tcx) else {
        return Ok(None);
    };
    let method_names = allocator_shim_contents(tcx, kind).into_iter().map(|method| method.name);
    allocator_module_spec_from_names(crate_name, tcx.sess.cfg_version, method_names).map(Some)
}

// ---------------------------------------------------------------------------
// Ongoing codegen handle
// ---------------------------------------------------------------------------

/// Opaque handle returned by `codegen_crate`, consumed by `join_codegen`.
///
/// Wraps the bridge's `OngoingCodegen` plus any rustc-specific metadata
/// we need to carry through the pipeline.
// tRust: CodegenBackend adapter for LLVM2 integration (#829).
struct OngoingLlvm2Codegen {
    /// Bridge-level ongoing codegen result.
    bridge_ongoing: Box<dyn Any>,
    /// Crate name for diagnostics.
    crate_name: String,
    /// Number of functions extracted from MIR (for diagnostics).
    function_count: usize,
}

// ---------------------------------------------------------------------------
// CodegenBackend impl
// ---------------------------------------------------------------------------

// tRust: CodegenBackend adapter for LLVM2 integration (#829, #959).
impl CodegenBackend for Llvm2CodegenBackend {
    fn name(&self) -> &'static str {
        "llvm2"
    }

    fn init(&self, sess: &Session) {
        // LLVM2 does not require session-level initialization.
        // The bridge backend's init() is a no-op.
        let bridge = self.bridge_for_session(sess);
        if let Err(e) = bridge.init() {
            panic!("LLVM2 backend initialization failed: {e}");
        }
    }

    // tRust: #959 -- register queries needed by the LLVM2 backend.
    fn provide(&self, _providers: &mut Providers) {
        // LLVM2 does not currently inject custom queries into the rustc
        // query system. When we add incremental compilation support or
        // custom optimization queries, they will be registered here.
        //
        // The standard rustc_codegen_ssa queries (symbol_export, etc.)
        // are already registered by the driver before calling into
        // the backend.
    }

    fn target_config(&self, sess: &Session) -> TargetConfig {
        let bridge = self.bridge_for_session(sess);
        let bridge_config = BridgeCodegenBackend::target_config(&bridge);
        TargetConfig {
            target_features: bridge_config
                .target_features
                .iter()
                .map(|s| Symbol::intern(s))
                .collect(),
            unstable_target_features: bridge_config
                .unstable_target_features
                .iter()
                .map(|s| Symbol::intern(s))
                .collect(),
            has_reliable_f16: bridge_config.has_reliable_f16,
            has_reliable_f16_math: bridge_config.has_reliable_f16_math,
            has_reliable_f128: bridge_config.has_reliable_f128,
            has_reliable_f128_math: bridge_config.has_reliable_f128_math,
        }
    }

    fn target_cpu(&self, sess: &Session) -> String {
        let bridge = self.bridge_for_session(sess);
        BridgeCodegenBackend::target_cpu(&bridge)
    }

    fn thin_lto_supported(&self) -> bool {
        // LLVM2 does not implement LTO.
        false
    }

    fn has_zstd(&self) -> bool {
        false
    }

    fn print_version(&self) {
        eprintln!("LLVM2 codegen backend (tRust verified pipeline)");
        eprintln!("  Supported target archs: aarch64, x86_64");
    }

    fn replaced_intrinsics(&self) -> Vec<Symbol> {
        // LLVM2 does not currently replace any intrinsics.
        vec![]
    }

    fn codegen_crate<'tcx>(&self, tcx: TyCtxt<'tcx>, _crate_info: &CrateInfo) -> Box<dyn Any> {
        let bridge = self.bridge_for_tcx(tcx);
        let crate_name = tcx.crate_name(rustc_span::def_id::LOCAL_CRATE).to_string();
        let allocator_module_spec = match allocator_module_spec_for_tcx(tcx, &crate_name) {
            Ok(spec) => spec,
            Err(e) => tcx.dcx().fatal(format!("LLVM2 allocator shim planning failed: {e}")),
        };

        // tRust #829: Extract real MIR from all functions in the crate.
        // mir_keys() returns all LocalDefIds that have MIR bodies (functions,
        // closures, const items, etc.). Filter out non-function owners before
        // optimized_mir(); statics/consts can carry MIR but do not belong in
        // this extraction path and would otherwise ICE the adapter (#988).
        let extracted = filter_then_map(
            tcx.mir_keys(()).iter().copied(),
            |local_def_id| tcx.hir_body_owner_kind(local_def_id).is_fn_or_closure(),
            |local_def_id| {
                let body = tcx.optimized_mir(local_def_id.to_def_id());
                let func = trust_mir_extract::extract_function(tcx, body);
                (local_def_id, body, func)
            },
        );
        let local_function_names: FxHashMap<LocalDefId, String> = functions
            .iter()
            .map(|(local_def_id, func)| (*local_def_id, func.name.clone()))
            .collect();
        for (local_def_id, func) in &mut functions {
            let body = tcx.optimized_mir(local_def_id.to_def_id());
            symbolize_direct_calls(tcx, body, &local_function_names, func);
        }
        let functions: Vec<_> = functions.into_iter().map(|(_, func)| func).collect();

        let local_function_names: FxHashMap<LocalDefId, String> = extracted
            .iter()
            .map(|(local_def_id, _, func)| (*local_def_id, func.name.clone()))
            .collect();

        let functions = extracted
            .into_iter()
            .map(|(_, body, mut func)| {
                let overrides =
                    collect_direct_call_name_overrides(tcx, body, &local_function_names);
                apply_direct_call_name_overrides(&mut func, &overrides);
                func
            })
            .collect::<Vec<_>>();

        let function_count = functions.len();

        // tRust: #961 -- structured tracing for smoke test observability.
        tracing::info!(
            crate_name = %crate_name,
            extracted = function_count,
            "[llvm2] MIR extraction complete"
        );

        let bridge_crate_info = bridge_backend::CrateInfo {
            target_cpu: BridgeCodegenBackend::target_cpu(&bridge),
            crate_name: crate_name.clone(),
            functions,
        };

        let mut bridge_ongoing =
            match BridgeCodegenBackend::codegen_crate(&bridge, &bridge_crate_info) {
                Ok(ongoing) => ongoing,
                Err(e) => {
                    tcx.dcx().fatal(format!("LLVM2 codegen_crate failed: {e}"));
                }
            };

        if let Some(spec) = allocator_module_spec {
            if let Err(e) = bridge.attach_allocator_module_spec(bridge_ongoing.as_mut(), spec) {
                tcx.dcx().fatal(format!("LLVM2 allocator shim planning failed: {e}"));
            }
        }

        // tRust: #961 -- downcast to get lowered/failure counts for diagnostics.
        if let Some(oc) = bridge_ongoing.downcast_ref::<bridge_backend::OngoingCodegen>() {
            tracing::info!(
                crate_name = %crate_name,
                lowered = oc.compiled_count(),
                failures = oc.failure_count(),
                allocator_planned = oc.allocator_module().is_some() || oc.allocator_module_spec().is_some(),
                "[llvm2] bridge lowering complete"
            );
        }

        Box::new(OngoingLlvm2Codegen { bridge_ongoing, crate_name, function_count })
    }

    // tRust: #959 -- join_codegen now produces meaningful CompiledModules
    // by converting bridge results and emitting LIR object artifacts to disk.
    fn join_codegen(
        &self,
        ongoing_codegen: Box<dyn Any>,
        sess: &Session,
        outputs: &OutputFilenames,
    ) -> (CompiledModules, FxIndexMap<WorkProductId, WorkProduct>) {
        let ongoing = ongoing_codegen.downcast::<OngoingLlvm2Codegen>().unwrap();

        // Derive output directory from rustc's OutputFilenames.
        let output_path = outputs.with_extension("o");
        let out_dir =
            output_path.parent().unwrap_or_else(|| std::path::Path::new(".")).to_path_buf();

        let bridge_outputs = bridge_backend::OutputFilenames {
            out_dir: out_dir.clone(),
            crate_stem: ongoing.crate_name.clone(),
        };
        let bridge = self.bridge_for_session(sess);

        match BridgeCodegenBackend::join_codegen(&bridge, ongoing.bridge_ongoing, &bridge_outputs) {
            Ok((bridge_compiled, _bridge_work_products)) => {
                // Convert bridge CompiledModules -> rustc CompiledModules.
                // Multi-function bridge modules are split into one rustc object
                // artifact per function because rustc CompiledModule carries a
                // single object path.
                let mut rustc_modules = Vec::new();

                for bridge_module in &bridge_compiled.modules {
                    rustc_modules.extend(self.emit_rustc_modules_for_bridge_module(
                        &bridge,
                        bridge_module,
                        sess,
                        outputs,
                    ));
                }

                // Convert allocator module if present.
                let allocator_module = bridge_compiled.allocator_module.as_ref().map(|alloc_mod| {
                    self.emit_rustc_allocator_module_for_bridge_module(
                        &bridge, alloc_mod, sess, outputs,
                    )
                });

                let compiled = CompiledModules { modules: rustc_modules, allocator_module };

                sess.dcx().note(format!(
                    "LLVM2: compiled {} function(s) in {} module(s)",
                    ongoing.function_count,
                    compiled.modules.len()
                ));

                (compiled, FxIndexMap::default())
            }
            Err(e) => {
                sess.dcx().fatal(format!("LLVM2 join_codegen failed: {e}"));
            }
        }
    }

    // tRust: #959 -- link() delegates to the standard rustc link_binary(),
    // which handles all output types (rlib, staticlib, cdylib, bin).
    // The compiled modules carry object file paths from join_codegen.
    fn link(
        &self,
        sess: &Session,
        compiled_modules: CompiledModules,
        crate_info: CrateInfo,
        metadata: EncodedMetadata,
        outputs: &OutputFilenames,
    ) {
        link_binary(
            sess,
            &ArArchiveBuilderBuilder,
            compiled_modules,
            crate_info,
            metadata,
            outputs,
            self.name(),
        );
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum FakeMirKey {
        Function(&'static str),
        Closure(&'static str),
        Const(&'static str),
        Static(&'static str),
    }

    #[test]
    fn test_backend_name() {
        let backend = Llvm2CodegenBackend;
        assert_eq!(CodegenBackend::name(&backend), "llvm2");
    }

    #[test]
    fn test_backend_thin_lto_not_supported() {
        let backend = Llvm2CodegenBackend;
        assert!(!backend.thin_lto_supported());
    }

    #[test]
    fn test_backend_new_returns_boxed() {
        let backend = Llvm2CodegenBackend::new();
        assert_eq!(CodegenBackend::name(&*backend), "llvm2");
    }

    #[test]
    fn test_backend_no_zstd() {
        let backend = Llvm2CodegenBackend;
        assert!(!backend.has_zstd());
    }

    #[test]
    fn test_backend_no_replaced_intrinsics() {
        let backend = Llvm2CodegenBackend;
        assert!(backend.replaced_intrinsics().is_empty());
    }

    #[test]
    fn test_filter_then_map_skips_non_function_keys_before_mapping() {
        let lowered = filter_then_map(
            [
                FakeMirKey::Const("C"),
                FakeMirKey::Function("f"),
                FakeMirKey::Static("S"),
                FakeMirKey::Closure("c"),
            ],
            |key| matches!(key, FakeMirKey::Function(_) | FakeMirKey::Closure(_)),
            |key| match key {
                FakeMirKey::Function(name) | FakeMirKey::Closure(name) => name,
                FakeMirKey::Const(_) | FakeMirKey::Static(_) => {
                    panic!("non-function MIR key reached mapper")
                }
            },
        );

        assert_eq!(lowered, vec!["f", "c"]);
    }

    #[test]
    fn test_allocator_module_spec_from_names_builds_known_wrappers() {
        let cfg_version = "rustc-test-version";
        let spec = allocator_module_spec_from_names(
            "krate",
            cfg_version,
            [sym::alloc, sym::alloc_error_handler],
        )
        .expect("known allocator method names should build a spec");

        let expected_marker =
            rustc_internal_symbol_name(cfg_version, "__rust_no_alloc_shim_is_unstable_v2");
        assert_eq!(spec.module_name, "krate.allocator");
        assert_eq!(
            spec.no_alloc_shim_is_unstable_symbol_name.as_deref(),
            Some(expected_marker.as_str())
        );
        assert_eq!(spec.functions.len(), 2);
        assert_eq!(spec.functions[0].name, "alloc");
        assert_eq!(
            spec.functions[0].wrapper_symbol_name,
            rustc_internal_symbol_name(cfg_version, "__rust_alloc")
        );
        assert_eq!(
            spec.functions[0].callee_symbol_name,
            rustc_internal_symbol_name(cfg_version, "__rdl_alloc")
        );
        assert_eq!(spec.functions[0].kind, bridge_backend::AllocatorFunctionKind::Alloc);
        assert_eq!(spec.functions[0].inputs, vec![bridge_backend::AllocatorArgKind::Layout]);
        assert_eq!(spec.functions[0].output, bridge_backend::AllocatorResultKind::ResultPtr);
        assert_eq!(
            spec.functions[1].kind,
            bridge_backend::AllocatorFunctionKind::AllocErrorHandler
        );
        assert_eq!(spec.functions[1].output, bridge_backend::AllocatorResultKind::Never);
    }

    #[test]
    fn test_allocator_module_spec_from_names_allows_empty_function_set() {
        let cfg_version = "rustc-test-version";
        let spec = allocator_module_spec_from_names("krate", cfg_version, std::iter::empty())
            .expect("empty allocator shim method set should still produce a module spec");

        let expected_marker =
            rustc_internal_symbol_name(cfg_version, "__rust_no_alloc_shim_is_unstable_v2");
        assert_eq!(spec.module_name, "krate.allocator");
        assert!(spec.functions.is_empty());
        assert_eq!(
            spec.no_alloc_shim_is_unstable_symbol_name.as_deref(),
            Some(expected_marker.as_str())
        );
    }

    #[test]
    fn test_allocator_module_spec_from_names_rejects_unknown_methods() {
        let err = allocator_module_spec_from_names(
            "krate",
            "rustc-test-version",
            [Symbol::intern("mystery_alloc")],
        )
        .expect_err("unexpected allocator method names should be rejected");

        assert!(err.contains("mystery_alloc"));
    }

    #[test]
    fn test_apply_direct_call_name_overrides_rewrites_call_terminators() {
        use trust_types::{
            BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
            VerifiableBody,
        };

        let mut func = VerifiableFunction {
            name: "caller".to_string(),
            def_path: "krate::caller".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "krate::helper".to_string(),
                            args: vec![],
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Assert {
                            cond: Operand::Constant(trust_types::ConstValue::Bool(true)),
                            expected: true,
                            msg: trust_types::AssertMessage::Custom("ok".to_string()),
                            target: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: "std::process::exit".to_string(),
                            args: vec![],
                            dest: Place::local(0),
                            target: None,
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        apply_direct_call_name_overrides(
            &mut func,
            &[
                Some("helper".to_string()),
                Some("should_be_ignored".to_string()),
                Some("_RNvCsynth4core3ptr13drop_in_place".to_string()),
            ],
        );

        match &func.body.blocks[0].terminator {
            Terminator::Call { func, .. } => assert_eq!(func, "helper"),
            other => panic!("expected call terminator, got {other:?}"),
        }
        assert!(matches!(func.body.blocks[1].terminator, Terminator::Assert { .. }));
        match &func.body.blocks[2].terminator {
            Terminator::Call { func, .. } => {
                assert_eq!(func, "_RNvCsynth4core3ptr13drop_in_place")
            }
            other => panic!("expected call terminator, got {other:?}"),
        }
    }
}
