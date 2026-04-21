// tRust: Linker argument construction functions, extracted from link.rs
// Author: Andrew Yates <andrew@andrewdyates.com>

use std::collections::BTreeSet;
use std::fs::{self, File};
use std::io;
use std::ops::{ControlFlow, Deref};
use std::path::{Path, PathBuf};

use object::{Object, ObjectSection, ObjectSymbol};
use rustc_data_structures::fx::{FxHashSet, FxIndexSet};
use rustc_data_structures::memmap::Mmap;
use rustc_fs_util::fix_windows_verbatim_for_gcc;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_metadata::fs::emit_wrapper_file;
use rustc_metadata::{NativeLibSearchFallback, find_native_static_library, walk_native_lib_search_dirs};
use rustc_middle::middle::debugger_visualizer::DebuggerVisualizerFile;
use rustc_middle::middle::dependency_format::Linkage;
use rustc_middle::middle::exported_symbols::SymbolExportKind;
use rustc_session::Session;
use rustc_session::config::{self, CrateType, CFGuard, SplitDwarfKind};
use rustc_target::spec::{
    BinaryFormat, Cc, LinkOutputKind, LinkSelfContainedComponents, LinkerFlavor, LinkerFeatures,
    Lld, Os, RelroLevel, SanitizerSet,
};
use rustc_span::Symbol;
use tracing::debug;

use super::apple_link;
use super::lld;
use super::raw_dylib;
use super::super::archive::ArchiveBuilderBuilder;
use super::super::command::Command;
use super::super::linker::{self, Linker};
use super::super::metadata::create_wrapper_file;
use super::super::rpath::{self, RPathConfig};
use super::super::{apple, versioned_llvm_target};
use crate::base::needs_allocator_shim_for_linking;
use crate::{CompiledModule, CompiledModules, CrateInfo, NativeLib, errors};

/// Add pre-link object files defined by the target spec.
pub(super) fn add_pre_link_objects(
    cmd: &mut dyn Linker,
    sess: &Session,
    flavor: LinkerFlavor,
    link_output_kind: LinkOutputKind,
    self_contained: bool,
) {
    // NOTE: Missing per-linker-flavor CRT object infrastructure.
    // so Fuchsia has to be special-cased.
    let opts = &sess.target;
    let empty = Default::default();
    let objects = if self_contained {
        &opts.pre_link_objects_self_contained
    } else if !(sess.target.os == Os::Fuchsia && matches!(flavor, LinkerFlavor::Gnu(Cc::Yes, _))) {
        &opts.pre_link_objects
    } else {
        &empty
    };
    for obj in objects.get(&link_output_kind).iter().copied().flatten() {
        cmd.add_object(&super::get_object_file_path(sess, obj, self_contained));
    }
}

/// Add post-link object files defined by the target spec.
pub(super) fn add_post_link_objects(
    cmd: &mut dyn Linker,
    sess: &Session,
    link_output_kind: LinkOutputKind,
    self_contained: bool,
) {
    let objects = if self_contained {
        &sess.target.post_link_objects_self_contained
    } else {
        &sess.target.post_link_objects
    };
    for obj in objects.get(&link_output_kind).iter().copied().flatten() {
        cmd.add_object(&super::get_object_file_path(sess, obj, self_contained));
    }
}

/// Add arbitrary "pre-link" args defined by the target spec or from command line.
/// NOTE: Exact insertion point for these args needs further analysis.
pub(super) fn add_pre_link_args(cmd: &mut dyn Linker, sess: &Session, flavor: LinkerFlavor) {
    if let Some(args) = sess.target.pre_link_args.get(&flavor) {
        cmd.verbatim_args(args.iter().map(Deref::deref));
    }

    cmd.verbatim_args(&sess.opts.unstable_opts.pre_link_args);
}

/// Add a link script embedded in the target, if applicable.
pub(super) fn add_link_script(cmd: &mut dyn Linker, sess: &Session, tmpdir: &Path, crate_type: CrateType) {
    match (crate_type, &sess.target.link_script) {
        (CrateType::Cdylib | CrateType::Executable, Some(script)) => {
            if !sess.target.linker_flavor.is_gnu() {
                sess.dcx().emit_fatal(errors::LinkScriptUnavailable);
            }

            let file_name = ["rustc", &sess.target.llvm_target, "linkfile.ld"].join("-");

            let path = tmpdir.join(file_name);
            if let Err(error) = fs::write(&path, script.as_ref()) {
                sess.dcx().emit_fatal(errors::LinkScriptWriteFailure { path, error });
            }

            cmd.link_arg("--script").link_arg(path);
        }
        _ => {}
    }
}

/// Add arbitrary "user defined" args defined from command line.
/// NOTE: Exact insertion point for these args needs further analysis.
pub(super) fn add_user_defined_link_args(cmd: &mut dyn Linker, sess: &Session) {
    cmd.verbatim_args(&sess.opts.cg.link_args);
}

/// Add arbitrary "late link" args defined by the target spec.
/// NOTE: Exact insertion point for these args needs further analysis.
pub(super) fn add_late_link_args(
    cmd: &mut dyn Linker,
    sess: &Session,
    flavor: LinkerFlavor,
    crate_type: CrateType,
    crate_info: &CrateInfo,
) {
    let any_dynamic_crate = crate_type == CrateType::Dylib
        || crate_type == CrateType::Sdylib
        || crate_info.dependency_formats.iter().any(|(ty, list)| {
            *ty == crate_type && list.iter().any(|&linkage| linkage == Linkage::Dynamic)
        });
    if any_dynamic_crate {
        if let Some(args) = sess.target.late_link_args_dynamic.get(&flavor) {
            cmd.verbatim_args(args.iter().map(Deref::deref));
        }
    } else if let Some(args) = sess.target.late_link_args_static.get(&flavor) {
        cmd.verbatim_args(args.iter().map(Deref::deref));
    }
    if let Some(args) = sess.target.late_link_args.get(&flavor) {
        cmd.verbatim_args(args.iter().map(Deref::deref));
    }
}

/// Add arbitrary "post-link" args defined by the target spec.
/// NOTE: Exact insertion point for these args needs further analysis.
pub(super) fn add_post_link_args(cmd: &mut dyn Linker, sess: &Session, flavor: LinkerFlavor) {
    if let Some(args) = sess.target.post_link_args.get(&flavor) {
        cmd.verbatim_args(args.iter().map(Deref::deref));
    }
}

/// Add a synthetic object file that contains reference to all symbols that we want to expose to
/// the linker.
///
/// Background: we implement rlibs as static library (archives). Linkers treat archives
/// differently from object files: all object files participate in linking, while archives will
/// only participate in linking if they can satisfy at least one undefined reference (version
/// scripts doesn't count). This causes `#[no_mangle]` or `#[used]` items to be ignored by the
/// linker, and since they never participate in the linking, using `KEEP` in the linker scripts
/// can't keep them either. This causes #47384.
///
/// To keep them around, we could use `--whole-archive`, `-force_load` and equivalents to force rlib
/// to participate in linking like object files, but this proves to be expensive (#93791). Therefore
/// we instead just introduce an undefined reference to them. This could be done by `-u` command
/// line option to the linker or `EXTERN(...)` in linker scripts, however they does not only
/// introduce an undefined reference, but also make them the GC roots, preventing `--gc-sections`
/// from removing them, and this is especially problematic for embedded programming where every
/// byte counts.
///
/// This method creates a synthetic object file, which contains undefined references to all symbols
/// that are necessary for the linking. They are only present in symbol table but not actually
/// used in any sections, so the linker will therefore pick relevant rlibs for linking, but
/// unused `#[no_mangle]` or `#[used(compiler)]` can still be discard by GC sections.
///
/// There's a few internal crates in the standard library (aka libcore and
/// libstd) which actually have a circular dependence upon one another. This
/// currently arises through "weak lang items" where libcore requires things
/// like `rust_begin_unwind` but libstd ends up defining it. To get this
/// circular dependence to work correctly we declare some of these things
/// in this synthetic object.
pub(super) fn add_linked_symbol_object(
    cmd: &mut dyn Linker,
    sess: &Session,
    tmpdir: &Path,
    symbols: &[(String, SymbolExportKind)],
) {
    if symbols.is_empty() {
        return;
    }

    let Some(mut file) = super::super::metadata::create_object_file(sess) else {
        return;
    };

    if file.format() == object::BinaryFormat::Coff {
        // NOTE(nbdd0121): MSVC will hang if the input object file contains no sections,
        // so add an empty section.
        file.add_section(Vec::new(), ".text".into(), object::SectionKind::Text);

        // We handle the name decoration of COFF targets in `symbol_export.rs`, so disable the
        // default mangler in `object` crate.
        file.set_mangling(object::write::Mangling::None);
    }

    if file.format() == object::BinaryFormat::MachO {
        // Divide up the sections into sub-sections via symbols for dead code stripping.
        // Without this flag, unused `#[no_mangle]` or `#[used(compiler)]` cannot be
        // discard on MachO targets.
        file.set_subsections_via_symbols();
    }

    // ld64 requires a relocation to load undefined symbols, see below.
    // Not strictly needed if linking with lld, but might as well do it there too.
    let ld64_section_helper = if file.format() == object::BinaryFormat::MachO {
        Some(file.add_section(
            file.segment_name(object::write::StandardSegment::Data).to_vec(),
            "__data".into(),
            object::SectionKind::Data,
        ))
    } else {
        None
    };

    for (sym, kind) in symbols.iter() {
        let symbol = file.add_symbol(object::write::Symbol {
            name: sym.clone().into(),
            value: 0,
            size: 0,
            kind: match kind {
                SymbolExportKind::Text => object::SymbolKind::Text,
                SymbolExportKind::Data => object::SymbolKind::Data,
                SymbolExportKind::Tls => object::SymbolKind::Tls,
            },
            scope: object::SymbolScope::Unknown,
            weak: false,
            section: object::write::SymbolSection::Undefined,
            flags: object::SymbolFlags::None,
        });

        // The linker shipped with Apple's Xcode, ld64, works a bit differently from other linkers.
        //
        // Code-wise, the relevant parts of ld64 are roughly:
        // 1. Find the `ArchiveLoadMode` based on commandline options, default to `parseObjects`.
        //    https://github.com/apple-oss-distributions/ld64/blob/ld64-954.16/src/ld/Options.cpp#L924-L932
        //    https://github.com/apple-oss-distributions/ld64/blob/ld64-954.16/src/ld/Options.h#L55
        //
        // 2. Read the archive table of contents (__.SYMDEF file).
        //    https://github.com/apple-oss-distributions/ld64/blob/ld64-954.16/src/ld/parsers/archive_file.cpp#L294-L325
        //
        // 3. Begin linking by loading "atoms" from input files.
        //    https://github.com/apple-oss-distributions/ld64/blob/ld64-954.16/doc/design/linker.html
        //    https://github.com/apple-oss-distributions/ld64/blob/ld64-954.16/src/ld/InputFiles.cpp#L1349
        //
        //   a. Directly specified object files (`.o`) are parsed immediately.
        //      https://github.com/apple-oss-distributions/ld64/blob/ld64-954.16/src/ld/parsers/macho_relocatable_file.cpp#L4611-L4627
        //
        //     - Undefined symbols are not atoms (`n_value > 0` denotes a common symbol).
        //       https://github.com/apple-oss-distributions/ld64/blob/ld64-954.16/src/ld/parsers/macho_relocatable_file.cpp#L2455-L2468
        //       https://maskray.me/blog/2022-02-06-all-about-common-symbols
        //
        //     - Relocations/fixups are atoms.
        //       https://github.com/apple-oss-distributions/ld64/blob/ce6341ae966b3451aa54eeb049f2be865afbd578/src/ld/parsers/macho_relocatable_file.cpp#L2088-L2114
        //
        //   b. Archives are not parsed yet.
        //      https://github.com/apple-oss-distributions/ld64/blob/ld64-954.16/src/ld/parsers/archive_file.cpp#L467-L577
        //
        // 4. When a symbol is needed by an atom, parse the object file that contains the symbol.
        //    https://github.com/apple-oss-distributions/ld64/blob/ld64-954.16/src/ld/InputFiles.cpp#L1417-L1491
        //    https://github.com/apple-oss-distributions/ld64/blob/ld64-954.16/src/ld/parsers/archive_file.cpp#L579-L597
        //
        // All of the steps above are fairly similar to other linkers, except that **it completely
        // ignores undefined symbols**.
        //
        // So to make this trick work on ld64, we need to do something else to load the relevant
        // object files. We do this by inserting a relocation (fixup) for each symbol.
        if let Some(section) = ld64_section_helper {
            apple::add_data_and_relocation(&mut file, section, symbol, &sess.target, *kind)
                .expect("failed adding relocation");
        }
    }

    let path = tmpdir.join("symbols.o");
    let result = std::fs::write(&path, file.write().expect("invariant: object file serialization must succeed"));
    if let Err(error) = result {
        sess.dcx().emit_fatal(errors::FailedToWrite { path, error });
    }
    cmd.add_object(&path);
}

/// Add object files containing code from the current crate.
pub(super) fn add_local_crate_regular_objects(cmd: &mut dyn Linker, compiled_modules: &CompiledModules) {
    for obj in compiled_modules.modules.iter().filter_map(|m| m.object.as_ref()) {
        cmd.add_object(obj);
    }
}

/// Add object files for allocator code linked once for the whole crate tree.
pub(super) fn add_local_crate_allocator_objects(
    cmd: &mut dyn Linker,
    compiled_modules: &CompiledModules,
    crate_info: &CrateInfo,
    crate_type: CrateType,
) {
    if needs_allocator_shim_for_linking(&crate_info.dependency_formats, crate_type) {
        if let Some(obj) =
            compiled_modules.allocator_module.as_ref().and_then(|m| m.object.as_ref())
        {
            cmd.add_object(obj);
        }
    }
}

/// Add object files containing metadata for the current crate.
pub(super) fn add_local_crate_metadata_objects(
    cmd: &mut dyn Linker,
    sess: &Session,
    archive_builder_builder: &dyn ArchiveBuilderBuilder,
    crate_type: CrateType,
    tmpdir: &Path,
    crate_info: &CrateInfo,
    metadata: &rustc_metadata::EncodedMetadata,
) {
    // When linking a dynamic library, we put the metadata into a section of the
    // executable. This metadata is in a separate object file from the main
    // object file, so we create and link it in here.
    if matches!(crate_type, CrateType::Dylib | CrateType::ProcMacro) {
        let data = archive_builder_builder.create_dylib_metadata_wrapper(
            sess,
            &metadata,
            &crate_info.metadata_symbol,
        );
        let obj = emit_wrapper_file(sess, &data, tmpdir, "rmeta.o");

        cmd.add_object(&obj);
    }
}

/// Add sysroot and other globally set directories to the directory search list.
pub(super) fn add_library_search_dirs(
    cmd: &mut dyn Linker,
    sess: &Session,
    self_contained_components: LinkSelfContainedComponents,
    apple_sdk_root: Option<&Path>,
) {
    if !sess.opts.unstable_opts.link_native_libraries {
        return;
    }

    let fallback = Some(NativeLibSearchFallback { self_contained_components, apple_sdk_root });
    let _ = walk_native_lib_search_dirs(sess, fallback, |dir, is_framework| {
        if is_framework {
            cmd.framework_path(dir);
        } else {
            cmd.include_path(&fix_windows_verbatim_for_gcc(dir));
        }
        ControlFlow::<()>::Continue(())
    });
}

/// Add options making relocation sections in the produced ELF files read-only
/// and suppressing lazy binding.
pub(super) fn add_relro_args(cmd: &mut dyn Linker, sess: &Session) {
    match sess.opts.cg.relro_level.unwrap_or(sess.target.relro_level) {
        RelroLevel::Full => cmd.full_relro(),
        RelroLevel::Partial => cmd.partial_relro(),
        RelroLevel::Off => cmd.no_relro(),
        RelroLevel::None => {}
    }
}

/// Add library search paths used at runtime by dynamic linkers.
pub(super) fn add_rpath_args(
    cmd: &mut dyn Linker,
    sess: &Session,
    crate_info: &CrateInfo,
    out_filename: &Path,
) {
    if !sess.target.has_rpath {
        return;
    }

    // NOTE(#2397): Rpath guesses for library search paths not yet implemented.
    // where extern libraries might live, based on the
    // add_lib_search_paths
    if sess.opts.cg.rpath {
        let libs = crate_info
            .used_crates
            .iter()
            .filter_map(|cnum| crate_info.used_crate_source[cnum].dylib.as_deref())
            .collect::<Vec<_>>();
        let rpath_config = RPathConfig {
            libs: &*libs,
            out_filename: out_filename.to_path_buf(),
            is_like_darwin: sess.target.is_like_darwin,
            linker_is_gnu: sess.target.linker_flavor.is_gnu(),
        };
        cmd.link_args(&rpath::get_rpath_linker_args(&rpath_config));
    }
}

pub(super) fn add_c_staticlib_symbols(
    sess: &Session,
    lib: &NativeLib,
    out: &mut Vec<(String, SymbolExportKind)>,
) -> io::Result<()> {
    let file_path = find_native_static_library(lib.name.as_str(), lib.verbatim, sess);

    // SAFETY: `File::open` returns a valid, open file handle. `Mmap::map` requires // tRust:
    // the file to remain open and unmodified for the lifetime of the mapping. The
    // `archive_map` lives for the duration of this function, during which the
    // underlying static library file is not modified by the compiler.
    // SAFETY: `File::open(&file_path)` yielded a valid handle, and this static
    // library is only read while the mapping lives in this function.
    let archive_map = unsafe { Mmap::map(File::open(&file_path)?)? };

    let archive = object::read::archive::ArchiveFile::parse(&*archive_map)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

    for member in archive.members() {
        let member = member.map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        let data = member
            .data(&*archive_map)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        // clang LTO: raw LLVM bitcode
        if data.starts_with(b"BC\xc0\xde") {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "LLVM bitcode object in C static library (LTO not supported)",
            ));
        }

        let object = object::File::parse(&*data)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        // gcc / clang ELF / Mach-O LTO
        if object.sections().any(|s| {
            s.name().map(|n| n.starts_with(".gnu.lto_") || n == ".llvm.lto").unwrap_or(false)
        }) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "LTO object in C static library is not supported",
            ));
        }

        for symbol in object.symbols() {
            if symbol.scope() != object::SymbolScope::Dynamic {
                continue;
            }

            let name = match symbol.name() {
                Ok(n) => n,
                Err(_) => continue,
            };

            let export_kind = match symbol.kind() {
                object::SymbolKind::Text => SymbolExportKind::Text,
                object::SymbolKind::Data => SymbolExportKind::Data,
                _ => continue,
            };

            // NOTE: Symbol mangle rules differ slightly on Windows (32-bit) and Apple platforms.
            // Need to be resolved.
            out.push((name.to_string(), export_kind));
        }
    }

    Ok(())
}

/// Produce the linker command line containing linker path and arguments.
///
/// When comments in the function say "order-(in)dependent" they mean order-dependence between
/// options and libraries/object files. For example `--whole-archive` (order-dependent) applies
/// to specific libraries passed after it, and `-o` (output file, order-independent) applies
/// to the linking process as a whole.
/// Order-independent options may still override each other in order-dependent fashion,
/// e.g `--foo=yes --foo=no` may be equivalent to `--foo=no`.
pub(super) fn linker_with_args(
    path: &Path,
    flavor: LinkerFlavor,
    sess: &Session,
    archive_builder_builder: &dyn ArchiveBuilderBuilder,
    crate_type: CrateType,
    tmpdir: &Path,
    out_filename: &Path,
    compiled_modules: &CompiledModules,
    crate_info: &CrateInfo,
    metadata: &rustc_metadata::EncodedMetadata,
    self_contained_components: LinkSelfContainedComponents,
    codegen_backend: &'static str,
) -> Command {
    let self_contained_crt_objects = self_contained_components.is_crt_objects_enabled();
    let cmd = &mut *linker::get_linker(
        sess,
        path,
        flavor,
        self_contained_components.are_any_components_enabled(),
        &crate_info.target_cpu,
        codegen_backend,
    );
    let link_output_kind = super::link_output_kind(sess, crate_type);

    let mut export_symbols = crate_info.exported_symbols[&crate_type].clone();

    if crate_type == CrateType::Cdylib {
        let mut seen = FxHashSet::default();

        for lib in &crate_info.used_libraries {
            if let rustc_hir::attrs::NativeLibKind::Static { export_symbols: Some(true), .. } = lib.kind
                && seen.insert((lib.name, lib.verbatim))
            {
                if let Err(err) = add_c_staticlib_symbols(&sess, lib, &mut export_symbols) {
                    sess.dcx().fatal(format!(
                        "failed to process C static library `{}`: {}",
                        lib.name, err
                    ));
                }
            }
        }
    }

    // ------------ Early order-dependent options ------------

    // If we're building something like a dynamic library then some platforms
    // need to make sure that all symbols are exported correctly from the
    // dynamic library.
    // Must be passed before any libraries to prevent the symbols to export from being thrown away,
    // at least on some platforms (e.g. windows-gnu).
    cmd.export_symbols(tmpdir, crate_type, &export_symbols);

    // Can be used for adding custom CRT objects or overriding order-dependent options above.
    // NOTE: Built-in target specs use this for arbitrary order-independent options.
    // introduce a target spec option for order-independent linker options and migrate built-in
    // specs to it.
    add_pre_link_args(cmd, sess, flavor);

    // ------------ Object code and libraries, order-dependent ------------

    // Pre-link CRT objects.
    add_pre_link_objects(cmd, sess, flavor, link_output_kind, self_contained_crt_objects);

    add_linked_symbol_object(cmd, sess, tmpdir, &crate_info.linked_symbols[&crate_type]);

    // Sanitizer libraries.
    super::add_sanitizer_libraries(sess, flavor, crate_type, cmd);

    // Object code from the current crate.
    // Take careful note of the ordering of the arguments we pass to the linker
    // here. Linkers will assume that things on the left depend on things to the
    // right. Things on the right cannot depend on things on the left. This is
    // all formally implemented in terms of resolving symbols (libs on the right
    // resolve unknown symbols of libs on the left, but not vice versa).
    //
    // For this reason, we have organized the arguments we pass to the linker as
    // such:
    //
    // 1. The local object that LLVM just generated
    // 2. Local native libraries
    // 3. Upstream rust libraries
    // 4. Upstream native libraries
    //
    // The rationale behind this ordering is that those items lower down in the
    // list can't depend on items higher up in the list. For example nothing can
    // depend on what we just generated (e.g., that'd be a circular dependency).
    // Upstream rust libraries are not supposed to depend on our local native
    // libraries as that would violate the structure of the DAG, in that
    // scenario they are required to link to them as well in a shared fashion.
    //
    // Note that upstream rust libraries may contain native dependencies as
    // well, but they also can't depend on what we just started to add to the
    // link line. And finally upstream native libraries can't depend on anything
    // in this DAG so far because they can only depend on other native libraries
    // and such dependencies are also required to be specified.
    add_local_crate_regular_objects(cmd, compiled_modules);
    add_local_crate_metadata_objects(
        cmd,
        sess,
        archive_builder_builder,
        crate_type,
        tmpdir,
        crate_info,
        metadata,
    );
    add_local_crate_allocator_objects(cmd, compiled_modules, crate_info, crate_type);

    // Avoid linking to dynamic libraries unless they satisfy some undefined symbols
    // at the point at which they are specified on the command line.
    // Must be passed before any (dynamic) libraries to have effect on them.
    // On Solaris-like systems, `-z ignore` acts as both `--as-needed` and `--gc-sections`
    // so it will ignore unreferenced ELF sections from relocatable objects.
    // For that reason, we put this flag after metadata objects as they would otherwise be removed.
    // NOTE: Dead code removal on Solaris/illumos is coarse-grained; more fine-grained support desired.
    // and move this option back to the top.
    cmd.add_as_needed();

    // Local native libraries of all kinds.
    super::add_local_native_libraries(
        cmd,
        sess,
        archive_builder_builder,
        crate_info,
        tmpdir,
        link_output_kind,
    );

    // Upstream rust crates and their non-dynamic native libraries.
    super::add_upstream_rust_crates(
        cmd,
        sess,
        archive_builder_builder,
        crate_info,
        crate_type,
        tmpdir,
        link_output_kind,
    );

    // Dynamic native libraries from upstream crates.
    super::add_upstream_native_libraries(
        cmd,
        sess,
        archive_builder_builder,
        crate_info,
        tmpdir,
        link_output_kind,
    );

    // Raw-dylibs from all crates.
    let raw_dylib_dir = tmpdir.join("raw-dylibs");
    if sess.target.binary_format == BinaryFormat::Elf {
        // On ELF we can't pass the raw-dylibs stubs to the linker as a path,
        // instead we need to pass them via -l. To find the stub, we need to add
        // the directory of the stub to the linker search path.
        // We make an extra directory for this to avoid polluting the search path.
        if let Err(error) = fs::create_dir(&raw_dylib_dir) {
            sess.dcx().emit_fatal(errors::CreateTempDir { error })
        }
        cmd.include_path(&raw_dylib_dir);
    }

    // Link with the import library generated for any raw-dylib functions.
    if sess.target.is_like_windows {
        for output_path in raw_dylib::create_raw_dylib_dll_import_libs(
            sess,
            archive_builder_builder,
            crate_info.used_libraries.iter(),
            tmpdir,
            true,
        ) {
            cmd.add_object(&output_path);
        }
    } else {
        for (link_path, as_needed) in raw_dylib::create_raw_dylib_elf_stub_shared_objects(
            sess,
            crate_info.used_libraries.iter(),
            &raw_dylib_dir,
        ) {
            // Always use verbatim linkage, see comments in create_raw_dylib_elf_stub_shared_objects.
            cmd.link_dylib_by_name(&link_path, true, as_needed);
        }
    }
    // As with add_upstream_native_libraries, we need to add the upstream raw-dylib symbols in case
    // they are used within inlined functions or instantiated generic functions. We do this *after*
    // handling the raw-dylib symbols in the current crate to make sure that those are chosen first
    // by the linker.
    let dependency_linkage = crate_info
        .dependency_formats
        .get(&crate_type)
        .expect("failed to find crate type in dependency format list");

    // We sort the libraries below
    #[allow(rustc::potential_query_instability)]
    let mut native_libraries_from_nonstatics = crate_info
        .native_libraries
        .iter()
        .filter_map(|(&cnum, libraries)| {
            if sess.target.is_like_windows {
                (dependency_linkage[cnum] != Linkage::Static).then_some(libraries)
            } else {
                Some(libraries)
            }
        })
        .flatten()
        .collect::<Vec<_>>();
    native_libraries_from_nonstatics.sort_unstable_by(|a, b| a.name.as_str().cmp(b.name.as_str()));

    if sess.target.is_like_windows {
        for output_path in raw_dylib::create_raw_dylib_dll_import_libs(
            sess,
            archive_builder_builder,
            native_libraries_from_nonstatics,
            tmpdir,
            false,
        ) {
            cmd.add_object(&output_path);
        }
    } else {
        for (link_path, as_needed) in raw_dylib::create_raw_dylib_elf_stub_shared_objects(
            sess,
            native_libraries_from_nonstatics,
            &raw_dylib_dir,
        ) {
            // Always use verbatim linkage, see comments in create_raw_dylib_elf_stub_shared_objects.
            cmd.link_dylib_by_name(&link_path, true, as_needed);
        }
    }

    // Library linking above uses some global state for things like `-Bstatic`/`-Bdynamic` to make
    // command line shorter, reset it to default here before adding more libraries.
    cmd.reset_per_library_state();

    // NOTE: Built-in target specs use this for linking system libraries.
    // eliminate all such uses by migrating them to `#[link]` attributes in `lib(std,c,unwind)`
    // and remove the option.
    add_late_link_args(cmd, sess, flavor, crate_type, crate_info);

    // ------------ Arbitrary order-independent options ------------

    // Add order-independent options determined by rustc from its compiler options,
    // target properties and source code.
    add_order_independent_options(
        cmd,
        sess,
        link_output_kind,
        self_contained_components,
        flavor,
        crate_type,
        crate_info,
        out_filename,
        tmpdir,
    );

    // Can be used for arbitrary order-independent options.
    // In practice may also be occasionally used for linking native libraries.
    // Passed after compiler-generated options to support manual overriding when necessary.
    add_user_defined_link_args(cmd, sess);

    // ------------ Builtin configurable linker scripts ------------
    // The user's link args should be able to overwrite symbols in the compiler's
    // linker script that were weakly defined (i.e. defined with `PROVIDE()`). For this
    // to work correctly, the user needs to be able to specify linker arguments like
    // `--defsym` and `--script` *before* any builtin linker scripts are evaluated.
    add_link_script(cmd, sess, tmpdir, crate_type);

    // ------------ Object code and libraries, order-dependent ------------

    // Post-link CRT objects.
    add_post_link_objects(cmd, sess, link_output_kind, self_contained_crt_objects);

    // ------------ Late order-dependent options ------------

    // Doesn't really make sense.
    // NOTE: Built-in target specs use this for arbitrary order-independent options.
    // Introduce a target spec option for order-independent linker options, migrate built-in specs
    // to it and remove the option. Currently the last holdout is wasm32-unknown-emscripten.
    add_post_link_args(cmd, sess, flavor);

    cmd.take_cmd()
}

fn add_order_independent_options(
    cmd: &mut dyn Linker,
    sess: &Session,
    link_output_kind: LinkOutputKind,
    self_contained_components: LinkSelfContainedComponents,
    flavor: LinkerFlavor,
    crate_type: CrateType,
    crate_info: &CrateInfo,
    out_filename: &Path,
    tmpdir: &Path,
) {
    // Take care of the flavors and CLI options requesting the `lld` linker.
    lld::add_lld_args(cmd, sess, flavor, self_contained_components);

    apple_link::add_apple_link_args(cmd, sess, flavor);

    let apple_sdk_root = apple_link::add_apple_sdk(cmd, sess, flavor);

    if sess.target.os == Os::Fuchsia
        && crate_type == CrateType::Executable
        && !matches!(flavor, LinkerFlavor::Gnu(Cc::Yes, _))
    {
        let prefix = if sess.sanitizers().contains(SanitizerSet::ADDRESS) { "asan/" } else { "" };
        cmd.link_arg(format!("--dynamic-linker={prefix}ld.so.1"));
    }

    if sess.target.eh_frame_header {
        cmd.add_eh_frame_header();
    }

    // Make the binary compatible with data execution prevention schemes.
    cmd.add_no_exec();

    if self_contained_components.is_crt_objects_enabled() {
        cmd.no_crt_objects();
    }

    if sess.target.os == Os::Emscripten {
        cmd.cc_arg(if sess.opts.unstable_opts.emscripten_wasm_eh {
            "-fwasm-exceptions"
        } else if sess.panic_strategy().unwinds() {
            "-sDISABLE_EXCEPTION_CATCHING=0"
        } else {
            "-sDISABLE_EXCEPTION_CATCHING=1"
        });
    }

    if flavor == LinkerFlavor::Llbc {
        cmd.link_args(&[
            "--target",
            &versioned_llvm_target(sess),
            "--target-cpu",
            &crate_info.target_cpu,
        ]);
        if crate_info.target_features.len() > 0 {
            cmd.link_arg(&format!("--target-feature={}", &crate_info.target_features.join(",")));
        }
    } else if flavor == LinkerFlavor::Ptx {
        cmd.link_args(&["--fallback-arch", &crate_info.target_cpu]);
    } else if flavor == LinkerFlavor::Bpf {
        cmd.link_args(&["--cpu", &crate_info.target_cpu]);
        if let Some(feat) = [sess.opts.cg.target_feature.as_str(), &sess.target.options.features]
            .into_iter()
            .find(|feat| !feat.is_empty())
        {
            cmd.link_args(&["--cpu-features", feat]);
        }
    }

    cmd.linker_plugin_lto();

    add_library_search_dirs(cmd, sess, self_contained_components, apple_sdk_root.as_deref());

    cmd.output_filename(out_filename);

    if crate_type == CrateType::Executable
        && sess.target.is_like_windows
        && let Some(s) = &crate_info.windows_subsystem
    {
        cmd.windows_subsystem(*s);
    }

    // Try to strip as much out of the generated object by removing unused
    // sections if possible. See more comments in linker.rs
    if !sess.link_dead_code() {
        // If PGO is enabled sometimes gc_sections will remove the profile data section
        // as it appears to be unused. This can then cause the PGO profile file to lose
        // some functions. If we are generating a profile we shouldn't strip those metadata
        // sections to ensure we have all the data for PGO.
        let keep_metadata =
            crate_type == CrateType::Dylib || sess.opts.cg.profile_generate.enabled();
        cmd.gc_sections(keep_metadata);
    }

    cmd.set_output_kind(link_output_kind, crate_type, out_filename);

    add_relro_args(cmd, sess);

    // Pass optimization flags down to the linker.
    cmd.optimize();

    // Gather the set of NatVis files, if any, and write them out to a temp directory.
    let natvis_visualizers = collect_natvis_visualizers(
        tmpdir,
        sess,
        &crate_info.local_crate_name,
        &crate_info.natvis_debugger_visualizers,
    );

    // Pass debuginfo, NatVis debugger visualizers and strip flags down to the linker.
    cmd.debuginfo(sess.opts.cg.strip, &natvis_visualizers);

    // We want to prevent the compiler from accidentally leaking in any system libraries,
    // so by default we tell linkers not to link to any default libraries.
    if !sess.opts.cg.default_linker_libraries && sess.target.no_default_libraries {
        cmd.no_default_libraries();
    }

    if sess.opts.cg.profile_generate.enabled() || sess.instrument_coverage() {
        cmd.pgo_gen();
    }

    if sess.opts.unstable_opts.instrument_mcount {
        cmd.enable_profiling();
    }

    if sess.opts.cg.control_flow_guard != CFGuard::Disabled {
        cmd.control_flow_guard();
    }

    // OBJECT-FILES-NO, AUDIT-ORDER
    if sess.opts.unstable_opts.ehcont_guard {
        cmd.ehcont_guard();
    }

    add_rpath_args(cmd, sess, crate_info, out_filename);
}

// Write the NatVis debugger visualizer files for each crate to the temp directory and gather the file paths.
fn collect_natvis_visualizers(
    tmpdir: &Path,
    sess: &Session,
    crate_name: &Symbol,
    natvis_debugger_visualizers: &BTreeSet<DebuggerVisualizerFile>,
) -> Vec<PathBuf> {
    let mut visualizer_paths = Vec::with_capacity(natvis_debugger_visualizers.len());

    for (index, visualizer) in natvis_debugger_visualizers.iter().enumerate() {
        let visualizer_out_file = tmpdir.join(format!("{}-{}.natvis", crate_name.as_str(), index));

        match fs::write(&visualizer_out_file, &visualizer.src) {
            Ok(()) => {
                visualizer_paths.push(visualizer_out_file);
            }
            Err(error) => {
                sess.dcx().emit_warn(errors::UnableToWriteDebuggerVisualizer {
                    path: visualizer_out_file,
                    error,
                });
            }
        };
    }
    visualizer_paths
}
