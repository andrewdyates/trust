//! tRust: Main linker driver that orchestrates object files, libraries, and system
//! tRust: components into final crate artifacts.

mod apple_link;
mod linker_args;
mod lld;
mod raw_dylib;

use std::collections::BTreeSet;
use std::ffi::OsString;
use std::fs::{File, OpenOptions, read};
use std::io::{BufReader, BufWriter, Write};
use std::ops::{ControlFlow, Deref};
use std::path::{Path, PathBuf};
use std::process::{Output, Stdio};
use std::{env, fmt, fs, io, mem, str};

use find_msvc_tools;
use itertools::Itertools;
use object::{Object, ObjectSection, ObjectSymbol};
use regex::Regex;
use rustc_arena::TypedArena;
use rustc_attr_parsing::eval_config_entry;
use rustc_data_structures::fx::{FxHashSet, FxIndexSet};
use rustc_data_structures::memmap::Mmap;
use rustc_data_structures::temp_dir::MaybeTempDir;
use rustc_errors::DiagCtxtHandle;
use rustc_fs_util::{TempDirBuilder, fix_windows_verbatim_for_gcc, try_canonicalize};
use rustc_hir::attrs::NativeLibKind;
use rustc_hir::def_id::{CrateNum, LOCAL_CRATE};
use rustc_lint_defs::builtin::LINKER_INFO;
use rustc_macros::Diagnostic;
use rustc_metadata::fs::{METADATA_FILENAME, copy_to_stdout, emit_wrapper_file};
use rustc_metadata::{
    EncodedMetadata, NativeLibSearchFallback, find_native_static_library,
    walk_native_lib_search_dirs,
};
use rustc_middle::bug;
use rustc_middle::lint::emit_lint_base;
use rustc_middle::middle::debugger_visualizer::DebuggerVisualizerFile;
use rustc_middle::middle::dependency_format::Linkage;
use rustc_middle::middle::exported_symbols::SymbolExportKind;
use rustc_session::config::{
    self, CFGuard, CrateType, DebugInfo, LinkerFeaturesCli, OutFileName, OutputFilenames,
    OutputType, PrintKind, SplitDwarfKind, Strip,
};
use rustc_session::lint::builtin::LINKER_MESSAGES;
use rustc_session::output::{check_file_is_writeable, invalid_output_for_target, out_filename};
use rustc_session::search_paths::PathKind;
/// For all the linkers we support, and information they might
/// need out of the shared crate context before we get rid of it.
use rustc_session::{Session, filesearch};
use rustc_span::Symbol;
use rustc_target::spec::crt_objects::CrtObjects;
use rustc_target::spec::{
    BinaryFormat, Cc, CfgAbi, Env, LinkOutputKind, LinkSelfContainedComponents,
    LinkSelfContainedDefault, LinkerFeatures, LinkerFlavor, LinkerFlavorCli, Lld, Os, RelocModel,
    RelroLevel, SanitizerSet, SplitDebuginfo,
};
use tracing::{debug, info, warn};

use super::archive::{ArchiveBuilder, ArchiveBuilderBuilder};
use super::command::Command;
use super::linker::{self, Linker};
use super::metadata::{MetadataPosition, create_wrapper_file};
use super::rpath::{self, RPathConfig};
use super::{apple, versioned_llvm_target};
use crate::base::needs_allocator_shim_for_linking;
use crate::{
    CodegenLintLevels, CompiledModule, CompiledModules, CrateInfo, NativeLib, errors,
    looks_like_rust_object_file,
};

pub fn ensure_removed(dcx: DiagCtxtHandle<'_>, path: &Path) {
    if let Err(e) = fs::remove_file(path) {
        if e.kind() != io::ErrorKind::NotFound {
            dcx.err(format!("failed to remove {}: {}", path.display(), e));
        }
    }
}

/// Performs the linkage portion of the compilation phase. This will generate all
/// of the requested outputs for this compilation session.
pub fn link_binary(
    sess: &Session,
    archive_builder_builder: &dyn ArchiveBuilderBuilder,
    compiled_modules: CompiledModules,
    crate_info: CrateInfo,
    metadata: EncodedMetadata,
    outputs: &OutputFilenames,
    codegen_backend: &'static str,
) {
    let _timer = sess.timer("link_binary");
    let output_metadata = sess.opts.output_types.contains_key(&OutputType::Metadata);
    let mut tempfiles_for_stdout_output: Vec<PathBuf> = Vec::new();
    for &crate_type in &crate_info.crate_types {
        // Ignore executable crates if we have -Z no-codegen, as they will error.
        if (sess.opts.unstable_opts.no_codegen || !sess.opts.output_types.should_codegen())
            && !output_metadata
            && crate_type == CrateType::Executable
        {
            continue;
        }

        if invalid_output_for_target(sess, crate_type) {
            // tRust: invariant: structural invariant — linker configuration constrains valid options at this point
            bug!("invalid output type `{:?}` for target `{}`", crate_type, sess.opts.target_triple);
        }

        sess.time("link_binary_check_files_are_writeable", || {
            for obj in compiled_modules.modules.iter().filter_map(|m| m.object.as_ref()) {
                check_file_is_writeable(obj, sess);
            }
        });

        if outputs.outputs.should_link() {
            let output = out_filename(sess, crate_type, outputs, crate_info.local_crate_name);
            let tmpdir = TempDirBuilder::new()
                .prefix("rustc")
                .tempdir_in(output.parent().unwrap_or_else(|| Path::new(".")))
                .unwrap_or_else(|error| sess.dcx().emit_fatal(errors::CreateTempDir { error }));
            let path = MaybeTempDir::new(tmpdir, sess.opts.cg.save_temps);

            let crate_name = format!("{}", crate_info.local_crate_name);
            let out_filename = output.file_for_writing(
                outputs,
                OutputType::Exe,
                &crate_name,
                sess.invocation_temp.as_deref(),
            );
            match crate_type {
                CrateType::Rlib => {
                    let _timer = sess.timer("link_rlib");
                    info!("preparing rlib to {:?}", out_filename);
                    link_rlib(
                        sess,
                        archive_builder_builder,
                        &compiled_modules,
                        &crate_info,
                        &metadata,
                        RlibFlavor::Normal,
                        &path,
                    )
                    .build(&out_filename);
                }
                CrateType::StaticLib => {
                    link_staticlib(
                        sess,
                        archive_builder_builder,
                        &compiled_modules,
                        &crate_info,
                        &metadata,
                        &out_filename,
                        &path,
                    );
                }
                _ => {
                    link_natively(
                        sess,
                        archive_builder_builder,
                        crate_type,
                        &out_filename,
                        &compiled_modules,
                        &crate_info,
                        &metadata,
                        path.as_ref(),
                        codegen_backend,
                    );
                }
            }
            if sess.opts.json_artifact_notifications {
                sess.dcx().emit_artifact_notification(&out_filename, "link");
            }

            if sess.prof.enabled()
                && let Some(artifact_name) = out_filename.file_name()
            {
                // Record size for self-profiling
                let file_size = std::fs::metadata(&out_filename).map(|m| m.len()).unwrap_or(0);

                sess.prof.artifact_size(
                    "linked_artifact",
                    artifact_name.to_string_lossy(),
                    file_size,
                );
            }

            if sess.target.binary_format == BinaryFormat::Elf {
                if let Err(err) = warn_if_linked_with_gold(sess, &out_filename) {
                    info!(?err, "Error while checking if gold was the linker");
                }
            }

            if output.is_stdout() {
                if output.is_tty() {
                    sess.dcx().emit_err(errors::BinaryOutputToTty {
                        shorthand: OutputType::Exe.shorthand(),
                    });
                } else if let Err(e) = copy_to_stdout(&out_filename) {
                    sess.dcx().emit_err(errors::CopyPath::new(&out_filename, output.as_path(), e));
                }
                tempfiles_for_stdout_output.push(out_filename);
            }
        }
    }

    // Remove the temporary object file and metadata if we aren't saving temps.
    sess.time("link_binary_remove_temps", || {
        // If the user requests that temporaries are saved, don't delete any.
        if sess.opts.cg.save_temps {
            return;
        }

        let maybe_remove_temps_from_module =
            |preserve_objects: bool, preserve_dwarf_objects: bool, module: &CompiledModule| {
                if !preserve_objects && let Some(ref obj) = module.object {
                    ensure_removed(sess.dcx(), obj);
                }

                if !preserve_dwarf_objects && let Some(ref dwo_obj) = module.dwarf_object {
                    ensure_removed(sess.dcx(), dwo_obj);
                }
            };

        let remove_temps_from_module =
            |module: &CompiledModule| maybe_remove_temps_from_module(false, false, module);

        // Otherwise, always remove the allocator module temporaries.
        if let Some(ref allocator_module) = compiled_modules.allocator_module {
            remove_temps_from_module(allocator_module);
        }

        // Remove the temporary files if output goes to stdout
        for temp in tempfiles_for_stdout_output {
            ensure_removed(sess.dcx(), &temp);
        }

        // If no requested outputs require linking, then the object temporaries should
        // be kept.
        if !sess.opts.output_types.should_link() {
            return;
        }

        // Potentially keep objects for their debuginfo.
        let (preserve_objects, preserve_dwarf_objects) = preserve_objects_for_their_debuginfo(sess);
        debug!(?preserve_objects, ?preserve_dwarf_objects);

        for module in &compiled_modules.modules {
            maybe_remove_temps_from_module(preserve_objects, preserve_dwarf_objects, module);
        }
    });
}

// Crate type is not passed when calculating the dylibs to include for LTO. In that case all
// crate types must use the same dependency formats.
pub fn each_linked_rlib(
    info: &CrateInfo,
    crate_type: Option<CrateType>,
    f: &mut dyn FnMut(CrateNum, &Path),
) -> Result<(), errors::LinkRlibError> {
    let fmts = if let Some(crate_type) = crate_type {
        let Some(fmts) = info.dependency_formats.get(&crate_type) else {
            return Err(errors::LinkRlibError::MissingFormat);
        };

        fmts
    } else {
        let mut dep_formats = info.dependency_formats.iter();
        let (ty1, list1) = dep_formats.next().ok_or(errors::LinkRlibError::MissingFormat)?;
        if let Some((ty2, list2)) = dep_formats.find(|(_, list2)| list1 != *list2) {
            return Err(errors::LinkRlibError::IncompatibleDependencyFormats {
                ty1: format!("{ty1:?}"),
                ty2: format!("{ty2:?}"),
                list1: format!("{list1:?}"),
                list2: format!("{list2:?}"),
            });
        }
        list1
    };

    let used_dep_crates = info.used_crates.iter();
    for &cnum in used_dep_crates {
        match fmts.get(cnum) {
            Some(&Linkage::NotLinked | &Linkage::Dynamic | &Linkage::IncludedFromDylib) => continue,
            Some(_) => {}
            None => return Err(errors::LinkRlibError::MissingFormat),
        }
        let crate_name = info.crate_name[&cnum];
        let used_crate_source = &info.used_crate_source[&cnum];
        if let Some(path) = &used_crate_source.rlib {
            f(cnum, path);
        } else if used_crate_source.rmeta.is_some() {
            return Err(errors::LinkRlibError::OnlyRmetaFound { crate_name });
        } else {
            return Err(errors::LinkRlibError::NotFound { crate_name });
        }
    }
    Ok(())
}

/// Create an 'rlib'.
///
/// An rlib in its current incarnation is essentially a renamed .a file (with "dummy" object files).
/// The rlib primarily contains the object file of the crate, but it also some of the object files
/// from native libraries.
fn link_rlib<'a>(
    sess: &'a Session,
    archive_builder_builder: &dyn ArchiveBuilderBuilder,
    compiled_modules: &CompiledModules,
    crate_info: &CrateInfo,
    metadata: &EncodedMetadata,
    flavor: RlibFlavor,
    tmpdir: &MaybeTempDir,
) -> Box<dyn ArchiveBuilder + 'a> {
    let mut ab = archive_builder_builder.new_archive_builder(sess);

    let trailing_metadata = match flavor {
        RlibFlavor::Normal => {
            let (metadata, metadata_position) =
                create_wrapper_file(sess, ".rmeta".to_string(), metadata.stub_or_full());
            let metadata = emit_wrapper_file(sess, &metadata, tmpdir.as_ref(), METADATA_FILENAME);
            match metadata_position {
                MetadataPosition::First => {
                    // Most of the time metadata in rlib files is wrapped in a "dummy" object
                    // file for the target platform so the rlib can be processed entirely by
                    // normal linkers for the platform. Sometimes this is not possible however.
                    // If it is possible however, placing the metadata object first improves
                    // performance of getting metadata from rlibs.
                    ab.add_file(&metadata);
                    None
                }
                MetadataPosition::Last => Some(metadata),
            }
        }

        RlibFlavor::StaticlibBase => None,
    };

    for m in &compiled_modules.modules {
        if let Some(obj) = m.object.as_ref() {
            ab.add_file(obj);
        }

        if let Some(dwarf_obj) = m.dwarf_object.as_ref() {
            ab.add_file(dwarf_obj);
        }
    }

    match flavor {
        RlibFlavor::Normal => {}
        RlibFlavor::StaticlibBase => {
            let obj = compiled_modules.allocator_module.as_ref().and_then(|m| m.object.as_ref());
            if let Some(obj) = obj {
                ab.add_file(obj);
            }
        }
    }

    // Used if packed_bundled_libs flag enabled.
    let mut packed_bundled_libs = Vec::new();

    // Note that in this loop we are ignoring the value of `lib.cfg`. That is,
    // we may not be configured to actually include a static library if we're
    // adding it here. That's because later when we consume this rlib we'll
    // decide whether we actually needed the static library or not.
    //
    // To do this "correctly" we'd need to keep track of which libraries added
    // which object files to the archive. We don't do that here, however. The
    // #[link(cfg(..))] feature is unstable, though, and only intended to get
    // liblibc working. In that sense the check below just indicates that if
    // there are any libraries we want to omit object files for at link time we
    // just exclude all custom object files.
    //
    // Eventually if we want to stabilize or flesh out the #[link(cfg(..))]
    // feature then we'll need to figure out how to record what objects were
    // loaded from the libraries found here and then encode that into the
    // metadata of the rlib we're generating somehow.
    for lib in crate_info.used_libraries.iter() {
        let NativeLibKind::Static { bundle: None | Some(true), .. } = lib.kind else {
            continue;
        };
        if flavor == RlibFlavor::Normal
            && let Some(filename) = lib.filename
        {
            let path = find_native_static_library(filename.as_str(), true, sess);
            let src = read(path)
                .unwrap_or_else(|e| sess.dcx().emit_fatal(errors::ReadFileError { message: e }));
            let (data, _) = create_wrapper_file(sess, ".bundled_lib".to_string(), &src);
            let wrapper_file = emit_wrapper_file(sess, &data, tmpdir.as_ref(), filename.as_str());
            packed_bundled_libs.push(wrapper_file);
        } else {
            let path = find_native_static_library(lib.name.as_str(), lib.verbatim, sess);
            ab.add_archive(&path, Box::new(|_| false)).unwrap_or_else(|error| {
                sess.dcx().emit_fatal(errors::AddNativeLibrary { library_path: path, error })
            });
        }
    }

    // On Windows, we add the raw-dylib import libraries to the rlibs already.
    // But on ELF, this is not possible, as a shared object cannot be a member of a static library.
    // Instead, we add all raw-dylibs to the final link on ELF.
    if sess.target.is_like_windows {
        for output_path in raw_dylib::create_raw_dylib_dll_import_libs(
            sess,
            archive_builder_builder,
            crate_info.used_libraries.iter(),
            tmpdir.as_ref(),
            true,
        ) {
            ab.add_archive(&output_path, Box::new(|_| false)).unwrap_or_else(|error| {
                sess.dcx()
                    .emit_fatal(errors::AddNativeLibrary { library_path: output_path, error });
            });
        }
    }

    if let Some(trailing_metadata) = trailing_metadata {
        // Note that it is important that we add all of our non-object "magical
        // files" *after* all of the object files in the archive. The reason for
        // this is as follows:
        //
        // * When performing LTO, this archive will be modified to remove
        //   objects from above. The reason for this is described below.
        //
        // * When the system linker looks at an archive, it will attempt to
        //   determine the architecture of the archive in order to see whether its
        //   linkable.
        //
        //   The algorithm for this detection is: iterate over the files in the
        //   archive. Skip magical SYMDEF names. Interpret the first file as an
        //   object file. Read architecture from the object file.
        //
        // * As one can probably see, if "metadata" and "foo.bc" were placed
        //   before all of the objects, then the architecture of this archive would
        //   not be correctly inferred once 'foo.o' is removed.
        //
        // * Most of the time metadata in rlib files is wrapped in a "dummy" object
        //   file for the target platform so the rlib can be processed entirely by
        //   normal linkers for the platform. Sometimes this is not possible however.
        //
        // Basically, all this means is that this code should not move above the
        // code above.
        ab.add_file(&trailing_metadata);
    }

    // Add all bundled static native library dependencies.
    // Archives added to the end of .rlib archive, see comment above for the reason.
    for lib in packed_bundled_libs {
        ab.add_file(&lib)
    }

    ab
}

/// Create a static archive.
///
/// This is essentially the same thing as an rlib, but it also involves adding all of the upstream
/// crates' objects into the archive. This will slurp in all of the native libraries of upstream
/// dependencies as well.
///
/// Additionally, there's no way for us to link dynamic libraries, so we warn about all dynamic
/// library dependencies that they're not linked in.
///
/// There's no need to include metadata in a static archive, so ensure to not link in the metadata
/// object file (and also don't prepare the archive with a metadata file).
fn link_staticlib(
    sess: &Session,
    archive_builder_builder: &dyn ArchiveBuilderBuilder,
    compiled_modules: &CompiledModules,
    crate_info: &CrateInfo,
    metadata: &EncodedMetadata,
    out_filename: &Path,
    tempdir: &MaybeTempDir,
) {
    info!("preparing staticlib to {:?}", out_filename);
    let mut ab = link_rlib(
        sess,
        archive_builder_builder,
        compiled_modules,
        crate_info,
        metadata,
        RlibFlavor::StaticlibBase,
        tempdir,
    );
    let mut all_native_libs = vec![];

    let res = each_linked_rlib(crate_info, Some(CrateType::StaticLib), &mut |cnum, path| {
        let lto = are_upstream_rust_objects_already_included(sess)
            && !ignored_for_lto(sess, crate_info, cnum);

        let native_libs = crate_info.native_libraries[&cnum].iter();
        let relevant = native_libs.clone().filter(|lib| relevant_lib(sess, lib));
        let relevant_libs: FxIndexSet<_> = relevant.filter_map(|lib| lib.filename).collect();

        let bundled_libs: FxIndexSet<_> = native_libs.filter_map(|lib| lib.filename).collect();
        ab.add_archive(
            path,
            Box::new(move |fname: &str| {
                // Ignore metadata files, no matter the name.
                if fname == METADATA_FILENAME {
                    return true;
                }

                // Don't include Rust objects if LTO is enabled
                if lto && looks_like_rust_object_file(fname) {
                    return true;
                }

                // Skip objects for bundled libs.
                if bundled_libs.contains(&Symbol::intern(fname)) {
                    return true;
                }

                false
            }),
        )
        .expect("invariant: archive builder creation must succeed");

        archive_builder_builder
            .extract_bundled_libs(path, tempdir.as_ref(), &relevant_libs)
            .unwrap_or_else(|e| sess.dcx().emit_fatal(e));

        for filename in relevant_libs.iter() {
            let joined = tempdir.as_ref().join(filename.as_str());
            let path = joined.as_path();
            ab.add_archive(path, Box::new(|_| false)).expect("invariant: adding archive must succeed");
        }

        all_native_libs.extend(crate_info.native_libraries[&cnum].iter().cloned());
    });
    if let Err(e) = res {
        sess.dcx().emit_fatal(e);
    }

    ab.build(out_filename);

    let crates = crate_info.used_crates.iter();

    let fmts = crate_info
        .dependency_formats
        .get(&CrateType::StaticLib)
        .expect("no dependency formats for staticlib");

    let mut all_rust_dylibs = vec![];
    for &cnum in crates {
        let Some(Linkage::Dynamic) = fmts.get(cnum) else {
            continue;
        };
        let crate_name = crate_info.crate_name[&cnum];
        let used_crate_source = &crate_info.used_crate_source[&cnum];
        if let Some(path) = &used_crate_source.dylib {
            all_rust_dylibs.push(&**path);
        } else if used_crate_source.rmeta.is_some() {
            sess.dcx().emit_fatal(errors::LinkRlibError::OnlyRmetaFound { crate_name });
        } else {
            sess.dcx().emit_fatal(errors::LinkRlibError::NotFound { crate_name });
        }
    }

    all_native_libs.extend_from_slice(&crate_info.used_libraries);

    for print in &sess.opts.prints {
        if print.kind == PrintKind::NativeStaticLibs {
            print_native_static_libs(sess, &print.out, &all_native_libs, &all_rust_dylibs);
        }
    }
}

/// Use `thorin` (rust implementation of a dwarf packaging utility) to link DWARF objects into a
/// DWARF package.
fn link_dwarf_object(
    sess: &Session,
    compiled_modules: &CompiledModules,
    crate_info: &CrateInfo,
    executable_out_filename: &Path,
) {
    let mut dwp_out_filename = executable_out_filename.to_path_buf().into_os_string();
    dwp_out_filename.push(".dwp");
    debug!(?dwp_out_filename, ?executable_out_filename);

    #[derive(Default)]
    struct ThorinSession<Relocations> {
        arena_data: TypedArena<Vec<u8>>,
        arena_mmap: TypedArena<Mmap>,
        arena_relocations: TypedArena<Relocations>,
    }

    impl<Relocations> ThorinSession<Relocations> {
        fn alloc_mmap(&self, data: Mmap) -> &Mmap {
            &*self.arena_mmap.alloc(data)
        }
    }

    impl<Relocations> thorin::Session<Relocations> for ThorinSession<Relocations> {
        fn alloc_data(&self, data: Vec<u8>) -> &[u8] {
            &*self.arena_data.alloc(data)
        }

        fn alloc_relocation(&self, data: Relocations) -> &Relocations {
            &*self.arena_relocations.alloc(data)
        }

        fn read_input(&self, path: &Path) -> std::io::Result<&[u8]> {
            let file = File::open(&path)?;
            // SAFETY: `file` is a valid, open `File` from `File::open` above. // tRust:
            // The resulting `Mmap` is stored in `self.arena_mmap` via `alloc_mmap`,
            // which keeps it alive for the lifetime of the `ThorinSession` arena.
            let mmap = (unsafe { Mmap::map(file) })?;
            Ok(self.alloc_mmap(mmap))
        }
    }

    match sess.time("run_thorin", || -> Result<(), thorin::Error> {
        let thorin_sess = ThorinSession::default();
        let mut package = thorin::DwarfPackage::new(&thorin_sess);

        // Input objs contain .o/.dwo files from the current crate.
        match sess.opts.unstable_opts.split_dwarf_kind {
            SplitDwarfKind::Single => {
                for input_obj in compiled_modules.modules.iter().filter_map(|m| m.object.as_ref()) {
                    package.add_input_object(input_obj)?;
                }
            }
            SplitDwarfKind::Split => {
                for input_obj in
                    compiled_modules.modules.iter().filter_map(|m| m.dwarf_object.as_ref())
                {
                    package.add_input_object(input_obj)?;
                }
            }
        }

        // Input rlibs contain .o/.dwo files from dependencies.
        let input_rlibs = crate_info
            .used_crate_source
            .items()
            .filter_map(|(_, csource)| csource.rlib.as_ref())
            .into_sorted_stable_ord();

        for input_rlib in input_rlibs {
            debug!(?input_rlib);
            package.add_input_object(input_rlib)?;
        }

        // Failing to read the referenced objects is expected for dependencies where the path in the
        // executable will have been cleaned by Cargo, but the referenced objects will be contained
        // within rlibs provided as inputs.
        //
        // If paths have been remapped, then .o/.dwo files from the current crate also won't be
        // found, but are provided explicitly above.
        //
        // Adding an executable is primarily done to make `thorin` check that all the referenced
        // dwarf objects are found in the end.
        package.add_executable(
            executable_out_filename,
            thorin::MissingReferencedObjectBehaviour::Skip,
        )?;

        let output_stream = BufWriter::new(
            OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .truncate(true)
                .open(dwp_out_filename)?,
        );
        let mut output_stream = thorin::object::write::StreamingBuffer::new(output_stream);
        package.finish()?.emit(&mut output_stream)?;
        output_stream.result()?;
        output_stream.into_inner().flush()?;

        Ok(())
    }) {
        Ok(()) => {}
        Err(e) => sess.dcx().emit_fatal(errors::ThorinErrorWrapper(e)),
    }
}

#[derive(Diagnostic)]
#[diag("{$inner}")]
/// Translating this is kind of useless. We don't pass translation flags to the linker, so we'd just
/// end up with inconsistent languages within the same diagnostic.
struct LinkerOutput {
    inner: String,
}

fn is_msvc_link_exe(sess: &Session) -> bool {
    let (linker_path, flavor) = linker_and_flavor(sess);
    sess.target.is_like_msvc
        && flavor == LinkerFlavor::Msvc(Lld::No)
        // Match exactly "link.exe"
        && linker_path.to_str() == Some("link.exe")
}

fn is_macos_ld(sess: &Session) -> bool {
    let (_, flavor) = linker_and_flavor(sess);
    sess.target.is_like_darwin && matches!(flavor, LinkerFlavor::Darwin(_, Lld::No))
}

fn is_windows_gnu_ld(sess: &Session) -> bool {
    let (_, flavor) = linker_and_flavor(sess);
    sess.target.is_like_windows
        && !sess.target.is_like_msvc
        && matches!(flavor, LinkerFlavor::Gnu(_, Lld::No))
}

fn report_linker_output(sess: &Session, levels: CodegenLintLevels, stdout: &[u8], stderr: &[u8]) {
    let mut escaped_stderr = escape_string(&stderr);
    let mut escaped_stdout = escape_string(&stdout);
    let mut linker_info = String::new();

    info!("linker stderr:\n{}", &escaped_stderr);
    info!("linker stdout:\n{}", &escaped_stdout);

    fn for_each(bytes: &[u8], mut f: impl FnMut(&str, &mut String)) -> String {
        let mut output = String::new();
        if let Ok(str) = str::from_utf8(bytes) {
            info!("line: {str}");
            output = String::with_capacity(str.len());
            for line in str.lines() {
                f(line.trim(), &mut output);
            }
        }
        escape_string(output.trim().as_bytes())
    }

    if is_msvc_link_exe(sess) {
        info!("inferred MSVC link.exe");

        escaped_stdout = for_each(&stdout, |line, output| {
            // Hide some progress messages from link.exe that we don't care about.
            // See https://github.com/chromium/chromium/blob/bfa41e41145ffc85f041384280caf2949bb7bd72/build/toolchain/win/tool_wrapper.py#L144-L146
            if line.starts_with("   Creating library")
                || line.starts_with("Generating code")
                || line.starts_with("Finished generating code")
            {
                linker_info += line;
                linker_info += "\r\n";
            } else {
                *output += line;
                *output += "\r\n"
            }
        });
    } else if is_macos_ld(sess) {
        info!("inferred macOS LD");

        // NOTE(#136113): Tracked upstream for future resolution.
        let deployment_mismatch = |line: &str| {
            line.starts_with("ld: warning: object file (")
                && line.contains("was built for newer 'macOS' version")
                && line.contains("than being linked")
        };
        // NOTE: This warning is suppressed because it fires on too many crates currently.
        // to want to turn it on immediately.
        let search_path = |line: &str| {
            line.starts_with("ld: warning: search path '") && line.ends_with("' not found")
        };
        escaped_stderr = for_each(&stderr, |line, output| {
            // This duplicate library warning is just not helpful at all.
            if line.starts_with("ld: warning: ignoring duplicate libraries: ")
                || deployment_mismatch(line)
                || search_path(line)
            {
                linker_info += line;
                linker_info += "\n";
            } else {
                *output += line;
                *output += "\n"
            }
        });
    } else if is_windows_gnu_ld(sess) {
        info!("inferred Windows GNU LD");

        let mut saw_exclude_symbol = false;
        // See https://github.com/rust-lang/rust/issues/112368.
        // NOTE: Could check binutils version (<2.40) before downgrading; not yet implemented.
        let exclude_symbols = |line: &str| {
            line.starts_with("Warning: .drectve `-exclude-symbols:")
                && line.ends_with("' unrecognized")
        };
        escaped_stderr = for_each(&stderr, |line, output| {
            if exclude_symbols(line) {
                saw_exclude_symbol = true;
                linker_info += line;
                linker_info += "\n";
            } else if saw_exclude_symbol && line == "Warning: corrupt .drectve at end of def file" {
                linker_info += line;
                linker_info += "\n";
            } else {
                *output += line;
                *output += "\n"
            }
        });
    }

    let lint_msg = |msg| {
        emit_lint_base(
            sess,
            LINKER_MESSAGES,
            levels.linker_messages,
            None,
            LinkerOutput { inner: msg },
        );
    };
    let lint_info = |msg| {
        emit_lint_base(sess, LINKER_INFO, levels.linker_info, None, LinkerOutput { inner: msg });
    };

    if !escaped_stderr.is_empty() {
        // We already print `warning:` at the start of the diagnostic. Remove it from the linker output if present.
        escaped_stderr =
            escaped_stderr.strip_prefix("warning: ").unwrap_or(&escaped_stderr).to_owned();
        // Windows GNU LD prints uppercase Warning
        escaped_stderr = escaped_stderr
            .strip_prefix("Warning: ")
            .unwrap_or(&escaped_stderr)
            .replace(": warning: ", ": ");
        lint_msg(format!("linker stderr: {escaped_stderr}"));
    }
    if !escaped_stdout.is_empty() {
        lint_msg(format!("linker stdout: {}", escaped_stdout))
    }
    if !linker_info.is_empty() {
        lint_info(linker_info);
    }
}

/// Create a dynamic library or executable.
///
/// This will invoke the system linker/cc to create the resulting file. This links to all upstream
/// files as well.
fn link_natively(
    sess: &Session,
    archive_builder_builder: &dyn ArchiveBuilderBuilder,
    crate_type: CrateType,
    out_filename: &Path,
    compiled_modules: &CompiledModules,
    crate_info: &CrateInfo,
    metadata: &EncodedMetadata,
    tmpdir: &Path,
    codegen_backend: &'static str,
) {
    info!("preparing {:?} to {:?}", crate_type, out_filename);
    let (linker_path, flavor) = linker_and_flavor(sess);
    let self_contained_components = self_contained_components(sess, crate_type, &linker_path);

    // On AIX, we ship all libraries as .a big_af archive
    // the expected format is lib<name>.a(libname.so) for the actual
    // dynamic library. So we link to a temporary .so file to be archived
    // at the final out_filename location
    let should_archive = crate_type != CrateType::Executable && sess.target.is_like_aix;
    let archive_member =
        should_archive.then(|| tmpdir.join(out_filename.file_name().expect("invariant: output path must have filename")).with_extension("so"));
    let temp_filename = archive_member.as_deref().unwrap_or(out_filename);

    let mut cmd = linker_with_args(
        &linker_path,
        flavor,
        sess,
        archive_builder_builder,
        crate_type,
        tmpdir,
        temp_filename,
        compiled_modules,
        crate_info,
        metadata,
        self_contained_components,
        codegen_backend,
    );

    linker::disable_localization(&mut cmd);

    for (k, v) in sess.target.link_env.as_ref() {
        cmd.env(k.as_ref(), v.as_ref());
    }
    for k in sess.target.link_env_remove.as_ref() {
        cmd.env_remove(k.as_ref());
    }

    for print in &sess.opts.prints {
        if print.kind == PrintKind::LinkArgs {
            let content = format!("{cmd:?}\n");
            print.out.overwrite(&content, sess);
        }
    }

    // May have not found libraries in the right formats.
    sess.dcx().abort_if_errors();

    // Invoke the system linker
    info!("{cmd:?}");
    let unknown_arg_regex =
        Regex::new(r"(unknown|unrecognized) (command line )?(option|argument)").expect("invariant: linker error regex is valid");
    let mut prog;
    loop {
        prog = sess.time("run_linker", || exec_linker(sess, &cmd, out_filename, flavor, tmpdir));
        let Ok(ref output) = prog else {
            break;
        };
        if output.status.success() {
            break;
        }
        let mut out = output.stderr.clone();
        out.extend(&output.stdout);
        let out = String::from_utf8_lossy(&out);

        // Check to see if the link failed with an error message that indicates it
        // doesn't recognize the -no-pie option. If so, re-perform the link step
        // without it. This is safe because if the linker doesn't support -no-pie
        // then it should not default to linking executables as pie. Different
        // versions of gcc seem to use different quotes in the error message so
        // don't check for them.
        if matches!(flavor, LinkerFlavor::Gnu(Cc::Yes, _))
            && unknown_arg_regex.is_match(&out)
            && out.contains("-no-pie")
            && cmd.get_args().iter().any(|e| e == "-no-pie")
        {
            info!("linker output: {:?}", out);
            warn!("Linker does not support -no-pie command line option. Retrying without.");
            for arg in cmd.take_args() {
                if arg != "-no-pie" {
                    cmd.arg(arg);
                }
            }
            info!("{cmd:?}");
            continue;
        }

        // Check if linking failed with an error message that indicates the driver didn't recognize
        // the `-fuse-ld=lld` option. If so, re-perform the link step without it. This avoids having
        // to spawn multiple instances on the happy path to do version checking, and ensures things
        // keep working on the tier 1 baseline of GLIBC 2.17+. That is generally understood as GCCs
        // circa RHEL/CentOS 7, 4.5 or so, whereas lld support was added in GCC 9.
        if matches!(flavor, LinkerFlavor::Gnu(Cc::Yes, Lld::Yes))
            && unknown_arg_regex.is_match(&out)
            && out.contains("-fuse-ld=lld")
            && cmd.get_args().iter().any(|e| e.to_string_lossy() == "-fuse-ld=lld")
        {
            info!("linker output: {:?}", out);
            info!("The linker driver does not support `-fuse-ld=lld`. Retrying without it.");
            for arg in cmd.take_args() {
                if arg.to_string_lossy() != "-fuse-ld=lld" {
                    cmd.arg(arg);
                }
            }
            info!("{cmd:?}");
            continue;
        }

        // Detect '-static-pie' used with an older version of gcc or clang not supporting it.
        // Fallback from '-static-pie' to '-static' in that case.
        if matches!(flavor, LinkerFlavor::Gnu(Cc::Yes, _))
            && unknown_arg_regex.is_match(&out)
            && (out.contains("-static-pie") || out.contains("--no-dynamic-linker"))
            && cmd.get_args().iter().any(|e| e == "-static-pie")
        {
            info!("linker output: {:?}", out);
            warn!(
                "Linker does not support -static-pie command line option. Retrying with -static instead."
            );
            // Mirror `add_(pre,post)_link_objects` to replace CRT objects.
            let self_contained_crt_objects = self_contained_components.is_crt_objects_enabled();
            let opts = &sess.target;
            let pre_objects = if self_contained_crt_objects {
                &opts.pre_link_objects_self_contained
            } else {
                &opts.pre_link_objects
            };
            let post_objects = if self_contained_crt_objects {
                &opts.post_link_objects_self_contained
            } else {
                &opts.post_link_objects
            };
            let get_objects = |objects: &CrtObjects, kind| {
                objects
                    .get(&kind)
                    .iter()
                    .copied()
                    .flatten()
                    .map(|obj| {
                        get_object_file_path(sess, obj, self_contained_crt_objects).into_os_string()
                    })
                    .collect::<Vec<_>>()
            };
            let pre_objects_static_pie = get_objects(pre_objects, LinkOutputKind::StaticPicExe);
            let post_objects_static_pie = get_objects(post_objects, LinkOutputKind::StaticPicExe);
            let mut pre_objects_static = get_objects(pre_objects, LinkOutputKind::StaticNoPicExe);
            let mut post_objects_static = get_objects(post_objects, LinkOutputKind::StaticNoPicExe);
            // Assume that we know insertion positions for the replacement arguments from replaced
            // arguments, which is true for all supported targets.
            assert!(pre_objects_static.is_empty() || !pre_objects_static_pie.is_empty());
            assert!(post_objects_static.is_empty() || !post_objects_static_pie.is_empty());
            for arg in cmd.take_args() {
                if arg == "-static-pie" {
                    // Replace the output kind.
                    cmd.arg("-static");
                } else if pre_objects_static_pie.contains(&arg) {
                    // Replace the pre-link objects (replace the first and remove the rest).
                    cmd.args(mem::take(&mut pre_objects_static));
                } else if post_objects_static_pie.contains(&arg) {
                    // Replace the post-link objects (replace the first and remove the rest).
                    cmd.args(mem::take(&mut post_objects_static));
                } else {
                    cmd.arg(arg);
                }
            }
            info!("{cmd:?}");
            continue;
        }

        break;
    }

    match prog {
        Ok(prog) => {
            if !prog.status.success() {
                let mut output = prog.stderr.clone();
                output.extend_from_slice(&prog.stdout);
                let escaped_output = escape_linker_output(&output, flavor);
                let err = errors::LinkingFailed {
                    linker_path: &linker_path,
                    exit_status: prog.status,
                    command: cmd,
                    escaped_output,
                    verbose: sess.opts.verbose,
                    sysroot_dir: sess.opts.sysroot.path().to_owned(),
                };
                sess.dcx().emit_err(err);
                // If MSVC's `link.exe` was expected but the return code
                // is not a Microsoft LNK error then suggest a way to fix or
                // install the Visual Studio build tools.
                if let Some(code) = prog.status.code() {
                    // All Microsoft `link.exe` linking ror codes are
                    // four digit numbers in the range 1000 to 9999 inclusive
                    if is_msvc_link_exe(sess) && (code < 1000 || code > 9999) {
                        let is_vs_installed = find_msvc_tools::find_vs_version().is_ok();
                        let has_linker =
                            find_msvc_tools::find_tool(sess.target.arch.desc(), "link.exe")
                                .is_some();

                        sess.dcx().emit_note(errors::LinkExeUnexpectedError);

                        // STATUS_STACK_BUFFER_OVERRUN is also used for fast abnormal program termination, e.g. abort().
                        // Emit a special diagnostic to let people know that this most likely doesn't indicate a stack buffer overrun.
                        const STATUS_STACK_BUFFER_OVERRUN: i32 = 0xc0000409u32 as _;
                        if code == STATUS_STACK_BUFFER_OVERRUN {
                            sess.dcx().emit_note(errors::LinkExeStatusStackBufferOverrun);
                        }

                        if is_vs_installed && has_linker {
                            // the linker is broken
                            sess.dcx().emit_note(errors::RepairVSBuildTools);
                            sess.dcx().emit_note(errors::MissingCppBuildToolComponent);
                        } else if is_vs_installed {
                            // the linker is not installed
                            sess.dcx().emit_note(errors::SelectCppBuildToolWorkload);
                        } else {
                            // visual studio is not installed
                            sess.dcx().emit_note(errors::VisualStudioNotInstalled);
                        }
                    }
                }

                sess.dcx().abort_if_errors();
            }

            info!("reporting linker output: flavor={flavor:?}");
            report_linker_output(sess, crate_info.lint_levels, &prog.stdout, &prog.stderr);
        }
        Err(e) => {
            let linker_not_found = e.kind() == io::ErrorKind::NotFound;

            let err = if linker_not_found {
                sess.dcx().emit_err(errors::LinkerNotFound { linker_path, error: e })
            } else {
                sess.dcx().emit_err(errors::UnableToExeLinker {
                    linker_path,
                    error: e,
                    command_formatted: format!("{cmd:?}"),
                })
            };

            if sess.target.is_like_msvc && linker_not_found {
                sess.dcx().emit_note(errors::MsvcMissingLinker);
                sess.dcx().emit_note(errors::CheckInstalledVisualStudio);
                sess.dcx().emit_note(errors::InsufficientVSCodeProduct);
            }
            err.raise_fatal();
        }
    }

    match sess.split_debuginfo() {
        // If split debug information is disabled or located in individual files
        // there's nothing to do here.
        SplitDebuginfo::Off | SplitDebuginfo::Unpacked => {}

        // If packed split-debuginfo is requested, but the final compilation
        // doesn't actually have any debug information, then we skip this step.
        SplitDebuginfo::Packed if sess.opts.debuginfo == DebugInfo::None => {}

        // On macOS the external `dsymutil` tool is used to create the packed
        // debug information. Note that this will read debug information from
        // the objects on the filesystem which we'll clean up later.
        SplitDebuginfo::Packed if sess.target.is_like_darwin => {
            let prog = Command::new("dsymutil").arg(out_filename).output();
            match prog {
                Ok(prog) => {
                    if !prog.status.success() {
                        let mut output = prog.stderr.clone();
                        output.extend_from_slice(&prog.stdout);
                        sess.dcx().emit_warn(errors::ProcessingDymutilFailed {
                            status: prog.status,
                            output: escape_string(&output),
                        });
                    }
                }
                Err(error) => sess.dcx().emit_fatal(errors::UnableToRunDsymutil { error }),
            }
        }

        // On MSVC packed debug information is produced by the linker itself so
        // there's no need to do anything else here.
        SplitDebuginfo::Packed if sess.target.is_like_windows => {}

        // ... and otherwise we're processing a `*.dwp` packed dwarf file.
        //
        // We cannot rely on the .o paths in the executable because they may have been
        // remapped by --remap-path-prefix and therefore invalid, so we need to provide
        // the .o/.dwo paths explicitly.
        SplitDebuginfo::Packed => {
            link_dwarf_object(sess, compiled_modules, crate_info, out_filename)
        }
    }

    let strip = sess.opts.cg.strip;

    if sess.target.is_like_darwin {
        let stripcmd = "rust-objcopy";
        match (strip, crate_type) {
            (Strip::Debuginfo, _) => {
                strip_with_external_utility(sess, stripcmd, out_filename, &["--strip-debug"])
            }

            // Per the manpage, --discard-all is the maximum safe strip level for dynamic libraries. (#93988)
            (
                Strip::Symbols,
                CrateType::Dylib | CrateType::Cdylib | CrateType::ProcMacro | CrateType::Sdylib,
            ) => strip_with_external_utility(sess, stripcmd, out_filename, &["--discard-all"]),
            (Strip::Symbols, _) => {
                strip_with_external_utility(sess, stripcmd, out_filename, &["--strip-all"])
            }
            (Strip::None, _) => {}
        }
    }

    if sess.target.is_like_solaris {
        // Many illumos systems will have both the native 'strip' utility and
        // the GNU one. Use the native version explicitly and do not rely on
        // what's in the path.
        //
        // If cross-compiling and there is not a native version, then use
        // `llvm-strip` and hope.
        let stripcmd = if !sess.host.is_like_solaris { "rust-objcopy" } else { "/usr/bin/strip" };
        match strip {
            // Always preserve the symbol table (-x).
            Strip::Debuginfo => strip_with_external_utility(sess, stripcmd, out_filename, &["-x"]),
            // Strip::Symbols is handled via the --strip-all linker option.
            Strip::Symbols => {}
            Strip::None => {}
        }
    }

    if sess.target.is_like_aix {
        // `llvm-strip` doesn't work for AIX - their strip must be used.
        if !sess.host.is_like_aix {
            sess.dcx().emit_warn(errors::AixStripNotUsed);
        }
        let stripcmd = "/usr/bin/strip";
        match strip {
            Strip::Debuginfo => {
                // NOTE: AIX strip only supports stripping line number info, not full symbol stripping.
                strip_with_external_utility(sess, stripcmd, temp_filename, &["-X32_64", "-l"])
            }
            Strip::Symbols => {
                // Must be noted this option might remove symbol __aix_rust_metadata and thus removes .info section which contains metadata.
                strip_with_external_utility(sess, stripcmd, temp_filename, &["-X32_64", "-r"])
            }
            Strip::None => {}
        }
    }

    if should_archive {
        let mut ab = archive_builder_builder.new_archive_builder(sess);
        ab.add_file(temp_filename);
        ab.build(out_filename);
    }
}

fn strip_with_external_utility(sess: &Session, util: &str, out_filename: &Path, options: &[&str]) {
    let mut cmd = Command::new(util);
    cmd.args(options);

    let mut new_path = sess.get_tools_search_paths(false);
    if let Some(path) = env::var_os("PATH") {
        new_path.extend(env::split_paths(&path));
    }
    cmd.env("PATH", env::join_paths(new_path).expect("invariant: PATH join must produce valid path"));

    let prog = cmd.arg(out_filename).output();
    match prog {
        Ok(prog) => {
            if !prog.status.success() {
                let mut output = prog.stderr.clone();
                output.extend_from_slice(&prog.stdout);
                sess.dcx().emit_warn(errors::StrippingDebugInfoFailed {
                    util,
                    status: prog.status,
                    output: escape_string(&output),
                });
            }
        }
        Err(error) => sess.dcx().emit_fatal(errors::UnableToRun { util, error }),
    }
}

fn escape_string(s: &[u8]) -> String {
    match str::from_utf8(s) {
        Ok(s) => s.to_owned(),
        Err(_) => format!("Non-UTF-8 output: {}", s.escape_ascii()),
    }
}

#[cfg(not(windows))]
fn escape_linker_output(s: &[u8], _flavour: LinkerFlavor) -> String {
    escape_string(s)
}

/// If the output of the msvc linker is not UTF-8 and the host is Windows,
/// then try to convert the string from the OEM encoding.
#[cfg(windows)]
fn escape_linker_output(s: &[u8], flavour: LinkerFlavor) -> String {
    // This only applies to the actual MSVC linker.
    if flavour != LinkerFlavor::Msvc(Lld::No) {
        return escape_string(s);
    }
    match str::from_utf8(s) {
        Ok(s) => return s.to_owned(),
        Err(_) => match win::locale_byte_str_to_string(s, win::oem_code_page()) {
            Some(s) => s,
            // The string is not UTF-8 and isn't valid for the OEM code page
            None => format!("Non-UTF-8 output: {}", s.escape_ascii()),
        },
    }
}

/// Wrappers around the Windows API.
#[cfg(windows)]
mod win {
    use windows::Win32::Globalization::{
        CP_OEMCP, GetLocaleInfoEx, LOCALE_IUSEUTF8LEGACYOEMCP, LOCALE_NAME_SYSTEM_DEFAULT,
        LOCALE_RETURN_NUMBER, MB_ERR_INVALID_CHARS, MultiByteToWideChar,
    };

    /// Get the Windows system OEM code page. This is most notably the code page
    /// used for link.exe's output.
    pub(super) fn oem_code_page() -> u32 {
        // SAFETY: `GetLocaleInfoEx` is called with `LOCALE_NAME_SYSTEM_DEFAULT` (a // tRust:
        // null pointer constant) and `LOCALE_RETURN_NUMBER`, which writes a u32 into
        // the provided buffer. `std::slice::from_raw_parts_mut` is sound because:
        // (1) `cp` is a local, properly aligned `u32` with exclusive access,
        // (2) the reinterpret cast to `*mut u16` with `len = size_of::<u32>() /
        //     size_of::<u16>()` covers exactly the same memory region,
        // (3) the slice does not outlive the stack frame.
        // SAFETY: `cp` is an aligned local `u32`, and viewing that storage as
        // `len` `u16`s gives `GetLocaleInfoEx` exactly the writable buffer it expects.
        unsafe {
            let mut cp: u32 = 0;
            // We're using the `LOCALE_RETURN_NUMBER` flag to return a u32.
            // But the API requires us to pass the data as though it's a [u16] string.
            let len = size_of::<u32>() / size_of::<u16>();
            let data = std::slice::from_raw_parts_mut(&mut cp as *mut u32 as *mut u16, len);
            let len_written = GetLocaleInfoEx(
                LOCALE_NAME_SYSTEM_DEFAULT,
                LOCALE_IUSEUTF8LEGACYOEMCP | LOCALE_RETURN_NUMBER,
                Some(data),
            );
            if len_written as usize == len { cp } else { CP_OEMCP }
        }
    }
    /// Try to convert a multi-byte string to a UTF-8 string using the given code page
    /// The string does not need to be null terminated.
    ///
    /// This is implemented as a wrapper around `MultiByteToWideChar`.
    /// See <https://learn.microsoft.com/en-us/windows/win32/api/stringapiset/nf-stringapiset-multibytetowidechar>
    ///
    /// It will fail if the multi-byte string is longer than `i32::MAX` or if it contains
    /// any invalid bytes for the expected encoding.
    pub(super) fn locale_byte_str_to_string(s: &[u8], code_page: u32) -> Option<String> {
        // `MultiByteToWideChar` requires a length to be a "positive integer".
        if s.len() > isize::MAX as usize {
            return None;
        }
        // Error if the string is not valid for the expected code page.
        let flags = MB_ERR_INVALID_CHARS;
        // Call MultiByteToWideChar twice.
        // First to calculate the length then to convert the string.
        // SAFETY: `MultiByteToWideChar` is a Windows API call. Passing `None` as // tRust:
        // the output buffer queries the required buffer length without writing.
        // `s` is a valid `&[u8]` slice, and `code_page` / `flags` are valid constants.
        // The length check at the top of this function ensures `s.len() <= isize::MAX`.
        // SAFETY: Passing `None` only queries the required UTF-16 length; `s`
        // is a valid input buffer and the earlier length check rules out overflow.
        let mut len = unsafe { MultiByteToWideChar(code_page, flags, s, None) };
        if len > 0 {
            let mut utf16 = vec![0; len as usize];
            // SAFETY: `utf16` is a freshly allocated buffer of exactly `len` elements // tRust:
            // as returned by the first call. `MultiByteToWideChar` writes at most
            // `len` wide characters into `Some(&mut utf16)`, which is within bounds.
            len = unsafe { MultiByteToWideChar(code_page, flags, s, Some(&mut utf16)) };
            if len > 0 {
                return utf16.get(..len as usize).map(String::from_utf16_lossy);
            }
        }
        None
    }
}

fn add_sanitizer_libraries(
    sess: &Session,
    flavor: LinkerFlavor,
    crate_type: CrateType,
    linker: &mut dyn Linker,
) {
    if sess.target.is_like_android {
        // Sanitizer runtime libraries are provided dynamically on Android
        // targets.
        return;
    }

    if sess.opts.unstable_opts.external_clangrt {
        // Linking against in-tree sanitizer runtimes is disabled via
        // `-Z external-clangrt`
        return;
    }

    if matches!(crate_type, CrateType::Rlib | CrateType::StaticLib) {
        return;
    }

    // On macOS and Windows using MSVC the runtimes are distributed as dylibs
    // which should be linked to both executables and dynamic libraries.
    // Everywhere else the runtimes are currently distributed as static
    // libraries which should be linked to executables only.
    if matches!(
        crate_type,
        CrateType::Dylib | CrateType::Cdylib | CrateType::ProcMacro | CrateType::Sdylib
    ) && !(sess.target.is_like_darwin || sess.target.is_like_msvc)
    {
        return;
    }

    let sanitizer = sess.sanitizers();
    if sanitizer.contains(SanitizerSet::ADDRESS) {
        link_sanitizer_runtime(sess, flavor, linker, "asan");
    }
    if sanitizer.contains(SanitizerSet::DATAFLOW) {
        link_sanitizer_runtime(sess, flavor, linker, "dfsan");
    }
    if sanitizer.contains(SanitizerSet::LEAK)
        && !sanitizer.contains(SanitizerSet::ADDRESS)
        && !sanitizer.contains(SanitizerSet::HWADDRESS)
    {
        link_sanitizer_runtime(sess, flavor, linker, "lsan");
    }
    if sanitizer.contains(SanitizerSet::MEMORY) {
        link_sanitizer_runtime(sess, flavor, linker, "msan");
    }
    if sanitizer.contains(SanitizerSet::THREAD) {
        link_sanitizer_runtime(sess, flavor, linker, "tsan");
    }
    if sanitizer.contains(SanitizerSet::HWADDRESS) {
        link_sanitizer_runtime(sess, flavor, linker, "hwasan");
    }
    if sanitizer.contains(SanitizerSet::SAFESTACK) {
        link_sanitizer_runtime(sess, flavor, linker, "safestack");
    }
    if sanitizer.contains(SanitizerSet::REALTIME) {
        link_sanitizer_runtime(sess, flavor, linker, "rtsan");
    }
}

fn link_sanitizer_runtime(
    sess: &Session,
    flavor: LinkerFlavor,
    linker: &mut dyn Linker,
    name: &str,
) {
    fn find_sanitizer_runtime(sess: &Session, filename: &str) -> PathBuf {
        let path = sess.target_tlib_path.dir.join(filename);
        if path.exists() {
            sess.target_tlib_path.dir.clone()
        } else {
            filesearch::make_target_lib_path(
                &sess.opts.sysroot.default,
                sess.opts.target_triple.tuple(),
            )
        }
    }

    let channel =
        option_env!("CFG_RELEASE_CHANNEL").map(|channel| format!("-{channel}")).unwrap_or_default();

    if sess.target.is_like_darwin {
        // On Apple platforms, the sanitizer is always built as a dylib, and
        // LLVM will link to `@rpath/*.dylib`, so we need to specify an
        // rpath to the library as well (the rpath should be absolute, see
        // PR #41352 for details).
        let filename = format!("rustc{channel}_rt.{name}");
        let path = find_sanitizer_runtime(sess, &filename);
        let rpath = path.to_str().expect("non-utf8 component in path");
        linker.link_args(&["-rpath", rpath]);
        linker.link_dylib_by_name(&filename, false, true);
    } else if sess.target.is_like_msvc && flavor == LinkerFlavor::Msvc(Lld::No) && name == "asan" {
        // MSVC provides the `/INFERASANLIBS` argument to automatically find the
        // compatible ASAN library.
        linker.link_arg("/INFERASANLIBS");
    } else {
        let filename = format!("librustc{channel}_rt.{name}.a");
        let path = find_sanitizer_runtime(sess, &filename).join(&filename);
        linker.link_staticlib_by_path(&path, true);
    }
}

/// Returns a boolean indicating whether the specified crate should be ignored
/// during LTO.
///
/// Crates ignored during LTO are not lumped together in the "massive object
/// file" that we create and are linked in their normal rlib states. See
/// comments below for what crates do not participate in LTO.
///
/// It's unusual for a crate to not participate in LTO. Typically only
/// compiler-specific and unstable crates have a reason to not participate in
/// LTO.
pub fn ignored_for_lto(sess: &Session, info: &CrateInfo, cnum: CrateNum) -> bool {
    // If our target enables builtin function lowering in LLVM then the
    // crates providing these functions don't participate in LTO (e.g.
    // no_builtins or compiler builtins crates).
    !sess.target.no_builtins
        && (info.compiler_builtins == Some(cnum) || info.is_no_builtins.contains(&cnum))
}

/// This functions tries to determine the appropriate linker (and corresponding LinkerFlavor) to use
pub fn linker_and_flavor(sess: &Session) -> (PathBuf, LinkerFlavor) {
    fn infer_from(
        sess: &Session,
        linker: Option<PathBuf>,
        flavor: Option<LinkerFlavor>,
        features: LinkerFeaturesCli,
    ) -> Option<(PathBuf, LinkerFlavor)> {
        let flavor = flavor.map(|flavor| adjust_flavor_to_features(flavor, features));
        match (linker, flavor) {
            (Some(linker), Some(flavor)) => Some((linker, flavor)),
            // only the linker flavor is known; use the default linker for the selected flavor
            (None, Some(flavor)) => Some((
                PathBuf::from(match flavor {
                    LinkerFlavor::Gnu(Cc::Yes, _)
                    | LinkerFlavor::Darwin(Cc::Yes, _)
                    | LinkerFlavor::WasmLld(Cc::Yes)
                    | LinkerFlavor::Unix(Cc::Yes) => {
                        if cfg!(any(target_os = "solaris", target_os = "illumos")) {
                            // On historical Solaris systems, "cc" may have
                            // been Sun Studio, which is not flag-compatible
                            // with "gcc". This history casts a long shadow,
                            // and many modern illumos distributions today
                            // ship GCC as "gcc" without also making it
                            // available as "cc".
                            "gcc"
                        } else {
                            "cc"
                        }
                    }
                    LinkerFlavor::Gnu(_, Lld::Yes)
                    | LinkerFlavor::Darwin(_, Lld::Yes)
                    | LinkerFlavor::WasmLld(..)
                    | LinkerFlavor::Msvc(Lld::Yes) => "lld",
                    LinkerFlavor::Gnu(..) | LinkerFlavor::Darwin(..) | LinkerFlavor::Unix(..) => {
                        "ld"
                    }
                    LinkerFlavor::Msvc(..) => "link.exe",
                    LinkerFlavor::EmCc => {
                        if cfg!(windows) {
                            "emcc.bat"
                        } else {
                            "emcc"
                        }
                    }
                    LinkerFlavor::Bpf => "bpf-linker",
                    LinkerFlavor::Llbc => "llvm-bitcode-linker",
                    LinkerFlavor::Ptx => "rust-ptx-linker",
                }),
                flavor,
            )),
            (Some(linker), None) => {
                let stem = linker.file_stem().and_then(|stem| stem.to_str()).unwrap_or_else(|| {
                    sess.dcx().emit_fatal(errors::LinkerFileStem);
                });
                let flavor = sess.target.linker_flavor.with_linker_hints(stem);
                let flavor = adjust_flavor_to_features(flavor, features);
                Some((linker, flavor))
            }
            (None, None) => None,
        }
    }

    // While linker flavors and linker features are isomorphic (and thus targets don't need to
    // define features separately), we use the flavor as the root piece of data and have the
    // linker-features CLI flag influence *that*, so that downstream code does not have to check for
    // both yet.
    fn adjust_flavor_to_features(
        flavor: LinkerFlavor,
        features: LinkerFeaturesCli,
    ) -> LinkerFlavor {
        // Note: a linker feature cannot be both enabled and disabled on the CLI.
        if features.enabled.contains(LinkerFeatures::LLD) {
            flavor.with_lld_enabled()
        } else if features.disabled.contains(LinkerFeatures::LLD) {
            flavor.with_lld_disabled()
        } else {
            flavor
        }
    }

    let features = sess.opts.cg.linker_features;

    // linker and linker flavor specified via command line have precedence over what the target
    // specification specifies
    let linker_flavor = match sess.opts.cg.linker_flavor {
        // The linker flavors that are non-target specific can be directly translated to LinkerFlavor
        Some(LinkerFlavorCli::Llbc) => Some(LinkerFlavor::Llbc),
        Some(LinkerFlavorCli::Ptx) => Some(LinkerFlavor::Ptx),
        // The linker flavors that corresponds to targets needs logic that keeps the base LinkerFlavor
        linker_flavor => {
            linker_flavor.map(|flavor| sess.target.linker_flavor.with_cli_hints(flavor))
        }
    };
    if let Some(ret) = infer_from(sess, sess.opts.cg.linker.clone(), linker_flavor, features) {
        return ret;
    }

    if let Some(ret) = infer_from(
        sess,
        sess.target.linker.as_deref().map(PathBuf::from),
        Some(sess.target.linker_flavor),
        features,
    ) {
        return ret;
    }

    // tRust: invariant: structural invariant — linker configuration constrains valid options at this point
    bug!("Not enough information provided to determine how to invoke the linker");
}

/// Returns a pair of boolean indicating whether we should preserve the object and
/// dwarf object files on the filesystem for their debug information. This is often
/// useful with split-dwarf like schemes.
fn preserve_objects_for_their_debuginfo(sess: &Session) -> (bool, bool) {
    // If the objects don't have debuginfo there's nothing to preserve.
    if sess.opts.debuginfo == config::DebugInfo::None {
        return (false, false);
    }

    match (sess.split_debuginfo(), sess.opts.unstable_opts.split_dwarf_kind) {
        // If there is no split debuginfo then do not preserve objects.
        (SplitDebuginfo::Off, _) => (false, false),
        // If there is packed split debuginfo, then the debuginfo in the objects
        // has been packaged and the objects can be deleted.
        (SplitDebuginfo::Packed, _) => (false, false),
        // If there is unpacked split debuginfo and the current target can not use
        // split dwarf, then keep objects.
        (SplitDebuginfo::Unpacked, _) if !sess.target_can_use_split_dwarf() => (true, false),
        // If there is unpacked split debuginfo and the target can use split dwarf, then
        // keep the object containing that debuginfo (whether that is an object file or
        // dwarf object file depends on the split dwarf kind).
        (SplitDebuginfo::Unpacked, SplitDwarfKind::Single) => (true, false),
        (SplitDebuginfo::Unpacked, SplitDwarfKind::Split) => (false, true),
    }
}

#[derive(PartialEq)]
enum RlibFlavor {
    Normal,
    StaticlibBase,
}

fn print_native_static_libs(
    sess: &Session,
    out: &OutFileName,
    all_native_libs: &[NativeLib],
    all_rust_dylibs: &[&Path],
) {
    let mut lib_args: Vec<_> = all_native_libs
        .iter()
        .filter(|l| relevant_lib(sess, l))
        .filter_map(|lib| {
            let name = lib.name;
            match lib.kind {
                NativeLibKind::Static { bundle: Some(false), .. }
                | NativeLibKind::Dylib { .. }
                | NativeLibKind::Unspecified => {
                    let verbatim = lib.verbatim;
                    if sess.target.is_like_msvc {
                        let (prefix, suffix) = sess.staticlib_components(verbatim);
                        Some(format!("{prefix}{name}{suffix}"))
                    } else if sess.target.linker_flavor.is_gnu() {
                        Some(format!("-l{}{}", if verbatim { ":" } else { "" }, name))
                    } else {
                        Some(format!("-l{name}"))
                    }
                }
                NativeLibKind::Framework { .. } => {
                    // ld-only syntax, since there are no frameworks in MSVC
                    Some(format!("-framework {name}"))
                }
                // These are included, no need to print them
                NativeLibKind::Static { bundle: None | Some(true), .. }
                | NativeLibKind::LinkArg
                | NativeLibKind::WasmImportModule
                | NativeLibKind::RawDylib { .. } => None,
            }
        })
        // deduplication of consecutive repeated libraries, see rust-lang/rust#113209
        .dedup()
        .collect();
    for path in all_rust_dylibs {
        // NOTE: Logic duplicated with add_dynamic_crate; consolidation desired.

        // Just need to tell the linker about where the library lives and
        // what its name is
        let parent = path.parent();
        if let Some(dir) = parent {
            let dir = fix_windows_verbatim_for_gcc(dir);
            if sess.target.is_like_msvc {
                let mut arg = String::from("/LIBPATH:");
                arg.push_str(&dir.display().to_string());
                lib_args.push(arg);
            } else {
                lib_args.push("-L".to_owned());
                lib_args.push(dir.display().to_string());
            }
        }
        let stem = path.file_stem().expect("invariant: crate path must have file stem").to_str().expect("invariant: path must be valid UTF-8");
        // Convert library file-stem into a cc -l argument.
        let lib = if let Some(lib) = stem.strip_prefix("lib")
            && !sess.target.is_like_windows
        {
            lib
        } else {
            stem
        };
        let path = parent.unwrap_or_else(|| Path::new(""));
        if sess.target.is_like_msvc {
            // When producing a dll, the MSVC linker may not actually emit a
            // `foo.lib` file if the dll doesn't actually export any symbols, so we
            // check to see if the file is there and just omit linking to it if it's
            // not present.
            let name = format!("{lib}.dll.lib");
            if path.join(&name).exists() {
                lib_args.push(name);
            }
        } else {
            lib_args.push(format!("-l{lib}"));
        }
    }

    match out {
        OutFileName::Real(path) => {
            out.overwrite(&lib_args.join(" "), sess);
            sess.dcx().emit_note(errors::StaticLibraryNativeArtifactsToFile { path });
        }
        OutFileName::Stdout => {
            sess.dcx().emit_note(errors::StaticLibraryNativeArtifacts);
            // Prefix for greppability
            // Note: This must not be translated as tools are allowed to depend on this exact string.
            sess.dcx().note(format!("native-static-libs: {}", lib_args.join(" ")));
        }
    }
}

fn get_object_file_path(sess: &Session, name: &str, self_contained: bool) -> PathBuf {
    let file_path = sess.target_tlib_path.dir.join(name);
    if file_path.exists() {
        return file_path;
    }
    // Special directory with objects used only in self-contained linkage mode
    if self_contained {
        let file_path = sess.target_tlib_path.dir.join("self-contained").join(name);
        if file_path.exists() {
            return file_path;
        }
    }
    for search_path in sess.target_filesearch().search_paths(PathKind::Native) {
        let file_path = search_path.dir.join(name);
        if file_path.exists() {
            return file_path;
        }
    }
    PathBuf::from(name)
}

fn exec_linker(
    sess: &Session,
    cmd: &Command,
    out_filename: &Path,
    flavor: LinkerFlavor,
    tmpdir: &Path,
) -> io::Result<Output> {
    // When attempting to spawn the linker we run a risk of blowing out the
    // size limits for spawning a new process with respect to the arguments
    // we pass on the command line.
    //
    // Here we attempt to handle errors from the OS saying "your list of
    // arguments is too big" by reinvoking the linker again with an `@`-file
    // that contains all the arguments (aka 'response' files).
    // The theory is that this is then accepted on all linkers and the linker
    // will read all its options out of there instead of looking at the command line.
    if !cmd.very_likely_to_exceed_some_spawn_limit() {
        match cmd.command().stdout(Stdio::piped()).stderr(Stdio::piped()).spawn() {
            Ok(child) => {
                let output = child.wait_with_output();
                flush_linked_file(&output, out_filename)?;
                return output;
            }
            Err(ref e) if command_line_too_big(e) => {
                info!("command line to linker was too big: {}", e);
            }
            Err(e) => return Err(e),
        }
    }

    info!("falling back to passing arguments to linker via an @-file");
    let mut cmd2 = cmd.clone();
    let mut args = String::new();
    for arg in cmd2.take_args() {
        args.push_str(
            &Escape {
                arg: arg.to_str().expect("invariant: linker argument must be valid UTF-8"),
                // Windows-style escaping for @-files is used by
                // - all linkers targeting MSVC-like targets, including LLD
                // - all LLD flavors running on Windows hosts
                // С/С++ compilers use Posix-style escaping (except clang-cl, which we do not use).
                is_like_msvc: sess.target.is_like_msvc
                    || (cfg!(windows) && flavor.uses_lld() && !flavor.uses_cc()),
            }
            .to_string(),
        );
        args.push('\n');
    }
    let file = tmpdir.join("linker-arguments");
    let bytes = if sess.target.is_like_msvc {
        let mut out = Vec::with_capacity((1 + args.len()) * 2);
        // start the stream with a UTF-16 BOM
        for c in std::iter::once(0xFEFF).chain(args.encode_utf16()) {
            // encode in little endian
            out.push(c as u8);
            out.push((c >> 8) as u8);
        }
        out
    } else {
        args.into_bytes()
    };
    fs::write(&file, &bytes)?;
    cmd2.arg(format!("@{}", file.display()));
    info!("invoking linker {:?}", cmd2);
    let output = cmd2.output();
    flush_linked_file(&output, out_filename)?;
    return output;

    #[cfg(not(windows))]
    fn flush_linked_file(_: &io::Result<Output>, _: &Path) -> io::Result<()> {
        Ok(())
    }

    #[cfg(windows)]
    fn flush_linked_file(
        command_output: &io::Result<Output>,
        out_filename: &Path,
    ) -> io::Result<()> {
        // On Windows, under high I/O load, output buffers are sometimes not flushed,
        // even long after process exit, causing nasty, non-reproducible output bugs.
        //
        // File::sync_all() calls FlushFileBuffers() down the line, which solves the problem.
        //
        // А full writeup of the original Chrome bug can be found at
        // randomascii.wordpress.com/2018/02/25/compiler-bug-linker-bug-windows-kernel-bug/amp

        if let &Ok(ref out) = command_output {
            if out.status.success() {
                if let Ok(of) = fs::OpenOptions::new().write(true).open(out_filename) {
                    of.sync_all()?;
                }
            }
        }

        Ok(())
    }

    #[cfg(unix)]
    fn command_line_too_big(err: &io::Error) -> bool {
        err.raw_os_error() == Some(::libc::E2BIG)
    }

    #[cfg(windows)]
    fn command_line_too_big(err: &io::Error) -> bool {
        const ERROR_FILENAME_EXCED_RANGE: i32 = 206;
        err.raw_os_error() == Some(ERROR_FILENAME_EXCED_RANGE)
    }

    #[cfg(not(any(unix, windows)))]
    fn command_line_too_big(_: &io::Error) -> bool {
        false
    }

    struct Escape<'a> {
        arg: &'a str,
        is_like_msvc: bool,
    }

    impl<'a> fmt::Display for Escape<'a> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if self.is_like_msvc {
                // This is "documented" at
                // https://docs.microsoft.com/en-us/cpp/build/reference/at-specify-a-linker-response-file
                //
                // Unfortunately there's not a great specification of the
                // syntax I could find online (at least) but some local
                // testing showed that this seemed sufficient-ish to catch
                // at least a few edge cases.
                write!(f, "\"")?;
                for c in self.arg.chars() {
                    match c {
                        '"' => write!(f, "\\{c}")?,
                        c => write!(f, "{c}")?,
                    }
                }
                write!(f, "\"")?;
            } else {
                // This is documented at https://linux.die.net/man/1/ld, namely:
                //
                // > Options in file are separated by whitespace. A whitespace
                // > character may be included in an option by surrounding the
                // > entire option in either single or double quotes. Any
                // > character (including a backslash) may be included by
                // > prefixing the character to be included with a backslash.
                //
                // We put an argument on each line, so all we need to do is
                // ensure the line is interpreted as one whole argument.
                for c in self.arg.chars() {
                    match c {
                        '\\' | ' ' => write!(f, "\\{c}")?,
                        c => write!(f, "{c}")?,
                    }
                }
            }
            Ok(())
        }
    }
}

fn link_output_kind(sess: &Session, crate_type: CrateType) -> LinkOutputKind {
    let kind = match (crate_type, sess.crt_static(Some(crate_type)), sess.relocation_model()) {
        (CrateType::Executable, _, _) if sess.is_wasi_reactor() => LinkOutputKind::WasiReactorExe,
        (CrateType::Executable, false, RelocModel::Pic | RelocModel::Pie) => {
            LinkOutputKind::DynamicPicExe
        }
        (CrateType::Executable, false, _) => LinkOutputKind::DynamicNoPicExe,
        (CrateType::Executable, true, RelocModel::Pic | RelocModel::Pie) => {
            LinkOutputKind::StaticPicExe
        }
        (CrateType::Executable, true, _) => LinkOutputKind::StaticNoPicExe,
        (_, true, _) => LinkOutputKind::StaticDylib,
        (_, false, _) => LinkOutputKind::DynamicDylib,
    };

    // Adjust the output kind to target capabilities.
    let opts = &sess.target;
    let pic_exe_supported = opts.position_independent_executables;
    let static_pic_exe_supported = opts.static_position_independent_executables;
    let static_dylib_supported = opts.crt_static_allows_dylibs;
    match kind {
        LinkOutputKind::DynamicPicExe if !pic_exe_supported => LinkOutputKind::DynamicNoPicExe,
        LinkOutputKind::StaticPicExe if !static_pic_exe_supported => LinkOutputKind::StaticNoPicExe,
        LinkOutputKind::StaticDylib if !static_dylib_supported => LinkOutputKind::DynamicDylib,
        _ => kind,
    }
}

// Returns true if linker is located within sysroot
fn detect_self_contained_mingw(sess: &Session, linker: &Path) -> bool {
    let linker_with_extension = if cfg!(windows) && linker.extension().is_none() {
        linker.with_extension("exe")
    } else {
        linker.to_path_buf()
    };
    for dir in env::split_paths(&env::var_os("PATH").unwrap_or_default()) {
        let full_path = dir.join(&linker_with_extension);
        // If linker comes from sysroot assume self-contained mode
        if full_path.is_file() && !full_path.starts_with(sess.opts.sysroot.path()) {
            return false;
        }
    }
    true
}

/// Various toolchain components used during linking are used from rustc distribution
/// instead of being found somewhere on the host system.
/// We only provide such support for a very limited number of targets.
fn self_contained_components(
    sess: &Session,
    crate_type: CrateType,
    linker: &Path,
) -> LinkSelfContainedComponents {
    // Turn the backwards compatible bool values for `self_contained` into fully inferred
    // `LinkSelfContainedComponents`.
    let self_contained =
        if let Some(self_contained) = sess.opts.cg.link_self_contained.explicitly_set {
            // Emit an error if the user requested self-contained mode on the CLI but the target
            // explicitly refuses it.
            if sess.target.link_self_contained.is_disabled() {
                sess.dcx().emit_err(errors::UnsupportedLinkSelfContained);
            }
            self_contained
        } else {
            match sess.target.link_self_contained {
                LinkSelfContainedDefault::False => false,
                LinkSelfContainedDefault::True => true,

                LinkSelfContainedDefault::WithComponents(components) => {
                    // For target specs with explicitly enabled components, we can return them
                    // directly.
                    return components;
                }

                // NOTE: Heuristic for detecting native musl toolchain is imprecise.
                // based on host and linker path, for example.
                // (https://github.com/rust-lang/rust/pull/71769#issuecomment-626330237).
                LinkSelfContainedDefault::InferredForMusl => sess.crt_static(Some(crate_type)),
                LinkSelfContainedDefault::InferredForMingw => {
                    sess.host == sess.target
                        && sess.target.cfg_abi != CfgAbi::Uwp
                        && detect_self_contained_mingw(sess, linker)
                }
            }
        };
    if self_contained {
        LinkSelfContainedComponents::all()
    } else {
        LinkSelfContainedComponents::empty()
    }
}


// tRust: Linker argument construction functions moved to link/linker_args.rs

fn add_native_libs_from_crate(
    cmd: &mut dyn Linker,
    sess: &Session,
    archive_builder_builder: &dyn ArchiveBuilderBuilder,
    crate_info: &CrateInfo,
    tmpdir: &Path,
    bundled_libs: &FxIndexSet<Symbol>,
    cnum: CrateNum,
    link_static: bool,
    link_dynamic: bool,
    link_output_kind: LinkOutputKind,
) {
    if !sess.opts.unstable_opts.link_native_libraries {
        // If `-Zlink-native-libraries=false` is set, then the assumption is that an
        // external build system already has the native dependencies defined, and it
        // will provide them to the linker itself.
        return;
    }

    if link_static && cnum != LOCAL_CRATE && !bundled_libs.is_empty() {
        // If rlib contains native libs as archives, unpack them to tmpdir.
        let rlib = crate_info.used_crate_source[&cnum].rlib.as_ref().expect("invariant: used crate must have rlib source");
        archive_builder_builder
            .extract_bundled_libs(rlib, tmpdir, bundled_libs)
            .unwrap_or_else(|e| sess.dcx().emit_fatal(e));
    }

    let native_libs = match cnum {
        LOCAL_CRATE => &crate_info.used_libraries,
        _ => &crate_info.native_libraries[&cnum],
    };

    let mut last = (None, NativeLibKind::Unspecified, false);
    for lib in native_libs {
        if !relevant_lib(sess, lib) {
            continue;
        }

        // Skip if this library is the same as the last.
        last = if (Some(lib.name), lib.kind, lib.verbatim) == last {
            continue;
        } else {
            (Some(lib.name), lib.kind, lib.verbatim)
        };

        let name = lib.name.as_str();
        let verbatim = lib.verbatim;
        match lib.kind {
            NativeLibKind::Static { bundle, whole_archive, .. } => {
                if link_static {
                    let bundle = bundle.unwrap_or(true);
                    let whole_archive = whole_archive == Some(true);
                    if bundle && cnum != LOCAL_CRATE {
                        if let Some(filename) = lib.filename {
                            // If rlib contains native libs as archives, they are unpacked to tmpdir.
                            let path = tmpdir.join(filename.as_str());
                            cmd.link_staticlib_by_path(&path, whole_archive);
                        }
                    } else {
                        cmd.link_staticlib_by_name(name, verbatim, whole_archive);
                    }
                }
            }
            NativeLibKind::Dylib { as_needed } => {
                if link_dynamic {
                    cmd.link_dylib_by_name(name, verbatim, as_needed.unwrap_or(true))
                }
            }
            NativeLibKind::Unspecified => {
                // If we are generating a static binary, prefer static library when the
                // link kind is unspecified.
                if !link_output_kind.can_link_dylib() && !sess.target.crt_static_allows_dylibs {
                    if link_static {
                        cmd.link_staticlib_by_name(name, verbatim, false);
                    }
                } else if link_dynamic {
                    cmd.link_dylib_by_name(name, verbatim, true);
                }
            }
            NativeLibKind::Framework { as_needed } => {
                if link_dynamic {
                    cmd.link_framework_by_name(name, verbatim, as_needed.unwrap_or(true))
                }
            }
            NativeLibKind::RawDylib { as_needed: _ } => {
                // Handled separately in `linker_with_args`.
            }
            NativeLibKind::WasmImportModule => {}
            NativeLibKind::LinkArg => {
                if link_static {
                    if verbatim {
                        cmd.verbatim_arg(name);
                    } else {
                        cmd.link_arg(name);
                    }
                }
            }
        }
    }
}

fn add_local_native_libraries(
    cmd: &mut dyn Linker,
    sess: &Session,
    archive_builder_builder: &dyn ArchiveBuilderBuilder,
    crate_info: &CrateInfo,
    tmpdir: &Path,
    link_output_kind: LinkOutputKind,
) {
    // All static and dynamic native library dependencies are linked to the local crate.
    let link_static = true;
    let link_dynamic = true;
    add_native_libs_from_crate(
        cmd,
        sess,
        archive_builder_builder,
        crate_info,
        tmpdir,
        &Default::default(),
        LOCAL_CRATE,
        link_static,
        link_dynamic,
        link_output_kind,
    );
}

fn add_upstream_rust_crates(
    cmd: &mut dyn Linker,
    sess: &Session,
    archive_builder_builder: &dyn ArchiveBuilderBuilder,
    crate_info: &CrateInfo,
    crate_type: CrateType,
    tmpdir: &Path,
    link_output_kind: LinkOutputKind,
) {
    // All of the heavy lifting has previously been accomplished by the
    // dependency_format module of the compiler. This is just crawling the
    // output of that module, adding crates as necessary.
    //
    // Linking to a rlib involves just passing it to the linker (the linker
    // will slurp up the object files inside), and linking to a dynamic library
    // involves just passing the right -l flag.
    let data = crate_info
        .dependency_formats
        .get(&crate_type)
        .expect("failed to find crate type in dependency format list");

    if sess.target.is_like_aix {
        // Unlike ELF linkers, AIX doesn't feature `DT_SONAME` to override
        // the dependency name when outputting a shared library. Thus, `ld` will
        // use the full path to shared libraries as the dependency if passed it
        // by default unless `noipath` is passed.
        // https://www.ibm.com/docs/en/aix/7.3?topic=l-ld-command.
        cmd.link_or_cc_arg("-bnoipath");
    }

    for &cnum in &crate_info.used_crates {
        // We may not pass all crates through to the linker. Some crates may appear statically in
        // an existing dylib, meaning we'll pick up all the symbols from the dylib.
        // We must always link crates `compiler_builtins` and `profiler_builtins` statically.
        // Even if they were already included into a dylib
        // (e.g. `libstd` when `-C prefer-dynamic` is used).
        let linkage = data[cnum];
        let link_static_crate = linkage == Linkage::Static
            || linkage == Linkage::IncludedFromDylib
                && (crate_info.compiler_builtins == Some(cnum)
                    || crate_info.profiler_runtime == Some(cnum));

        let mut bundled_libs = Default::default();
        match linkage {
            Linkage::Static | Linkage::IncludedFromDylib | Linkage::NotLinked => {
                if link_static_crate {
                    bundled_libs = crate_info.native_libraries[&cnum]
                        .iter()
                        .filter_map(|lib| lib.filename)
                        .collect();
                    add_static_crate(
                        cmd,
                        sess,
                        archive_builder_builder,
                        crate_info,
                        tmpdir,
                        cnum,
                        &bundled_libs,
                    );
                }
            }
            Linkage::Dynamic => {
                let src = &crate_info.used_crate_source[&cnum];
                add_dynamic_crate(cmd, sess, src.dylib.as_ref().expect("invariant: dynamic crate must have dylib source"));
            }
        }

        // Static libraries are linked for a subset of linked upstream crates.
        // 1. If the upstream crate is a directly linked rlib then we must link the native library
        // because the rlib is just an archive.
        // 2. If the upstream crate is a dylib or a rlib linked through dylib, then we do not link
        // the native library because it is already linked into the dylib, and even if
        // inline/const/generic functions from the dylib can refer to symbols from the native
        // library, those symbols should be exported and available from the dylib anyway.
        // 3. Libraries bundled into `(compiler,profiler)_builtins` are special, see above.
        let link_static = link_static_crate;
        // Dynamic libraries are not linked here; see NOTE in add_upstream_native_libraries.
        let link_dynamic = false;
        add_native_libs_from_crate(
            cmd,
            sess,
            archive_builder_builder,
            crate_info,
            tmpdir,
            &bundled_libs,
            cnum,
            link_static,
            link_dynamic,
            link_output_kind,
        );
    }
}

fn add_upstream_native_libraries(
    cmd: &mut dyn Linker,
    sess: &Session,
    archive_builder_builder: &dyn ArchiveBuilderBuilder,
    crate_info: &CrateInfo,
    tmpdir: &Path,
    link_output_kind: LinkOutputKind,
) {
    for &cnum in &crate_info.used_crates {
        // Static libraries are not linked here, they are linked in `add_upstream_rust_crates`.
        // NOTE: This function could be merged with add_upstream_rust_crates for unified
        // native library handling.
        // are linked together with their respective upstream crates, and in their originally
        // specified order. This is slightly breaking due to our use of `--as-needed` (see crater
        // results in https://github.com/rust-lang/rust/pull/102832#issuecomment-1279772306).
        let link_static = false;
        // Dynamic libraries are linked for all linked upstream crates.
        // 1. If the upstream crate is a directly linked rlib then we must link the native library
        // because the rlib is just an archive.
        // 2. If the upstream crate is a dylib or a rlib linked through dylib, then we have to link
        // the native library too because inline/const/generic functions from the dylib can refer
        // to symbols from the native library, so the native library providing those symbols should
        // be available when linking our final binary.
        let link_dynamic = true;
        add_native_libs_from_crate(
            cmd,
            sess,
            archive_builder_builder,
            crate_info,
            tmpdir,
            &Default::default(),
            cnum,
            link_static,
            link_dynamic,
            link_output_kind,
        );
    }
}

// Rehome lib paths (which exclude the library file name) that point into the sysroot lib directory
// to be relative to the sysroot directory, which may be a relative path specified by the user.
//
// If the sysroot is a relative path, and the sysroot libs are specified as an absolute path, the
// linker command line can be non-deterministic due to the paths including the current working
// directory. The linker command line needs to be deterministic since it appears inside the PDB
// file generated by the MSVC linker. See https://github.com/rust-lang/rust/issues/112586.
//
// The returned path will always have `fix_windows_verbatim_for_gcc()` applied to it.
fn rehome_sysroot_lib_dir(sess: &Session, lib_dir: &Path) -> PathBuf {
    let sysroot_lib_path = &sess.target_tlib_path.dir;
    let canonical_sysroot_lib_path =
        { try_canonicalize(sysroot_lib_path).unwrap_or_else(|_| sysroot_lib_path.clone()) };

    let canonical_lib_dir = try_canonicalize(lib_dir).unwrap_or_else(|_| lib_dir.to_path_buf());
    if canonical_lib_dir == canonical_sysroot_lib_path {
        // This path already had `fix_windows_verbatim_for_gcc()` applied if needed.
        sysroot_lib_path.clone()
    } else {
        fix_windows_verbatim_for_gcc(lib_dir)
    }
}

fn rehome_lib_path(sess: &Session, path: &Path) -> PathBuf {
    if let Some(dir) = path.parent() {
        let file_name = path.file_name().expect("library path has no file name component");
        rehome_sysroot_lib_dir(sess, dir).join(file_name)
    } else {
        fix_windows_verbatim_for_gcc(path)
    }
}

// Adds the static "rlib" versions of all crates to the command line.
// There's a bit of magic which happens here specifically related to LTO,
// namely that we remove upstream object files.
//
// When performing LTO, almost(*) all of the bytecode from the upstream
// libraries has already been included in our object file output. As a
// result we need to remove the object files in the upstream libraries so
// the linker doesn't try to include them twice (or whine about duplicate
// symbols). We must continue to include the rest of the rlib, however, as
// it may contain static native libraries which must be linked in.
//
// (*) Crates marked with `#![no_builtins]` don't participate in LTO and
// their bytecode wasn't included. The object files in those libraries must
// still be passed to the linker.
//
// Note, however, that if we're not doing LTO we can just pass the rlib
// blindly to the linker (fast) because it's fine if it's not actually
// included as we're at the end of the dependency chain.
fn add_static_crate(
    cmd: &mut dyn Linker,
    sess: &Session,
    archive_builder_builder: &dyn ArchiveBuilderBuilder,
    crate_info: &CrateInfo,
    tmpdir: &Path,
    cnum: CrateNum,
    bundled_lib_file_names: &FxIndexSet<Symbol>,
) {
    let src = &crate_info.used_crate_source[&cnum];
    let cratepath = src.rlib.as_ref().expect("invariant: rlib crate must have rlib source");

    let mut link_upstream =
        |path: &Path| cmd.link_staticlib_by_path(&rehome_lib_path(sess, path), false);

    if !are_upstream_rust_objects_already_included(sess) || ignored_for_lto(sess, crate_info, cnum)
    {
        link_upstream(cratepath);
        return;
    }

    let dst = tmpdir.join(cratepath.file_name().expect("invariant: crate path must have filename"));
    let name = cratepath.file_name().expect("invariant: crate path must have filename").to_str().expect("invariant: path must be valid UTF-8");
    let name = &name[3..name.len() - 5]; // chop off lib/.rlib
    let bundled_lib_file_names = bundled_lib_file_names.clone();

    sess.prof.generic_activity_with_arg("link_altering_rlib", name).run(|| {
        let canonical_name = name.replace('-', "_");
        let upstream_rust_objects_already_included =
            are_upstream_rust_objects_already_included(sess);
        let is_builtins = sess.target.no_builtins || !crate_info.is_no_builtins.contains(&cnum);

        let mut archive = archive_builder_builder.new_archive_builder(sess);
        if let Err(error) = archive.add_archive(
            cratepath,
            Box::new(move |f| {
                if f == METADATA_FILENAME {
                    return true;
                }

                let canonical = f.replace('-', "_");

                let is_rust_object =
                    canonical.starts_with(&canonical_name) && looks_like_rust_object_file(f);

                // If we're performing LTO and this is a rust-generated object
                // file, then we don't need the object file as it's part of the
                // LTO module. Note that `#![no_builtins]` is excluded from LTO,
                // though, so we let that object file slide.
                if upstream_rust_objects_already_included && is_rust_object && is_builtins {
                    return true;
                }

                // We skip native libraries because:
                // 1. This native libraries won't be used from the generated rlib,
                //    so we can throw them away to avoid the copying work.
                // 2. We can't allow it to be a single remaining entry in archive
                //    as some linkers may complain on that.
                if bundled_lib_file_names.contains(&Symbol::intern(f)) {
                    return true;
                }

                false
            }),
        ) {
            sess.dcx()
                .emit_fatal(errors::RlibArchiveBuildFailure { path: cratepath.clone(), error });
        }
        if archive.build(&dst) {
            link_upstream(&dst);
        }
    });
}

// Same thing as above, but for dynamic crates instead of static crates.
fn add_dynamic_crate(cmd: &mut dyn Linker, sess: &Session, cratepath: &Path) {
    cmd.link_dylib_by_path(&rehome_lib_path(sess, cratepath), true);
}

fn relevant_lib(sess: &Session, lib: &NativeLib) -> bool {
    match lib.cfg {
        Some(ref cfg) => eval_config_entry(sess, cfg).as_bool(),
        None => true,
    }
}

pub(crate) fn are_upstream_rust_objects_already_included(sess: &Session) -> bool {
    match sess.lto() {
        config::Lto::Fat => true,
        config::Lto::Thin => {
            // If we defer LTO to the linker, we haven't run LTO ourselves, so
            // any upstream object files have not been copied yet.
            !sess.opts.cg.linker_plugin_lto.enabled()
        }
        config::Lto::No | config::Lto::ThinLocal => false,
    }
}

// tRust: Apple linking functions moved to link/apple_link.rs
// tRust: LLD functions moved to link/lld.rs
