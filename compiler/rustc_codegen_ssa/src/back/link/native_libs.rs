// tRust: Native library linking functions, extracted from link.rs
// Author: Andrew Yates <andrew@andrewdyates.com>

use std::path::{Path, PathBuf};

use rustc_attr_parsing::eval_config_entry;
use rustc_data_structures::fx::FxIndexSet;
use rustc_fs_util::fix_windows_verbatim_for_gcc;
use rustc_hir::attrs::NativeLibKind;
use rustc_hir::def_id::{CrateNum, LOCAL_CRATE};
use rustc_metadata::fs::METADATA_FILENAME;
use rustc_middle::middle::dependency_format::Linkage;
use rustc_session::Session;
use rustc_session::config::{self, CrateType};
use rustc_session::search_paths::PathKind;
use rustc_session::filesearch;
use rustc_span::Symbol;
use rustc_target::spec::{
    Cc, LinkOutputKind, LinkerFlavor, Lld, SanitizerSet,
};
use tracing::info;

use super::super::archive::ArchiveBuilderBuilder;
use super::super::linker::Linker;
use crate::{CrateInfo, NativeLib, errors, looks_like_rust_object_file};

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

pub(super) fn add_native_libs_from_crate(
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
        let rlib = crate_info.used_crate_source[&cnum].rlib.as_ref().unwrap();
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

pub(super) fn add_local_native_libraries(
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

pub(super) fn add_upstream_rust_crates(
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
                add_dynamic_crate(cmd, sess, src.dylib.as_ref().unwrap());
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

pub(super) fn add_upstream_native_libraries(
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
        { rustc_fs_util::try_canonicalize(sysroot_lib_path).unwrap_or_else(|_| sysroot_lib_path.clone()) };

    let canonical_lib_dir = rustc_fs_util::try_canonicalize(lib_dir).unwrap_or_else(|_| lib_dir.to_path_buf());
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
    let cratepath = src.rlib.as_ref().unwrap();

    let mut link_upstream =
        |path: &Path| cmd.link_staticlib_by_path(&rehome_lib_path(sess, path), false);

    if !are_upstream_rust_objects_already_included(sess) || ignored_for_lto(sess, crate_info, cnum)
    {
        link_upstream(cratepath);
        return;
    }

    let dst = tmpdir.join(cratepath.file_name().unwrap());
    let name = cratepath.file_name().unwrap().to_str().unwrap();
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

pub(super) fn relevant_lib(sess: &Session, lib: &NativeLib) -> bool {
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

pub(super) fn add_sanitizer_libraries(
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

pub(super) fn get_object_file_path(sess: &Session, name: &str, self_contained: bool) -> PathBuf {
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
