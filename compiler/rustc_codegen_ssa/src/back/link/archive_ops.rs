// tRust: Archive operations for rlib and staticlib creation, extracted from link.rs
// Author: Andrew Yates <andrew@andrewdyates.com>

use std::fs::{File, read};
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};

use rustc_arena::TypedArena;
use rustc_data_structures::fx::FxIndexSet;
use rustc_data_structures::memmap::Mmap;
use rustc_data_structures::temp_dir::MaybeTempDir;
use rustc_hir::def_id::{CrateNum, LOCAL_CRATE};
use rustc_metadata::fs::{METADATA_FILENAME, emit_wrapper_file};
use rustc_metadata::{EncodedMetadata, find_native_static_library};
use rustc_middle::middle::dependency_format::Linkage;
use rustc_session::Session;
use rustc_session::config::{CrateType, OutFileName, PrintKind, SplitDwarfKind};
use rustc_span::Symbol;
use tracing::{debug, info};

use super::super::archive::{ArchiveBuilder, ArchiveBuilderBuilder};
use super::super::metadata::{MetadataPosition, create_wrapper_file};
use super::raw_dylib;
use crate::{CompiledModule, CompiledModules, CrateInfo, NativeLib, errors, looks_like_rust_object_file};

/// Create an 'rlib'.
///
/// An rlib in its current incarnation is essentially a renamed .a file (with "dummy" object files).
/// The rlib primarily contains the object file of the crate, but it also some of the object files
/// from native libraries.
pub(super) fn link_rlib<'a>(
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
        let rustc_hir::attrs::NativeLibKind::Static { bundle: None | Some(true), .. } = lib.kind
        else {
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
pub(super) fn link_staticlib(
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

    let res = super::each_linked_rlib(crate_info, Some(CrateType::StaticLib), &mut |cnum, path| {
        let lto = super::native_libs::are_upstream_rust_objects_already_included(sess)
            && !super::native_libs::ignored_for_lto(sess, crate_info, cnum);

        let native_libs = crate_info.native_libraries[&cnum].iter();
        let relevant = native_libs.clone().filter(|lib| super::native_libs::relevant_lib(sess, lib));
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
        .unwrap(); // tRust: replaced unwrap with expect

        archive_builder_builder
            .extract_bundled_libs(path, tempdir.as_ref(), &relevant_libs)
            .unwrap_or_else(|e| sess.dcx().emit_fatal(e));

        for filename in relevant_libs.iter() {
            let joined = tempdir.as_ref().join(filename.as_str());
            let path = joined.as_path();
            ab.add_archive(path, Box::new(|_| false)).unwrap(); // tRust: replaced unwrap with expect
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
            super::linker_config::print_native_static_libs(sess, &print.out, &all_native_libs, &all_rust_dylibs);
        }
    }
}

/// Use `thorin` (rust implementation of a dwarf packaging utility) to link DWARF objects into a
/// DWARF package.
pub(super) fn link_dwarf_object(
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
            std::fs::OpenOptions::new()
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

#[derive(PartialEq)]
pub(super) enum RlibFlavor {
    Normal,
    StaticlibBase,
}
