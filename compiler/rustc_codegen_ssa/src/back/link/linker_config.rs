// tRust: Linker configuration and detection, extracted from link.rs
// Author: Andrew Yates <andrew@andrewdyates.com>

use std::path::{Path, PathBuf};
use std::{env, str};

use itertools::Itertools;
use rustc_fs_util::fix_windows_verbatim_for_gcc;
use rustc_middle::bug;
use rustc_session::Session;
use rustc_session::config::{
    self, CrateType, LinkerFeaturesCli, OutFileName, SplitDwarfKind,
};
use rustc_target::spec::{
    Cc, CfgAbi, LinkOutputKind, LinkSelfContainedComponents,
    LinkSelfContainedDefault, LinkerFeatures, LinkerFlavor, LinkerFlavorCli, Lld, RelocModel,
    SplitDebuginfo,
};
use tracing::info;

use crate::{NativeLib, errors};

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

    // tRust: invariant: structural invariant -- linker configuration constrains valid options at this point
    bug!("Not enough information provided to determine how to invoke the linker");
}

/// Returns a pair of boolean indicating whether we should preserve the object and
/// dwarf object files on the filesystem for their debug information. This is often
/// useful with split-dwarf like schemes.
pub(super) fn preserve_objects_for_their_debuginfo(sess: &Session) -> (bool, bool) {
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

pub(super) fn link_output_kind(sess: &Session, crate_type: CrateType) -> LinkOutputKind {
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
pub(super) fn self_contained_components(
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

pub(super) fn print_native_static_libs(
    sess: &Session,
    out: &OutFileName,
    all_native_libs: &[NativeLib],
    all_rust_dylibs: &[&Path],
) {
    let mut lib_args: Vec<_> = all_native_libs
        .iter()
        .filter(|l| super::native_libs::relevant_lib(sess, l))
        .filter_map(|lib| {
            let name = lib.name;
            match lib.kind {
                rustc_hir::attrs::NativeLibKind::Static { bundle: Some(false), .. }
                | rustc_hir::attrs::NativeLibKind::Dylib { .. }
                | rustc_hir::attrs::NativeLibKind::Unspecified => {
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
                rustc_hir::attrs::NativeLibKind::Framework { .. } => {
                    // ld-only syntax, since there are no frameworks in MSVC
                    Some(format!("-framework {name}"))
                }
                // These are included, no need to print them
                rustc_hir::attrs::NativeLibKind::Static { bundle: None | Some(true), .. }
                | rustc_hir::attrs::NativeLibKind::LinkArg
                | rustc_hir::attrs::NativeLibKind::WasmImportModule
                | rustc_hir::attrs::NativeLibKind::RawDylib { .. } => None,
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
        let stem = path.file_stem().unwrap().to_str().unwrap();
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
