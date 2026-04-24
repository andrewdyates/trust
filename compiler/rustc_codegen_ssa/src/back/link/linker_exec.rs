// tRust: Linker execution, output handling, and strip utilities, extracted from link.rs
// Author: Andrew Yates <andrew@andrewdyates.com>

use std::path::{Path, PathBuf};
use std::process::{Output, Stdio};
use std::{env, fmt, fs, io, mem, str};

use regex::Regex;
use rustc_data_structures::temp_dir::MaybeTempDir;
use rustc_errors::DiagCtxtHandle;
use rustc_fs_util::TempDirBuilder;
use rustc_macros::Diagnostic;
use rustc_metadata::EncodedMetadata;
use rustc_metadata::fs::copy_to_stdout;
use rustc_middle::bug;
use rustc_middle::lint::emit_lint_base;
use rustc_lint_defs::builtin::LINKER_INFO;
use rustc_session::Session;
use rustc_session::config::{
    CrateType, DebugInfo, OutputFilenames, OutputType, PrintKind,
    Strip,
};
use rustc_session::lint::builtin::LINKER_MESSAGES;
use rustc_session::output::{check_file_is_writeable, out_filename};
use rustc_target::spec::{
    BinaryFormat, Cc, LinkOutputKind,
    LinkerFlavor, Lld, SplitDebuginfo,
};
use rustc_target::spec::crt_objects::CrtObjects;
use tracing::{debug, info, warn};

use super::super::archive::ArchiveBuilderBuilder;
use super::super::command::Command;
use super::super::linker::{self, Linker};
use super::archive_ops;
use super::linker_args;
use super::native_libs;
use crate::{CodegenLintLevels, CompiledModule, CompiledModules, CrateInfo, errors};

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

        if rustc_session::output::invalid_output_for_target(sess, crate_type) {
            // tRust: invariant: structural invariant -- linker configuration constrains valid options at this point
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

            let crate_name = crate_info.local_crate_name.to_string(); // tRust: simplified from format!("{}", ...)
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
                    archive_ops::link_rlib(
                        sess,
                        archive_builder_builder,
                        &compiled_modules,
                        &crate_info,
                        &metadata,
                        archive_ops::RlibFlavor::Normal,
                        &path,
                    )
                    .build(&out_filename);
                }
                CrateType::StaticLib => {
                    archive_ops::link_staticlib(
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
                if let Err(err) = super::lld::warn_if_linked_with_gold(sess, &out_filename) {
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

    // tRust: Clean stale .rcgu.o files from previous incremental sessions on macOS.
    // This fixes rust-lang#108216: with incremental compilation and unpacked debuginfo
    // (the macOS default), stale object files from previous sessions can corrupt
    // debug info when dsymutil or debuggers reference them. We collect the set of
    // valid object file paths for this session and remove any other .rcgu.o files
    // in the output directory.
    if sess.target.is_like_osx
        && sess.opts.incremental.is_some()
        && sess.split_debuginfo() == SplitDebuginfo::Unpacked
    {
        sess.time("link_binary_clean_stale_objects", || {
            // tRust: Collect all valid object paths from the current compilation session.
            let valid_objects: std::collections::HashSet<PathBuf> = compiled_modules
                .modules
                .iter()
                .chain(compiled_modules.allocator_module.iter())
                .filter_map(|m| m.object.as_ref())
                .map(|p| p.canonicalize().unwrap_or_else(|_| p.clone()))
                .collect();

            // tRust: Determine the output directory from the first object file's parent.
            let obj_dir = compiled_modules
                .modules
                .iter()
                .filter_map(|m| m.object.as_ref())
                .find_map(|p| p.parent().map(Path::to_path_buf));

            if let Some(dir) = obj_dir {
                if let Ok(entries) = fs::read_dir(&dir) {
                    for entry in entries.flatten() {
                        let path = entry.path();
                        if let Some(filename) = path.file_name().and_then(|f| f.to_str()) {
                            if crate::looks_like_rust_object_file(filename) {
                                let canonical = path
                                    .canonicalize()
                                    .unwrap_or_else(|_| path.clone());
                                if !valid_objects.contains(&canonical) {
                                    debug!(
                                        "tRust: removing stale object file: {}",
                                        path.display()
                                    );
                                    let _ = fs::remove_file(&path);
                                }
                            }
                        }
                    }
                }
            }
        });
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
        let (preserve_objects, preserve_dwarf_objects) = super::linker_config::preserve_objects_for_their_debuginfo(sess);
        debug!(?preserve_objects, ?preserve_dwarf_objects);

        for module in &compiled_modules.modules {
            maybe_remove_temps_from_module(preserve_objects, preserve_dwarf_objects, module);
        }
    });
}

#[derive(Diagnostic)]
#[diag("{$inner}")]
/// Translating this is kind of useless. We don't pass translation flags to the linker, so we'd just
/// end up with inconsistent languages within the same diagnostic.
struct LinkerOutput {
    inner: String,
}

fn is_msvc_link_exe(sess: &Session) -> bool {
    let (linker_path, flavor) = super::linker_config::linker_and_flavor(sess);
    sess.target.is_like_msvc
        && flavor == LinkerFlavor::Msvc(Lld::No)
        // Match exactly "link.exe"
        && linker_path.to_str() == Some("link.exe")
}

fn is_macos_ld(sess: &Session) -> bool {
    let (_, flavor) = super::linker_config::linker_and_flavor(sess);
    sess.target.is_like_darwin && matches!(flavor, LinkerFlavor::Darwin(_, Lld::No))
}

fn is_windows_gnu_ld(sess: &Session) -> bool {
    let (_, flavor) = super::linker_config::linker_and_flavor(sess);
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
    // tRust: ABI soundness — linker must have at least one object or bitcode to link
    debug_assert!(
        !compiled_modules.modules.is_empty(),
        "tRust: link_natively called with no compiled modules for crate type {:?}",
        crate_type
    );
    // tRust: ABI soundness — output path must have a parent directory
    debug_assert!(
        out_filename.parent().is_some(),
        "tRust: linker output path must have a parent directory: {:?}",
        out_filename
    );
    // tRust: ABI soundness — tmpdir must exist for linker temporaries
    debug_assert!(
        tmpdir.exists(),
        "tRust: linker tmpdir must exist: {:?}",
        tmpdir
    );

    info!("preparing {:?} to {:?}", crate_type, out_filename);
    let (linker_path, flavor) = super::linker_config::linker_and_flavor(sess);
    let self_contained_components = super::linker_config::self_contained_components(sess, crate_type, &linker_path);

    // On AIX, we ship all libraries as .a big_af archive
    // the expected format is lib<name>.a(libname.so) for the actual
    // dynamic library. So we link to a temporary .so file to be archived
    // at the final out_filename location
    let should_archive = crate_type != CrateType::Executable && sess.target.is_like_aix;
    let archive_member =
        should_archive.then(|| tmpdir.join(out_filename.file_name().unwrap()).with_extension("so"));
    let temp_filename = archive_member.as_deref().unwrap_or(out_filename);

    let mut cmd = linker_args::linker_with_args(
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
        Regex::new(r"(unknown|unrecognized) (command line )?(option|argument)").unwrap();
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
                        native_libs::get_object_file_path(sess, obj, self_contained_crt_objects).into_os_string()
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
            archive_ops::link_dwarf_object(sess, compiled_modules, crate_info, out_filename)
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
    cmd.env("PATH", env::join_paths(new_path).unwrap());

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

pub(super) fn escape_string(s: &[u8]) -> String {
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
                arg: arg.to_str().unwrap(),
                // Windows-style escaping for @-files is used by
                // - all linkers targeting MSVC-like targets, including LLD
                // - all LLD flavors running on Windows hosts
                // C/C++ compilers use Posix-style escaping (except clang-cl, which we do not use).
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
        // A full writeup of the original Chrome bug can be found at
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

