// tRust: LLD-specific linker logic, extracted from link.rs
// Author: Andrew Yates <andrew@andrewdyates.com>

use std::ffi::OsString;
use std::fs::File;
use std::io::BufReader;
use std::path::Path;

use object::read::elf::{FileHeader, SectionHeader};
use object::read::{ReadCache, ReadRef, Result};
use object::{Endianness, elf};
use rustc_session::Session;
use rustc_target::spec::{LinkSelfContainedComponents, LinkerFlavor};
use tracing::debug;

use super::super::linker::Linker;
use super::super::versioned_llvm_target;
use crate::errors;

/// When using the linker flavors opting in to `lld`, add the necessary paths and arguments to
/// invoke it:
/// - when the self-contained linker flag is active: the build of `lld` distributed with rustc,
/// - or any `lld` available to `cc`.
pub(super) fn add_lld_args(
    cmd: &mut dyn Linker,
    sess: &Session,
    flavor: LinkerFlavor,
    self_contained_components: LinkSelfContainedComponents,
) {
    debug!(
        "add_lld_args requested, flavor: '{:?}', target self-contained components: {:?}",
        flavor, self_contained_components,
    );

    // If the flavor doesn't use a C/C++ compiler to invoke the linker, or doesn't opt in to `lld`,
    // we don't need to do anything.
    if !(flavor.uses_cc() && flavor.uses_lld()) {
        return;
    }

    // 1. Implement the "self-contained" part of this feature by adding rustc distribution
    // directories to the tool's search path, depending on a mix between what users can specify on
    // the CLI, and what the target spec enables (as it can't disable components):
    // - if the self-contained linker is enabled on the CLI or by the target spec,
    // - and if the self-contained linker is not disabled on the CLI.
    let self_contained_cli = sess.opts.cg.link_self_contained.is_linker_enabled();
    let self_contained_target = self_contained_components.is_linker_enabled();

    let self_contained_linker = self_contained_cli || self_contained_target;
    if self_contained_linker && !sess.opts.cg.link_self_contained.is_linker_disabled() {
        let mut linker_path_exists = false;
        for path in sess.get_tools_search_paths(false) {
            let linker_path = path.join("gcc-ld");
            linker_path_exists |= linker_path.exists();
            cmd.cc_arg({
                let mut arg = OsString::from("-B");
                arg.push(linker_path);
                arg
            });
        }
        if !linker_path_exists {
            // As a sanity check, we emit an error if none of these paths exist: we want
            // self-contained linking and have no linker.
            sess.dcx().emit_fatal(errors::SelfContainedLinkerMissing);
        }
    }

    // 2. Implement the "linker flavor" part of this feature by asking `cc` to use some kind of
    // `lld` as the linker.
    //
    // Note that wasm targets skip this step since the only option there anyway
    // is to use LLD but the `wasm32-wasip2` target relies on a wrapper around
    // this, `wasm-component-ld`, which is overridden if this option is passed.
    if !sess.target.is_like_wasm {
        cmd.cc_arg("-fuse-ld=lld");
    }

    if !flavor.is_gnu() {
        // Tell clang to use a non-default LLD flavor.
        // Gcc doesn't understand the target option, but we currently assume
        // that gcc is not used for Apple and Wasm targets (#97402).
        //
        // Note that we don't want to do that by default on macOS: e.g. passing a
        // 10.7 target to LLVM works, but not to recent versions of clang/macOS, as
        // shown in issue #101653 and the discussion in PR #101792.
        //
        // It could be required in some cases of cross-compiling with
        // LLD, but this is generally unspecified, and we don't know
        // which specific versions of clang, macOS SDK, host and target OS
        // combinations impact us here.
        //
        // So we do a simple first-approximation until we know more of what the
        // Apple targets require (and which would be handled prior to hitting this
        // LLD codepath anyway), but the expectation is that until then
        // this should be manually passed if needed. We specify the target when
        // targeting a different linker flavor on macOS, and that's also always
        // the case when targeting WASM.
        if sess.target.linker_flavor != sess.host.linker_flavor {
            cmd.cc_arg(format!("--target={}", versioned_llvm_target(sess)));
        }
    }
}

// gold has been deprecated with binutils 2.44
// and is known to behave incorrectly around Rust programs.
// There have been reports of being unable to bootstrap with gold:
// https://github.com/rust-lang/rust/issues/139425
// Additionally, gold miscompiles SHF_GNU_RETAIN sections, which are
// emitted with `#[used(linker)]`.
pub(super) fn warn_if_linked_with_gold(sess: &Session, path: &Path) -> std::result::Result<(), Box<dyn std::error::Error>> {
    fn elf_has_gold_version_note<'a>(
        elf: &impl FileHeader,
        data: impl ReadRef<'a>,
    ) -> Result<bool> {
        let endian = elf.endian()?;

        let section =
            elf.sections(endian, data)?.section_by_name(endian, b".note.gnu.gold-version");
        if let Some((_, section)) = section
            && let Some(mut notes) = section.notes(endian, data)?
        {
            return Ok(notes.any(|note| {
                note.is_ok_and(|note| note.n_type(endian) == elf::NT_GNU_GOLD_VERSION)
            }));
        }

        Ok(false)
    }

    let data = ReadCache::new(BufReader::new(File::open(path)?));

    let was_linked_with_gold = if sess.target.pointer_width == 64 {
        let elf = elf::FileHeader64::<Endianness>::parse(&data)?;
        elf_has_gold_version_note(elf, &data)?
    } else if sess.target.pointer_width == 32 {
        let elf = elf::FileHeader32::<Endianness>::parse(&data)?;
        elf_has_gold_version_note(elf, &data)?
    } else {
        return Ok(());
    };

    if was_linked_with_gold {
        let mut warn =
            sess.dcx().struct_warn("the gold linker is deprecated and has known bugs with Rust");
        warn.help("consider using LLD or ld from GNU binutils instead");
        warn.emit();
    }
    Ok(())
}
