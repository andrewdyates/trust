// tRust: Apple/macOS specific linking functions, extracted from link.rs
// Author: Andrew Yates <andrew@andrewdyates.com>

use std::env;
use std::path::{Path, PathBuf};

use rustc_middle::bug;
use rustc_session::Session;
use rustc_target::spec::{Cc, Env, LinkerFlavor, Os};

use super::super::{apple, versioned_llvm_target};
use super::super::linker::Linker;

/// We need to communicate five things to the linker on Apple/Darwin targets:
/// - The architecture.
/// - The operating system (and that it's an Apple platform).
/// - The environment.
/// - The deployment target.
/// - The SDK version.
pub(super) fn add_apple_link_args(cmd: &mut dyn Linker, sess: &Session, flavor: LinkerFlavor) {
    if !sess.target.is_like_darwin {
        return;
    }
    let LinkerFlavor::Darwin(cc, _) = flavor else {
        return;
    };

    // `sess.target.arch` (`target_arch`) is not detailed enough.
    let llvm_arch = sess.target.llvm_target.split_once('-').expect("LLVM target must have arch").0;
    let target_os = &sess.target.os;
    let target_env = &sess.target.env;

    // The architecture name to forward to the linker.
    //
    // Supported architecture names can be found in the source:
    // https://github.com/apple-oss-distributions/ld64/blob/ld64-951.9/src/abstraction/MachOFileAbstraction.hpp#L578-L648
    //
    // Intentionally verbose to ensure that the list always matches correctly
    // with the list in the source above.
    let ld64_arch = match llvm_arch {
        "armv7k" => "armv7k",
        "armv7s" => "armv7s",
        "arm64" => "arm64",
        "arm64e" => "arm64e",
        "arm64_32" => "arm64_32",
        // ld64 doesn't understand i686, so fall back to i386 instead.
        //
        // Same story when linking with cc, since that ends up invoking ld64.
        "i386" | "i686" => "i386",
        "x86_64" => "x86_64",
        "x86_64h" => "x86_64h",
        // tRust: invariant: structural invariant — linker configuration constrains valid options at this point
        _ => bug!("unsupported architecture in Apple target: {}", sess.target.llvm_target),
    };

    if cc == Cc::No {
        // From the man page for ld64 (`man ld`):
        // > The linker accepts universal (multiple-architecture) input files,
        // > but always creates a "thin" (single-architecture), standard
        // > Mach-O output file. The architecture for the output file is
        // > specified using the -arch option.
        //
        // The linker has heuristics to determine the desired architecture,
        // but to be safe, and to avoid a warning, we set the architecture
        // explicitly.
        cmd.link_args(&["-arch", ld64_arch]);

        // Man page says that ld64 supports the following platform names:
        // > - macos
        // > - ios
        // > - tvos
        // > - watchos
        // > - bridgeos
        // > - visionos
        // > - xros
        // > - mac-catalyst
        // > - ios-simulator
        // > - tvos-simulator
        // > - watchos-simulator
        // > - visionos-simulator
        // > - xros-simulator
        // > - driverkit
        let platform_name = match (target_os, target_env) {
            (os, Env::Unspecified) => os.desc(),
            (Os::IOs, Env::MacAbi) => "mac-catalyst",
            (Os::IOs, Env::Sim) => "ios-simulator",
            (Os::TvOs, Env::Sim) => "tvos-simulator",
            (Os::WatchOs, Env::Sim) => "watchos-simulator",
            (Os::VisionOs, Env::Sim) => "visionos-simulator",
            // tRust: invariant: structural invariant — linker configuration constrains valid options at this point
            _ => bug!("invalid OS/env combination for Apple target: {target_os}, {target_env}"),
        };

        let min_version = sess.apple_deployment_target().fmt_full().to_string();

        // The SDK version is used at runtime when compiling with a newer SDK / version of Xcode:
        // - By dyld to give extra warnings and errors, see e.g.:
        //   <https://github.com/apple-oss-distributions/dyld/blob/dyld-1165.3/common/MachOFile.cpp#L3029>
        //   <https://github.com/apple-oss-distributions/dyld/blob/dyld-1165.3/common/MachOFile.cpp#L3738-L3857>
        // - By system frameworks to change certain behaviour. For example, the default value of
        //   `-[NSView wantsBestResolutionOpenGLSurface]` is `YES` when the SDK version is >= 10.15.
        //   <https://developer.apple.com/documentation/appkit/nsview/1414938-wantsbestresolutionopenglsurface?language=objc>
        //
        // We do not currently know the actual SDK version though, so we have a few options:
        // 1. Use the minimum version supported by rustc.
        // 2. Use the same as the deployment target.
        // 3. Use an arbitrary recent version.
        // 4. Omit the version.
        //
        // The first option is too low / too conservative, and means that users will not get the
        // same behaviour from a binary compiled with rustc as with one compiled by clang.
        //
        // The second option is similarly conservative, and also wrong since if the user specified a
        // higher deployment target than the SDK they're compiling/linking with, the runtime might
        // make invalid assumptions about the capabilities of the binary.
        //
        // The third option requires that `rustc` is periodically kept up to date with Apple's SDK
        // version, and is also wrong for similar reasons as above.
        //
        // The fourth option is bad because while `ld`, `otool`, `vtool` and such understand it to
        // mean "absent" or `n/a`, dyld doesn't actually understand it, and will end up interpreting
        // it as 0.0, which is again too low/conservative.
        //
        // Currently, we lie about the SDK version, and choose the second option.
        //
        // NOTE(madsmtm): SDK version could be parsed from SDK root for accuracy.
        // <https://github.com/rust-lang/rust/issues/129432>
        let sdk_version = &*min_version;

        // From the man page for ld64 (`man ld`):
        // > This is set to indicate the platform, oldest supported version of
        // > that platform that output is to be used on, and the SDK that the
        // > output was built against.
        //
        // Like with `-arch`, the linker can figure out the platform versions
        // itself from the binaries being linked, but to be safe, we specify
        // the desired versions here explicitly.
        cmd.link_args(&["-platform_version", platform_name, &*min_version, sdk_version]);
    } else {
        // cc == Cc::Yes
        //
        // We'd _like_ to use `-target` everywhere, since that can uniquely
        // communicate all the required details except for the SDK version
        // (which is read by Clang itself from the SDKROOT), but that doesn't
        // work on GCC, and since we don't know whether the `cc` compiler is
        // Clang, GCC, or something else, we fall back to other options that
        // also work on GCC when compiling for macOS.
        //
        // Targets other than macOS are ill-supported by GCC (it doesn't even
        // support e.g. `-miphoneos-version-min`), so in those cases we can
        // fairly safely use `-target`. See also the following, where it is
        // made explicit that the recommendation by LLVM developers is to use
        // `-target`: <https://github.com/llvm/llvm-project/issues/88271>
        if *target_os == Os::MacOs {
            // `-arch` communicates the architecture.
            //
            // CC forwards the `-arch` to the linker, so we use the same value
            // here intentionally.
            cmd.cc_args(&["-arch", ld64_arch]);

            // The presence of `-mmacosx-version-min` makes CC default to
            // macOS, and it sets the deployment target.
            let version = sess.apple_deployment_target().fmt_full();
            // Intentionally pass this as a single argument, Clang doesn't
            // seem to like it otherwise.
            cmd.cc_arg(&format!("-mmacosx-version-min={version}"));

            // macOS has no environment, so with these two, we've told CC the
            // four desired parameters.
            //
            // We avoid `-m32`/`-m64`, as this is already encoded by `-arch`.
        } else {
            cmd.cc_args(&["-target", &versioned_llvm_target(sess)]);
        }
    }
}

pub(super) fn add_apple_sdk(cmd: &mut dyn Linker, sess: &Session, flavor: LinkerFlavor) -> Option<PathBuf> {
    if !sess.target.is_like_darwin {
        return None;
    }
    let LinkerFlavor::Darwin(cc, _) = flavor else {
        return None;
    };

    // The default compiler driver on macOS is at `/usr/bin/cc`. This is a trampoline binary that
    // effectively invokes `xcrun cc` internally to look up both the compiler binary and the SDK
    // root from the current Xcode installation. When cross-compiling, when `rustc` is invoked
    // inside Xcode, or when invoking the linker directly, this default logic is unsuitable, so
    // instead we invoke `xcrun` manually.
    //
    // (Note that this doesn't mean we get a duplicate lookup here - passing `SDKROOT` below will
    // cause the trampoline binary to skip looking up the SDK itself).
    let sdkroot = sess.time("get_apple_sdk_root", || get_apple_sdk_root(sess))?;

    if cc == Cc::Yes {
        // There are a few options to pass the SDK root when linking with a C/C++ compiler:
        // - The `--sysroot` flag.
        // - The `-isysroot` flag.
        // - The `SDKROOT` environment variable.
        //
        // `--sysroot` isn't actually enough to get Clang to treat it as a platform SDK, you need
        // to specify `-isysroot`. This is admittedly a bit strange, as on most targets `-isysroot`
        // only applies to include header files, but on Apple targets it also applies to libraries
        // and frameworks.
        //
        // This leaves the choice between `-isysroot` and `SDKROOT`. Both are supported by Clang and
        // GCC, though they may not be supported by all compiler drivers. We choose `SDKROOT`,
        // primarily because that is the same interface that is used when invoking the tool under
        // `xcrun -sdk macosx $tool`.
        //
        // In that sense, if a given compiler driver does not support `SDKROOT`, the blame is fairly
        // clearly in the tool in question, since they also don't support being run under `xcrun`.
        //
        // Additionally, `SDKROOT` is an environment variable and thus optional. It also has lower
        // precedence than `-isysroot`, so a custom compiler driver that does not support it and
        // instead figures out the SDK on their own can easily do so by using `-isysroot`.
        //
        // (This in particular affects Clang built with the `DEFAULT_SYSROOT` CMake flag, such as
        // the one provided by some versions of Homebrew's `llvm` package. Those will end up
        // ignoring the value we set here, and instead use their built-in sysroot).
        cmd.cmd().env("SDKROOT", &sdkroot);
    } else {
        // When invoking the linker directly, we use the `-syslibroot` parameter. `SDKROOT` is not
        // read by the linker, so it's really the only option.
        //
        // This is also what Clang does.
        cmd.link_arg("-syslibroot");
        cmd.link_arg(&sdkroot);
    }

    Some(sdkroot)
}

fn get_apple_sdk_root(sess: &Session) -> Option<PathBuf> {
    if let Ok(sdkroot) = env::var("SDKROOT") {
        let p = PathBuf::from(&sdkroot);

        // Ignore invalid SDKs, similar to what clang does:
        // https://github.com/llvm/llvm-project/blob/llvmorg-19.1.6/clang/lib/Driver/ToolChains/Darwin.cpp#L2212-L2229
        //
        // NOTE: Things are complicated here by the fact that `rustc` can be run by Cargo to compile
        // build scripts and proc-macros for the host, and thus we need to ignore SDKROOT if it's
        // clearly set for the wrong platform.
        //
        // NOTE(madsmtm): Could read SDKSettings.json like Clang for more robust SDK detection.
        match &*apple::sdk_name(&sess.target).to_lowercase() {
            "appletvos"
                if sdkroot.contains("TVSimulator.platform")
                    || sdkroot.contains("MacOSX.platform") => {}
            "appletvsimulator"
                if sdkroot.contains("TVOS.platform") || sdkroot.contains("MacOSX.platform") => {}
            "iphoneos"
                if sdkroot.contains("iPhoneSimulator.platform")
                    || sdkroot.contains("MacOSX.platform") => {}
            "iphonesimulator"
                if sdkroot.contains("iPhoneOS.platform") || sdkroot.contains("MacOSX.platform") => {
            }
            "macosx"
                if sdkroot.contains("iPhoneOS.platform")
                    || sdkroot.contains("iPhoneSimulator.platform")
                    || sdkroot.contains("AppleTVOS.platform")
                    || sdkroot.contains("AppleTVSimulator.platform")
                    || sdkroot.contains("WatchOS.platform")
                    || sdkroot.contains("WatchSimulator.platform")
                    || sdkroot.contains("XROS.platform")
                    || sdkroot.contains("XRSimulator.platform") => {}
            "watchos"
                if sdkroot.contains("WatchSimulator.platform")
                    || sdkroot.contains("MacOSX.platform") => {}
            "watchsimulator"
                if sdkroot.contains("WatchOS.platform") || sdkroot.contains("MacOSX.platform") => {}
            "xros"
                if sdkroot.contains("XRSimulator.platform")
                    || sdkroot.contains("MacOSX.platform") => {}
            "xrsimulator"
                if sdkroot.contains("XROS.platform") || sdkroot.contains("MacOSX.platform") => {}
            // Ignore `SDKROOT` if it's not a valid path.
            _ if !p.is_absolute() || p == Path::new("/") || !p.exists() => {}
            _ => return Some(p),
        }
    }

    apple::get_sdk_root(sess)
}
