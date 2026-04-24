#![doc = include_str!("../README.md")]

mod checksum;
mod manifest;
mod versions;

use std::collections::{BTreeMap, HashSet};
use std::path::{Path, PathBuf};
use std::{env, fs};

use crate::checksum::Checksums;
use crate::manifest::{Component, Manifest, Package, Rename, Target};
use crate::versions::{PkgType, Versions};

include!(concat!(env!("OUT_DIR"), "/targets.rs"));

/// This allows the manifest to contain rust-docs and rustc-docs for hosts
/// that don't build certain docs.
///
/// Tuples of `(host_partial, host_instead)`. If the host does not have the
/// corresponding docs component available, then if the host name contains
/// `host_partial`, it will use the docs from `host_instead` instead.
///
/// The order here matters, more specific entries should be first.
static DOCS_FALLBACK: &[(&str, &str)] = &[
    ("-apple-", "aarch64-apple-darwin"),
    ("aarch64", "aarch64-unknown-linux-gnu"),
    ("arm-", "aarch64-unknown-linux-gnu"),
    ("", "x86_64-unknown-linux-gnu"),
];

static PKG_INSTALLERS: &[&str] = &["x86_64-apple-darwin", "aarch64-apple-darwin"];

fn is_nightly_only(pkg: &PkgType) -> bool {
    match pkg {
        PkgType::Miri
        | PkgType::JsonDocs
        | PkgType::RustcCodegenCranelift
        | PkgType::RustcCodegenGcc
        | PkgType::Gcc { .. } => true,
        _ => false,
    }
}

macro_rules! t {
    ($e:expr) => {
        match $e {
            Ok(e) => e,
            Err(e) => panic!("{} failed with {}", stringify!($e), e),
        }
    };
    ($e:expr, $extra:expr) => {
        match $e {
            Ok(e) => e,
            Err(e) => panic!("{} failed with {}: {}", stringify!($e), e, $extra),
        }
    };
}

struct Builder {
    versions: Versions,
    checksums: Checksums,
    shipped_files: HashSet<String>,

    input: PathBuf,
    output: PathBuf,
    s3_address: String,
    date: String,
}

fn main() {
    let num_threads = if let Some(num) = env::var_os("BUILD_MANIFEST_NUM_THREADS") {
        num.to_str().unwrap().parse().expect("invalid number for BUILD_MANIFEST_NUM_THREADS")
    } else {
        std::thread::available_parallelism().map_or(1, std::num::NonZero::get)
    };
    rayon::ThreadPoolBuilder::new()
        .num_threads(num_threads)
        .build_global()
        .expect("failed to initialize Rayon");

    let mut args = env::args().skip(1);
    let input = PathBuf::from(args.next().unwrap());
    let output = PathBuf::from(args.next().unwrap());
    let date = args.next().unwrap();
    let s3_address = args.next().unwrap();
    let channel = args.next().unwrap();

    Builder {
        versions: Versions::new(&channel, &input).unwrap(),
        checksums: t!(Checksums::new()),
        shipped_files: HashSet::new(),

        input,
        output,
        s3_address,
        date,
    }
    .build();
}

impl Builder {
    fn build(&mut self) {
        let manifest = self.build_manifest();

        let channel = self.versions.channel().to_string();
        self.write_channel_files(&channel, &manifest);
        if channel == "stable" {
            // channel-rust-1.XX.YY.toml
            let rust_version = self.versions.rustc_version().to_string();
            self.write_channel_files(&rust_version, &manifest);

            // channel-rust-1.XX.toml
            let major_minor = rust_version.split('.').take(2).collect::<Vec<_>>().join(".");
            self.write_channel_files(&major_minor, &manifest);
        } else if channel == "beta" {
            // channel-rust-1.XX.YY-beta.Z.toml
            let rust_version = self
                .versions
                .version(&PkgType::Rust)
                .expect("missing Rust tarball")
                .version
                .expect("missing Rust version")
                .split(' ')
                .next()
                .unwrap()
                .to_string();
            self.write_channel_files(&rust_version, &manifest);

            // channel-rust-1.XX.YY-beta.toml
            let major_minor_patch_beta =
                rust_version.split('.').take(3).collect::<Vec<_>>().join(".");
            self.write_channel_files(&major_minor_patch_beta, &manifest);

            // channel-rust-1.XX-beta.toml
            let major_minor_beta =
                format!("{}-beta", rust_version.split('.').take(2).collect::<Vec<_>>().join("."));
            self.write_channel_files(&major_minor_beta, &manifest);
        }

        if let Some(path) = std::env::var_os("BUILD_MANIFEST_SHIPPED_FILES_PATH") {
            self.write_shipped_files(&Path::new(&path));
        }

        t!(self.checksums.store_cache());
    }

    fn build_manifest(&mut self) -> Manifest {
        let mut manifest = Manifest {
            manifest_version: "2".to_string(),
            date: self.date.to_string(),
            pkg: BTreeMap::new(),
            artifacts: BTreeMap::new(),
            renames: BTreeMap::new(),
            profiles: BTreeMap::new(),
        };
        self.add_packages_to(&mut manifest);
        self.add_artifacts_to(&mut manifest);
        self.add_profiles_to(&mut manifest);
        self.add_renames_to(&mut manifest);
        manifest.pkg.insert("rust".to_string(), self.rust_package(&manifest));

        self.checksums.fill_missing_checksums(&mut manifest);

        manifest
    }

    fn add_packages_to(&mut self, manifest: &mut Manifest) {
        for pkg in &PkgType::all() {
            self.package(pkg, &mut manifest.pkg);
        }
    }

    fn add_artifacts_to(&mut self, manifest: &mut Manifest) {
        manifest.add_artifact("source-code", |artifact| {
            let tarball = self.versions.tarball_name(&PkgType::Rustc, "src").unwrap();
            artifact.add_tarball(self, "*", &tarball);
        });

        manifest.add_artifact("installer-msi", |artifact| {
            for target in MSI_INSTALLERS {
                let msi = self.versions.archive_name(&PkgType::Rust, target, "msi").unwrap();
                artifact.add_file(self, target, &msi);
            }
        });

        manifest.add_artifact("installer-pkg", |artifact| {
            for target in PKG_INSTALLERS {
                let pkg = self.versions.archive_name(&PkgType::Rust, target, "pkg").unwrap();
                artifact.add_file(self, target, &pkg);
            }
        });
    }

    fn add_profiles_to(&mut self, manifest: &mut Manifest) {
        use PkgType::*;

        let mut profile = |name, pkgs: &_| self.profile(name, &mut manifest.profiles, pkgs);

        // Use a Vec here to make sure we don't exclude any components in an earlier profile.
        let minimal = vec![Rustc, Cargo, RustStd, RustMingw];
        profile("minimal", &minimal);

        let mut default = minimal;
        default.extend([HtmlDocs, Rustfmt, Clippy, CargoTrust, RustAnalyzer, RustSrc, LlvmTools]);
        profile("default", &default);

        // NOTE: this profile is effectively deprecated; do not add new components to it.
        let mut complete = default;
        complete.extend([RustAnalysis, Miri, RustcCodegenCranelift]);
        profile("complete", &complete);

        // The compiler libraries are not stable for end users, and they're also huge, so we only
        // `rustc-dev` for nightly users, and only in the "complete" profile. It's still possible
        // for users to install the additional component manually, if needed.
        if self.versions.channel() == "nightly" {
            self.extend_profile("complete", &mut manifest.profiles, &[RustcDev]);
            // Do not include the rustc-docs component for now, as it causes
            // conflicts with the rust-docs component when installed. See
            // #75833.
            // self.extend_profile("complete", &mut manifest.profiles, &["rustc-docs"]);
        }
    }

    fn add_renames_to(&self, manifest: &mut Manifest) {
        let mut rename = |from: &str, to: &str| {
            manifest.renames.insert(from.to_owned(), Rename { to: to.to_owned() })
        };
        for pkg in PkgType::all() {
            if pkg.is_preview() {
                rename(&pkg.tarball_component_name(), &pkg.manifest_component_name());
            }
        }
    }

    fn rust_package(&mut self, manifest: &Manifest) -> Package {
        let version_info = self.versions.version(&PkgType::Rust).expect("missing Rust tarball");
        let mut pkg = Package {
            version: version_info.version.expect("missing Rust version"),
            git_commit_hash: version_info.git_commit,
            target: BTreeMap::new(),
        };
        for host in HOSTS {
            if let Some(target) = self.target_host_combination(host, &manifest) {
                pkg.target.insert(host.to_string(), target);
            } else {
                pkg.target.insert(host.to_string(), Target::unavailable());
                continue;
            }
        }
        pkg
    }

    fn target_host_combination(&mut self, host: &str, manifest: &Manifest) -> Option<Target> {
        let filename = self.versions.tarball_name(&PkgType::Rust, host).unwrap();

        let mut target = Target::from_compressed_tar(self, &filename);
        if !target.available {
            return None;
        }

        let mut components = Vec::new();
        let mut extensions = Vec::new();

        let host_component = |pkg: &_| Component::from_pkg(pkg, host);

        for pkg in &PkgType::all() {
            match pkg {
                // rustc/rust-std/cargo/docs are all required
                PkgType::Rustc | PkgType::Cargo | PkgType::HtmlDocs => {
                    components.push(host_component(pkg));
                }
                PkgType::RustStd => {
                    components.push(host_component(pkg));
                    extensions.extend(
                        TARGETS
                            .iter()
                            .filter(|&&target| target != host)
                            .map(|target| Component::from_pkg(pkg, target)),
                    );
                }
                // so is rust-mingw if it's available for the target
                PkgType::RustMingw => {
                    if host.contains("pc-windows-gnu") {
                        components.push(host_component(pkg));
                        extensions.extend(
                            TARGETS
                                .iter()
                                .filter(|&&target| {
                                    target.contains("pc-windows-gnu") && target != host
                                })
                                .map(|target| Component::from_pkg(pkg, target)),
                        );
                    }
                }
                // Tools are always present in the manifest,
                // but might be marked as unavailable if they weren't built.
                PkgType::Clippy
                | PkgType::CargoTrust
                | PkgType::Miri
                | PkgType::RustAnalyzer
                | PkgType::Rustfmt
                | PkgType::LlvmTools
                | PkgType::RustAnalysis
                | PkgType::JsonDocs
                | PkgType::RustcDocs
                | PkgType::RustcCodegenCranelift
                | PkgType::RustcCodegenGcc
                | PkgType::Gcc { .. }
                | PkgType::LlvmBitcodeLinker => {
                    extensions.push(host_component(pkg));
                }
                PkgType::RustcDev => {
                    extensions.extend(HOSTS.iter().map(|target| Component::from_pkg(pkg, target)));
                }
                PkgType::RustSrc => {
                    extensions.push(Component::from_pkg(pkg, "*"));
                }
                PkgType::Rust => {}
                // NOTE: this is intentional, these artifacts aren't intended to be used with rustup
                PkgType::ReproducibleArtifacts => {}
            }
        }

        // If the components/extensions don't actually exist for this
        // particular host/target combination then nix it entirely from our
        // lists.
        let has_component = |c: &Component| {
            if c.target == "*" {
                return true;
            }
            let pkg = match manifest.pkg.get(&c.pkg) {
                Some(p) => p,
                None => return false,
            };
            pkg.target.contains_key(&c.target)
        };
        extensions.retain(&has_component);
        components.retain(&has_component);

        target.components = Some(components);
        target.extensions = Some(extensions);
        Some(target)
    }

    fn profile(
        &mut self,
        profile_name: &str,
        dst: &mut BTreeMap<String, Vec<String>>,
        pkgs: &[PkgType],
    ) {
        dst.insert(
            profile_name.to_owned(),
            pkgs.iter().map(|s| s.manifest_component_name()).collect(),
        );
    }

    fn extend_profile(
        &mut self,
        profile_name: &str,
        dst: &mut BTreeMap<String, Vec<String>>,
        pkgs: &[PkgType],
    ) {
        dst.get_mut(profile_name)
            .expect("existing profile")
            .extend(pkgs.iter().map(|s| s.manifest_component_name()));
    }

    fn package(&mut self, pkg: &PkgType, dst: &mut BTreeMap<String, Package>) {
        if *pkg == PkgType::Rust {
            // This is handled specially by `rust_package` later.
            // Order is important, so don't call `rust_package` here.
            return;
        }

        let fallback = if pkg.use_docs_fallback() { DOCS_FALLBACK } else { &[] };
        let version_info = self.versions.version(&pkg).expect("failed to load package version");
        let mut is_present = version_info.present;

        // Never ship nightly-only components for other trains.
        if self.versions.channel() != "nightly" && is_nightly_only(&pkg) {
            is_present = false; // Pretend the component is entirely missing.
        }

        macro_rules! tarball_name {
            ($target_name:expr) => {
                self.versions.tarball_name(pkg, $target_name).unwrap()
            };
        }
        let mut target_from_compressed_tar = |target_name| {
            let target = Target::from_compressed_tar(self, &tarball_name!(target_name));
            if target.available {
                return target;
            }
            for (substr, fallback_target) in fallback {
                if target_name.contains(substr) {
                    let t = Target::from_compressed_tar(self, &tarball_name!(fallback_target));
                    // Fallbacks should typically be available on 'production' builds
                    // but may not be available for try builds, which only build one target by
                    // default. It is also possible that `rust-docs` and `rustc-docs` differ in
                    // availability per target. Thus, we take the first available fallback we can
                    // find.
                    if !t.available {
                        eprintln!(
                            "{:?} not available for fallback",
                            tarball_name!(fallback_target)
                        );
                        continue;
                    }
                    return t;
                }
            }
            Target::unavailable()
        };

        let targets = pkg
            .targets()
            .iter()
            .map(|name| {
                let target = if is_present {
                    target_from_compressed_tar(name)
                } else {
                    // If the component is not present for this build add it anyway but mark it as
                    // unavailable -- this way rustup won't allow upgrades without --force
                    Target::unavailable()
                };
                (name.to_string(), target)
            })
            .collect();

        dst.insert(
            pkg.manifest_component_name(),
            Package {
                version: version_info.version.unwrap_or_default(),
                git_commit_hash: version_info.git_commit,
                target: targets,
            },
        );
    }

    fn url(&self, path: &Path) -> String {
        let file_name = path.file_name().unwrap().to_str().unwrap();
        format!("{}/{}/{}", self.s3_address, self.date, file_name)
    }

    fn write_channel_files(&mut self, channel_name: &str, manifest: &Manifest) {
        self.write(&toml::to_string(&manifest).unwrap(), channel_name, ".toml");
        self.write(&manifest.date, channel_name, "-date.txt");
        self.write(
            manifest.pkg["rust"].git_commit_hash.as_ref().unwrap(),
            channel_name,
            "-git-commit-hash.txt",
        );
    }

    fn write(&mut self, contents: &str, channel_name: &str, suffix: &str) {
        let name = format!("channel-rust-{}{}", channel_name, suffix);
        self.shipped_files.insert(name.clone());

        let dst = self.output.join(name);
        t!(fs::write(&dst, contents), format!("failed to create manifest {}", dst.display()));
    }

    fn write_shipped_files(&self, path: &Path) {
        let mut files = self.shipped_files.iter().map(|s| s.as_str()).collect::<Vec<_>>();
        files.sort();
        let content = format!("{}\n", files.join("\n"));

        t!(std::fs::write(path, content.as_bytes()));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn empty_manifest() -> Manifest {
        Manifest {
            manifest_version: "2".to_string(),
            date: "2026-04-23".to_string(),
            pkg: BTreeMap::new(),
            artifacts: BTreeMap::new(),
            renames: BTreeMap::new(),
            profiles: BTreeMap::new(),
        }
    }

    fn test_builder(input: PathBuf) -> Builder {
        Builder {
            versions: Versions::new("nightly", &input).unwrap(),
            checksums: Checksums::new().unwrap(),
            shipped_files: HashSet::new(),
            input: input.clone(),
            output: input,
            s3_address: "https://static.example.test/dist".to_string(),
            date: "2026-04-23".to_string(),
        }
    }

    fn temp_dist_dir(test_name: &str) -> PathBuf {
        let nanos = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let dir = env::temp_dir()
            .join(format!("build-manifest-{test_name}-{}-{nanos}", std::process::id()));
        fs::create_dir(&dir).unwrap();
        dir
    }

    fn package_available_for(target: &str) -> Package {
        Package {
            version: String::new(),
            git_commit_hash: None,
            target: BTreeMap::from([(
                target.to_string(),
                Target { available: true, ..Target::default() },
            )]),
        }
    }

    fn has_component(components: &[Component], pkg: &str, target: &str) -> bool {
        components.iter().any(|component| component.pkg == pkg && component.target == target)
    }

    fn assert_profile_has_no_duplicates(name: &str, components: &[String]) {
        let mut seen = HashSet::new();
        for component in components {
            assert!(
                seen.insert(component),
                "{name} profile contains duplicate component {component}: {components:?}"
            );
        }
    }

    #[test]
    fn default_profile_contains_daily_driver_tools() {
        let mut builder = test_builder(PathBuf::new());
        let mut manifest = empty_manifest();

        builder.add_profiles_to(&mut manifest);

        let default = manifest.profiles.get("default").expect("default profile");
        assert_profile_has_no_duplicates("default", default);
        for component in [
            "rustc",
            "cargo",
            "rust-std",
            "rust-docs",
            "cargo-trust",
            "rustfmt-preview",
            "clippy-preview",
            "rust-analyzer-preview",
            "rust-src",
            "llvm-tools-preview",
        ] {
            assert!(
                default.iter().any(|actual| actual == component),
                "default profile is missing {component}; components: {default:?}"
            );
        }

        let complete = manifest.profiles.get("complete").expect("complete profile");
        assert_profile_has_no_duplicates("complete", complete);
    }

    #[test]
    fn rust_package_host_extensions_contain_cargo_trust() {
        let host = HOSTS[0];
        let input = temp_dist_dir("cargo-trust-extension");
        let mut builder = test_builder(input.clone());
        let rust_tarball = builder.versions.tarball_name(&PkgType::Rust, host).unwrap();
        fs::write(input.join(rust_tarball), b"").unwrap();

        let mut manifest = empty_manifest();
        manifest.pkg.insert("cargo-trust".to_string(), package_available_for(host));

        let target = builder
            .target_host_combination(host, &manifest)
            .expect("rust package target is available");
        let extensions = target.extensions.expect("rust package extensions");

        assert!(
            has_component(&extensions, "cargo-trust", host),
            "rust package extensions for {host}: {:?}",
            extensions
                .iter()
                .map(|component| (&component.pkg, &component.target))
                .collect::<Vec<_>>()
        );

        fs::remove_dir_all(input).unwrap();
    }
}
