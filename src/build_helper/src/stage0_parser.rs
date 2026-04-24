use std::collections::BTreeMap;

#[derive(Default, Clone)]
pub struct Stage0 {
    pub compiler: VersionMetadata,
    pub rustfmt: Option<VersionMetadata>,
    pub config: Stage0Config,
    pub checksums_sha256: BTreeMap<String, String>,
}

#[derive(Default, Clone)]
pub struct VersionMetadata {
    pub channel_manifest_hash: String,
    pub git_commit_hash: String,
    pub date: String,
    pub version: String,
}

#[derive(Default, Clone)]
pub struct Stage0Config {
    pub dist_server: String,
    pub artifacts_server: String,
    pub artifacts_with_llvm_assertions_server: String,
    pub git_merge_commit_email: String,
    pub nightly_branch: String,
    pub compiler_dist_channel: String,
    pub rustfmt_dist_channel: String,
}

pub fn parse_stage0_file() -> Stage0 {
    parse_stage0_content(include_str!("../../stage0"))
}

fn parse_stage0_content(stage0_content: &str) -> Stage0 {
    let mut stage0 = Stage0::default();
    for line in stage0_content.lines() {
        let line = line.trim();

        if line.is_empty() {
            continue;
        }

        // Ignore comments
        if line.starts_with('#') {
            continue;
        }

        let (key, value) = line.split_once('=').unwrap();

        match key {
            "dist_server" => stage0.config.dist_server = value.to_owned(),
            "artifacts_server" => stage0.config.artifacts_server = value.to_owned(),
            "artifacts_with_llvm_assertions_server" => {
                stage0.config.artifacts_with_llvm_assertions_server = value.to_owned()
            }
            "git_merge_commit_email" => stage0.config.git_merge_commit_email = value.to_owned(),
            "nightly_branch" => stage0.config.nightly_branch = value.to_owned(),
            "compiler_dist_channel" => stage0.config.compiler_dist_channel = value.to_owned(),
            "rustfmt_dist_channel" => stage0.config.rustfmt_dist_channel = value.to_owned(),

            "compiler_channel_manifest_hash" => {
                stage0.compiler.channel_manifest_hash = value.to_owned()
            }
            "compiler_git_commit_hash" => stage0.compiler.git_commit_hash = value.to_owned(),
            "compiler_date" => stage0.compiler.date = value.to_owned(),
            "compiler_version" => stage0.compiler.version = value.to_owned(),

            "rustfmt_channel_manifest_hash" => {
                stage0.rustfmt.get_or_insert(VersionMetadata::default()).channel_manifest_hash =
                    value.to_owned();
            }
            "rustfmt_git_commit_hash" => {
                stage0.rustfmt.get_or_insert(VersionMetadata::default()).git_commit_hash =
                    value.to_owned();
            }
            "rustfmt_date" => {
                stage0.rustfmt.get_or_insert(VersionMetadata::default()).date = value.to_owned();
            }
            "rustfmt_version" => {
                stage0.rustfmt.get_or_insert(VersionMetadata::default()).version = value.to_owned();
            }

            dist if dist.starts_with("dist") => {
                stage0.checksums_sha256.insert(key.to_owned(), value.to_owned());
            }

            unsupported => {
                println!("'{unsupported}' field is not supported.");
            }
        }
    }

    stage0
}

#[cfg(test)]
mod tests {
    use super::parse_stage0_content;

    #[test]
    fn parses_stage0_dist_channel_overrides() {
        let parsed = parse_stage0_content(
            r#"
dist_server=https://dist.example
artifacts_server=https://artifacts.example
artifacts_with_llvm_assertions_server=https://assertions.example
git_merge_commit_email=merge@example.com
nightly_branch=main
compiler_dist_channel=nightly
rustfmt_dist_channel=nightly
compiler_channel_manifest_hash=compiler-hash
compiler_git_commit_hash=compiler-git
compiler_date=2026-04-23
compiler_version=nightly
rustfmt_channel_manifest_hash=rustfmt-hash
rustfmt_git_commit_hash=rustfmt-git
rustfmt_date=2026-04-23
rustfmt_version=nightly
dist/2026-04-23/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz=deadbeef
"#,
        );

        assert_eq!(parsed.config.compiler_dist_channel, "nightly");
        assert_eq!(parsed.config.rustfmt_dist_channel, "nightly");
        assert_eq!(parsed.compiler.version, "nightly");
        assert_eq!(parsed.rustfmt.as_ref().unwrap().version, "nightly");
        assert_eq!(
            parsed
                .checksums_sha256
                .get("dist/2026-04-23/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz")
                .unwrap(),
            "deadbeef"
        );
    }

    #[test]
    fn leaves_dist_channel_overrides_empty_when_unspecified() {
        let parsed = parse_stage0_content(
            r#"
dist_server=https://dist.example
artifacts_server=https://artifacts.example
artifacts_with_llvm_assertions_server=https://assertions.example
git_merge_commit_email=merge@example.com
nightly_branch=main
compiler_channel_manifest_hash=compiler-hash
compiler_git_commit_hash=compiler-git
compiler_date=2026-04-23
compiler_version=beta
"#,
        );

        assert!(parsed.config.compiler_dist_channel.is_empty());
        assert!(parsed.config.rustfmt_dist_channel.is_empty());
    }
}
