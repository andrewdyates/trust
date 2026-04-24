use std::collections::BTreeMap;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};

use sha2::Digest;

use super::EditorKind;
use crate::utils::helpers::hex_encode;
#[test]
fn check_matching_settings_hash() {
    // Needs to be a btree so we serialize in a deterministic order.
    let mut mismatched = BTreeMap::new();

    for editor in EditorKind::ALL {
        let mut hasher = sha2::Sha256::new();
        hasher.update(&editor.settings_template());
        let actual = hex_encode(hasher.finalize().as_slice());
        let expected = *editor.hashes().last().unwrap();

        if expected != actual {
            mismatched.insert(editor, (expected, actual));
        }
    }

    if mismatched.is_empty() {
        return;
    }

    if option_env!("INSTA_UPDATE").is_some_and(|s| s != "0") {
        let mut updated = super::PARSED_HASHES.clone();
        for (editor, (_, actual)) in &mismatched {
            *updated.get_mut(editor).unwrap().last_mut().unwrap() = actual;
        }
        let hash_path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("src/core/build_steps/setup/hashes.json");
        let mut hash_file = File::create(hash_path).unwrap();
        serde_json::to_writer_pretty(&mut hash_file, &updated).unwrap();
        hash_file.write_all(b"\n").unwrap();
    } else {
        for (editor, (expected, actual)) in &mismatched {
            eprintln!("recorded hash did not match actual hash: {expected} != {actual}");
            eprintln!(
                "Run `x test --bless -- hash`, or manually update `setup/hashes.json` with the new hash of `{actual}` for `EditorKind::{editor:?}`"
            );
        }
        panic!("mismatched hashes");
    }
}

#[test]
fn trust_toolchain_name_matches_repo_workflow() {
    assert_eq!(super::local_toolchain_name(), "trust");
}

#[test]
fn toolchain_list_entry_name_requires_exact_match() {
    assert_eq!(super::toolchain_list_entry_name("trust /tmp/stage1"), Some("trust"));
    assert_eq!(
        super::toolchain_list_entry_name("trust-experimental /tmp/stage1"),
        Some("trust-experimental")
    );
    assert_ne!(super::toolchain_list_entry_name("stage1 /tmp/stage1"), Some("trust"));
}

#[test]
fn toolchain_list_entry_path_must_match_stage_path() {
    let stage_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src").join("core").join("build_steps");
    let line = format!("trust {}", stage_path.display());

    assert!(super::toolchain_list_entry_matches_path(&line, &stage_path));
    assert!(!super::toolchain_list_entry_matches_path(&line, Path::new("/tmp/not-stage1")));
}

#[test]
fn toolchain_list_entry_path_handles_status_prefixes() {
    let stage_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src").join("core").join("build_steps");
    let line = format!("trust (active, default) {}", stage_path.display());

    assert_eq!(super::toolchain_list_entry_path(&line), Some(stage_path.to_str().unwrap()));
}

#[test]
fn stage_path_uses_host_symlink_under_configured_out_dir() {
    let out = Path::new("/tmp/trust bootstrap out");
    assert_eq!(super::stage_path_for(out, 1), out.join("host").join("stage1"));
}

#[test]
fn stage_path_uses_top_stage_when_requested() {
    let out = Path::new("/tmp/trust bootstrap out");
    assert_eq!(super::stage_path_for(out, 2), out.join("host").join("stage2"));
}

#[test]
fn stage_path_clamps_stage_zero_to_stage_one() {
    let out = Path::new("/tmp/trust bootstrap out");
    assert_eq!(super::stage_path_for(out, 0), out.join("host").join("stage1"));
}
