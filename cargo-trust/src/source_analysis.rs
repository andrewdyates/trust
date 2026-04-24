// Lightweight source-level analysis for standalone verification mode.
//
// Parses Rust source files to extract function signatures and specification
// attributes (#[requires], #[ensures]) without requiring the full rustc MIR
// pipeline. Generates basic verification conditions for each function.
//
// This enables `cargo trust check --standalone` to produce a verification
// summary even when the built tRust compiler is not available.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::ffi::OsString;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Parsed source types
// ---------------------------------------------------------------------------

/// A function extracted from source-level parsing.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct ParsedFunction {
    pub(crate) name: String,
    pub(crate) file: PathBuf,
    pub(crate) line: usize,
    pub(crate) is_public: bool,
    pub(crate) is_unsafe: bool,
    pub(crate) has_requires: bool,
    pub(crate) has_ensures: bool,
    pub(crate) return_type: Option<String>,
    pub(crate) params: Vec<String>,
    /// Parameters with types: (name, type_string). Used by `cargo trust init`.
    pub(crate) typed_params: Vec<(String, String)>,
}

/// A basic verification condition generated from source analysis.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct StandaloneVc {
    pub(crate) function: String,
    pub(crate) file: PathBuf,
    pub(crate) kind: VcKind,
    pub(crate) description: String,
    pub(crate) outcome: StandaloneOutcome,
}

/// Kind of verification condition for source-level analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub(crate) enum VcKind {
    /// Function has a #[requires] spec that should be checked.
    PreconditionPresent,
    /// Function has a #[ensures] spec that should be checked.
    PostconditionPresent,
    /// Unsafe function detected -- needs safety audit.
    UnsafeFunction,
    /// Public function without specification.
    UnspecifiedPublicApi,
}

/// Outcome of a standalone VC -- note this is analysis-level, not solver-level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub(crate) enum StandaloneOutcome {
    /// Spec is present (positive signal).
    Proved,
    /// Something needs attention.
    Unknown,
    /// Problem detected.
    Failed,
}

// ---------------------------------------------------------------------------
// Source summary
// ---------------------------------------------------------------------------

/// Summary of standalone source analysis.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct SourceAnalysisSummary {
    pub(crate) files_analyzed: usize,
    pub(crate) functions_found: usize,
    pub(crate) public_functions: usize,
    pub(crate) unsafe_functions: usize,
    pub(crate) specified_functions: usize,
    pub(crate) total_vcs: usize,
    pub(crate) proved: usize,
    pub(crate) failed: usize,
    pub(crate) unknown: usize,
    pub(crate) functions: Vec<ParsedFunction>,
    pub(crate) vcs: Vec<StandaloneVc>,
}

// ---------------------------------------------------------------------------
// Source file discovery
// ---------------------------------------------------------------------------

/// Cargo manifest fields relevant to standalone target discovery.
#[derive(Debug, Default, Deserialize)]
struct CargoManifest {
    package: Option<ManifestPackage>,
    workspace: Option<ManifestWorkspace>,
    lib: Option<ManifestTarget>,
    #[serde(default)]
    bin: Vec<ManifestNamedTarget>,
}

#[derive(Debug, Default, Deserialize)]
struct ManifestPackage {
    #[serde(default)]
    autobins: Option<bool>,
}

#[derive(Debug, Default, Deserialize)]
struct ManifestWorkspace {
    #[serde(default)]
    members: Vec<String>,
    #[serde(default, rename = "default-members")]
    default_members: Vec<String>,
}

#[derive(Debug, Default, Deserialize)]
struct ManifestTarget {
    path: Option<PathBuf>,
}

#[derive(Debug, Default, Deserialize)]
struct ManifestNamedTarget {
    name: Option<String>,
    path: Option<PathBuf>,
}

/// Find all .rs source files in a crate directory or manifest path.
///
/// Standalone mode prefers Cargo manifest target discovery so it can honor
/// custom target paths, bin layouts, ancestor package roots, workspace member
/// manifests, and `--manifest-path` when `cargo-trust` is invoked from a
/// different working directory. If discovery fails, it falls back to scanning
/// `<root>/src` for compatibility.
pub(crate) fn find_source_files(crate_root: &Path) -> Vec<PathBuf> {
    if let Some(manifest_path) = resolve_manifest_path(crate_root) {
        let mut visited = BTreeSet::new();
        let manifest_files = collect_manifest_source_files(&manifest_path, &mut visited);
        if !manifest_files.is_empty() {
            return manifest_files;
        }
        if let Some(manifest_dir) = manifest_path.parent() {
            return legacy_src_scan(manifest_dir);
        }
    }
    legacy_src_scan(crate_root)
}

fn legacy_src_scan(crate_root: &Path) -> Vec<PathBuf> {
    let src_dir = crate_root.join("src");
    if !src_dir.is_dir() {
        return Vec::new();
    }
    collect_rs_files(&src_dir)
}

fn collect_rs_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(_) => return files,
    };
    for entry in entries {
        let entry = match entry {
            Ok(e) => e,
            Err(_) => continue,
        };
        let path = entry.path();
        if path.is_dir() {
            files.extend(collect_rs_files(&path));
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            files.push(path);
        }
    }
    files.sort();
    files
}

fn resolve_manifest_path(crate_root: &Path) -> Option<PathBuf> {
    if should_consult_process_args_for_manifest(crate_root) {
        if let Some(manifest_path) = manifest_path_from_process_args() {
            return Some(manifest_path);
        }
    }
    manifest_path_from_input(crate_root)
}

fn should_consult_process_args_for_manifest(crate_root: &Path) -> bool {
    if crate_root == Path::new(".") {
        return true;
    }
    std::env::current_dir().is_ok_and(|cwd| paths_equivalent(crate_root, &cwd))
}

fn paths_equivalent(left: &Path, right: &Path) -> bool {
    if left == right {
        return true;
    }
    match (std::fs::canonicalize(left), std::fs::canonicalize(right)) {
        (Ok(left), Ok(right)) => left == right,
        _ => false,
    }
}

fn manifest_path_from_process_args() -> Option<PathBuf> {
    let manifest_path = manifest_path_from_args(std::env::args_os())?;
    if manifest_path.is_absolute() {
        return Some(manifest_path);
    }
    std::env::current_dir().ok().map(|cwd| cwd.join(manifest_path))
}

fn manifest_path_from_args<I>(args: I) -> Option<PathBuf>
where
    I: IntoIterator<Item = OsString>,
{
    let mut args = args.into_iter();
    while let Some(arg) = args.next() {
        if arg == "--manifest-path" {
            let value = args.next()?;
            if !value.is_empty() {
                return Some(PathBuf::from(value));
            }
            continue;
        }

        if let Some(arg) = arg.to_str().and_then(|s| s.strip_prefix("--manifest-path=")) {
            if !arg.is_empty() {
                return Some(PathBuf::from(arg));
            }
        }
    }
    None
}

fn manifest_path_from_input(path: &Path) -> Option<PathBuf> {
    if path.is_file() {
        if path.file_name().is_some_and(|name| name == "Cargo.toml") {
            return Some(path.to_path_buf());
        }
        return path.parent().and_then(find_manifest_in_ancestors);
    }

    find_manifest_in_ancestors(path)
}

fn find_manifest_in_ancestors(dir: &Path) -> Option<PathBuf> {
    dir.ancestors().map(|ancestor| ancestor.join("Cargo.toml")).find(|path| path.is_file())
}

fn collect_manifest_source_files(
    manifest_path: &Path,
    visited_manifests: &mut BTreeSet<PathBuf>,
) -> Vec<PathBuf> {
    let manifest_key = canonicalize_or_self(manifest_path);
    if !visited_manifests.insert(manifest_key) {
        return Vec::new();
    }

    let manifest_dir = manifest_path.parent().unwrap_or_else(|| Path::new("."));
    let content = match std::fs::read_to_string(&manifest_path) {
        Ok(content) => content,
        Err(_) => return legacy_src_scan(manifest_dir),
    };
    let manifest = match toml::from_str::<CargoManifest>(&content) {
        Ok(manifest) => manifest,
        Err(_) => return legacy_src_scan(manifest_dir),
    };

    if manifest.package.is_some() || manifest.lib.is_some() || !manifest.bin.is_empty() {
        return collect_package_target_files(manifest_dir, &manifest);
    }

    if let Some(workspace) = manifest.workspace.as_ref() {
        return collect_workspace_member_files(manifest_dir, workspace, visited_manifests);
    }

    legacy_src_scan(manifest_dir)
}

fn collect_package_target_files(manifest_dir: &Path, manifest: &CargoManifest) -> Vec<PathBuf> {
    let mut files = BTreeSet::new();

    if let Some(lib) = manifest.lib.as_ref() {
        if let Some(path) = lib.path.as_ref() {
            push_target_file(&mut files, manifest_dir.join(path));
        } else {
            push_target_file(&mut files, manifest_dir.join("src/lib.rs"));
        }
    } else {
        push_target_file(&mut files, manifest_dir.join("src/lib.rs"));
    }

    for bin in &manifest.bin {
        if let Some(path) = bin.path.as_ref() {
            push_target_file(&mut files, manifest_dir.join(path));
        } else if let Some(name) = bin.name.as_deref() {
            push_named_bin_defaults(&mut files, manifest_dir, name);
        }
    }

    if manifest.package.as_ref().and_then(|package| package.autobins).unwrap_or(true) {
        push_target_file(&mut files, manifest_dir.join("src/main.rs"));
        push_auto_bin_targets(&mut files, &manifest_dir.join("src/bin"));
    }

    files.into_iter().collect()
}

fn push_target_file(files: &mut BTreeSet<PathBuf>, path: PathBuf) {
    if path.is_file() {
        if let Some(parent) = path.parent() {
            files.extend(collect_rs_files(parent));
        } else {
            files.insert(path);
        }
    }
}

fn push_named_bin_defaults(files: &mut BTreeSet<PathBuf>, manifest_dir: &Path, name: &str) {
    push_target_file(files, manifest_dir.join(format!("src/bin/{name}.rs")));
    push_target_file(files, manifest_dir.join(format!("src/bin/{name}/main.rs")));
}

fn push_auto_bin_targets(files: &mut BTreeSet<PathBuf>, src_bin_dir: &Path) {
    let entries = match std::fs::read_dir(src_bin_dir) {
        Ok(entries) => entries,
        Err(_) => return,
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_file() && path.extension().is_some_and(|ext| ext == "rs") {
            files.insert(path);
            continue;
        }
        if path.is_dir() {
            push_target_file(files, path.join("main.rs"));
        }
    }
}

fn collect_workspace_member_files(
    workspace_dir: &Path,
    workspace: &ManifestWorkspace,
    visited_manifests: &mut BTreeSet<PathBuf>,
) -> Vec<PathBuf> {
    let member_patterns = if workspace.default_members.is_empty() {
        &workspace.members
    } else {
        &workspace.default_members
    };
    let mut files = BTreeSet::new();

    for member_manifest in expand_workspace_member_manifests(workspace_dir, member_patterns) {
        files.extend(collect_manifest_source_files(&member_manifest, visited_manifests));
    }

    files.into_iter().collect()
}

fn expand_workspace_member_manifests(
    workspace_dir: &Path,
    member_patterns: &[String],
) -> Vec<PathBuf> {
    let mut manifests = BTreeSet::new();

    for pattern in member_patterns {
        for member_dir in expand_workspace_member_pattern(workspace_dir, pattern) {
            let manifest_path = if member_dir.file_name().is_some_and(|name| name == "Cargo.toml") {
                member_dir
            } else {
                member_dir.join("Cargo.toml")
            };
            if manifest_path.is_file() {
                manifests.insert(manifest_path);
            }
        }
    }

    manifests.into_iter().collect()
}

fn expand_workspace_member_pattern(workspace_dir: &Path, pattern: &str) -> Vec<PathBuf> {
    if !contains_wildcard(pattern) {
        return vec![workspace_dir.join(pattern)];
    }

    let normalized = pattern.replace('\\', "/");
    let components: Vec<&str> =
        normalized.split('/').filter(|component| !component.is_empty()).collect();
    let mut matches = Vec::new();
    expand_workspace_pattern_components(workspace_dir, &components, &mut matches);
    matches
}

fn expand_workspace_pattern_components(
    base: &Path,
    components: &[&str],
    matches: &mut Vec<PathBuf>,
) {
    if components.is_empty() {
        matches.push(base.to_path_buf());
        return;
    }

    let component = components[0];
    if component == "." {
        expand_workspace_pattern_components(base, &components[1..], matches);
        return;
    }

    if component == "**" {
        expand_workspace_pattern_components(base, &components[1..], matches);
        let entries = match std::fs::read_dir(base) {
            Ok(entries) => entries,
            Err(_) => return,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                expand_workspace_pattern_components(&path, components, matches);
            }
        }
        return;
    }

    if contains_wildcard(component) {
        let entries = match std::fs::read_dir(base) {
            Ok(entries) => entries,
            Err(_) => return,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if !path.is_dir() {
                continue;
            }
            let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
                continue;
            };
            if wildcard_matches(component, name) {
                expand_workspace_pattern_components(&path, &components[1..], matches);
            }
        }
        return;
    }

    let next = base.join(component);
    if next.is_dir() {
        expand_workspace_pattern_components(&next, &components[1..], matches);
    }
}

fn contains_wildcard(pattern: &str) -> bool {
    pattern.contains('*') || pattern.contains('?')
}

fn wildcard_matches(pattern: &str, value: &str) -> bool {
    let pattern: Vec<char> = pattern.chars().collect();
    let value: Vec<char> = value.chars().collect();
    let mut dp = vec![vec![false; value.len() + 1]; pattern.len() + 1];
    dp[0][0] = true;

    for i in 0..pattern.len() {
        match pattern[i] {
            '*' => {
                dp[i + 1][0] = dp[i][0];
                for j in 0..value.len() {
                    dp[i + 1][j + 1] = dp[i][j + 1] || dp[i + 1][j];
                }
            }
            '?' => {
                for j in 0..value.len() {
                    dp[i + 1][j + 1] = dp[i][j];
                }
            }
            ch => {
                for j in 0..value.len() {
                    dp[i + 1][j + 1] = dp[i][j] && ch == value[j];
                }
            }
        }
    }

    dp[pattern.len()][value.len()]
}

fn canonicalize_or_self(path: &Path) -> PathBuf {
    std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

// ---------------------------------------------------------------------------
// Function extraction
// ---------------------------------------------------------------------------

/// Parse a Rust source file and extract function signatures.
///
/// This is a lightweight line-by-line parser that finds `fn` declarations
/// and associated `#[requires]` / `#[ensures]` attributes. It does NOT
/// build an AST -- it uses pattern matching for speed and simplicity.
pub(crate) fn extract_functions(file: &Path) -> Vec<ParsedFunction> {
    let content = match std::fs::read_to_string(file) {
        Ok(c) => c,
        Err(_) => return Vec::new(),
    };
    extract_functions_from_source(&content, file)
}

/// Extract functions from source text (testable without filesystem).
pub(crate) fn extract_functions_from_source(source: &str, file: &Path) -> Vec<ParsedFunction> {
    let mut functions = Vec::new();
    let mut pending_requires = false;
    let mut pending_ensures = false;
    let mut in_block_comment = false;

    for (line_idx, line) in source.lines().enumerate() {
        let trimmed = line.trim();

        // Track block comments
        if in_block_comment {
            if trimmed.contains("*/") {
                in_block_comment = false;
            }
            continue;
        }
        if trimmed.starts_with("/*") {
            in_block_comment = true;
            if trimmed.contains("*/") {
                in_block_comment = false;
            }
            continue;
        }

        // Skip line comments
        if trimmed.starts_with("//") {
            continue;
        }

        // Detect spec attributes
        if let Some(kind) = contract_attr_kind(trimmed) {
            match kind {
                ContractAttrKind::Requires => pending_requires = true,
                ContractAttrKind::Ensures => pending_ensures = true,
            }
            continue;
        }

        // Skip other attributes (but preserve pending spec state)
        if trimmed.starts_with("#[") {
            continue;
        }

        // Look for function declarations
        if let Some(func) = try_parse_fn_line(trimmed, file, line_idx + 1) {
            let mut func = func;
            func.has_requires = pending_requires;
            func.has_ensures = pending_ensures;
            functions.push(func);
            pending_requires = false;
            pending_ensures = false;
        } else if !trimmed.is_empty() {
            // Non-attribute, non-fn line -- reset pending specs
            // (unless it's a visibility modifier that precedes fn)
            if !trimmed.starts_with("pub") {
                pending_requires = false;
                pending_ensures = false;
            }
        }
    }

    functions
}

#[derive(Clone, Copy)]
enum ContractAttrKind {
    Requires,
    Ensures,
}

fn contract_attr_kind(line: &str) -> Option<ContractAttrKind> {
    let inner = line.strip_prefix("#[")?.trim_start();
    let name_end = inner.find(['(', '=', ' ', ']']).unwrap_or(inner.len());
    let name = inner[..name_end].trim();
    let name = name.rsplit("::").next().unwrap_or(name);

    match name {
        "requires" | "contracts_requires" | "trust_requires" => Some(ContractAttrKind::Requires),
        "ensures" | "contracts_ensures" | "trust_ensures" => Some(ContractAttrKind::Ensures),
        _ => None,
    }
}

/// Try to parse a line as a function declaration.
fn try_parse_fn_line(line: &str, file: &Path, line_num: usize) -> Option<ParsedFunction> {
    // Patterns we recognize:
    //   fn name(...)
    //   pub fn name(...)
    //   pub(crate) fn name(...)
    //   pub(super) fn name(...)
    //   unsafe fn name(...)
    //   pub unsafe fn name(...)
    //   async fn name(...)
    //   pub async fn name(...)
    //   pub async unsafe fn name(...)
    //   const fn name(...)

    let mut rest = line;
    let mut is_public = false;
    let mut is_unsafe = false;

    // Strip visibility
    if rest.starts_with("pub") {
        is_public = true;
        rest = rest[3..].trim_start();
        // pub(crate), pub(super), etc.
        if rest.starts_with('(') {
            if let Some(close) = rest.find(')') {
                rest = rest[close + 1..].trim_start();
            }
        }
    }

    // Strip qualifiers: const, async, unsafe, extern
    loop {
        if let Some(after) = rest.strip_prefix("const ") {
            rest = after.trim_start();
        } else if let Some(after) = rest.strip_prefix("async ") {
            rest = after.trim_start();
        } else if let Some(after) = rest.strip_prefix("unsafe ") {
            is_unsafe = true;
            rest = after.trim_start();
        } else if let Some(after) = rest.strip_prefix("extern ") {
            rest = after.trim_start();
            // Skip optional ABI string: extern "C"
            if rest.starts_with('"') {
                if let Some(close) = rest[1..].find('"') {
                    rest = rest[close + 2..].trim_start();
                }
            }
        } else {
            break;
        }
    }

    // Must start with "fn "
    rest = rest.strip_prefix("fn ")?;
    rest = rest.trim_start();

    // Extract function name (up to `(` or `<`)
    let name_end = rest.find(|c: char| c == '(' || c == '<' || c.is_whitespace())?;
    let name = rest[..name_end].to_string();

    // Basic validation: name should be a valid identifier
    if name.is_empty() || !name.chars().next()?.is_alphanumeric() && name.chars().next()? != '_' {
        return None;
    }

    // Extract parameters (rough: everything between first ( and matching ))
    let params = extract_param_names(rest);
    let typed_params = extract_typed_params(rest);

    // Extract return type
    let return_type = extract_return_type(rest);

    Some(ParsedFunction {
        name,
        file: file.to_path_buf(),
        line: line_num,
        is_public,
        is_unsafe,
        has_requires: false,
        has_ensures: false,
        return_type,
        params,
        typed_params,
    })
}

/// Extract parameter names from a function signature line.
fn extract_param_names(sig: &str) -> Vec<String> {
    let paren_start = match sig.find('(') {
        Some(i) => i,
        None => return Vec::new(),
    };
    let paren_end = match sig[paren_start..].find(')') {
        Some(i) => paren_start + i,
        None => return Vec::new(),
    };
    let params_str = &sig[paren_start + 1..paren_end];
    if params_str.trim().is_empty() {
        return Vec::new();
    }

    params_str
        .split(',')
        .filter_map(|p| {
            let p = p.trim();
            if p == "self" || p == "&self" || p == "&mut self" || p == "mut self" {
                Some("self".to_string())
            } else {
                // "name: Type" -> extract name
                p.split(':').next().map(|n| n.trim().to_string())
            }
        })
        .filter(|n| !n.is_empty())
        .collect()
}

/// Extract parameters with their types from a function signature line.
///
/// Returns `(name, type)` pairs. Self parameters are skipped since they
/// don't carry useful type information for spec inference.
fn extract_typed_params(sig: &str) -> Vec<(String, String)> {
    let paren_start = match sig.find('(') {
        Some(i) => i,
        None => return Vec::new(),
    };
    let paren_end = match sig[paren_start..].find(')') {
        Some(i) => paren_start + i,
        None => return Vec::new(),
    };
    let params_str = &sig[paren_start + 1..paren_end];
    if params_str.trim().is_empty() {
        return Vec::new();
    }

    params_str
        .split(',')
        .filter_map(|p| {
            let p = p.trim();
            // Skip self parameters
            if p == "self" || p == "&self" || p == "&mut self" || p == "mut self" {
                return None;
            }
            // "name: Type" -> (name, Type)
            let colon_pos = p.find(':')?;
            let name = p[..colon_pos].trim().to_string();
            let ty = p[colon_pos + 1..].trim().to_string();
            if name.is_empty() || ty.is_empty() {
                return None;
            }
            Some((name, ty))
        })
        .collect()
}

/// Extract the return type from a function signature line.
fn extract_return_type(sig: &str) -> Option<String> {
    // Find "-> Type" after the parameter list
    let arrow_pos = sig.find("->")?;
    let after_arrow = sig[arrow_pos + 2..].trim();
    // Return type ends at `{`, `where`, or end of line
    let end = after_arrow.find(['{', '\n']).unwrap_or(after_arrow.len());
    let ret = after_arrow[..end].trim();
    let ret = ret.strip_suffix("where").unwrap_or(ret).trim();
    if ret.is_empty() { None } else { Some(ret.to_string()) }
}

// ---------------------------------------------------------------------------
// VC generation
// ---------------------------------------------------------------------------

/// Generate standalone VCs from a list of parsed functions.
pub(crate) fn generate_standalone_vcs(functions: &[ParsedFunction]) -> Vec<StandaloneVc> {
    let mut vcs = Vec::new();

    for func in functions {
        // VC: requires spec present
        if func.has_requires {
            vcs.push(StandaloneVc {
                function: func.name.clone(),
                file: func.file.clone(),
                kind: VcKind::PreconditionPresent,
                description: format!("{}: #[requires] specification present", func.name),
                outcome: StandaloneOutcome::Proved,
            });
        }

        // VC: ensures spec present
        if func.has_ensures {
            vcs.push(StandaloneVc {
                function: func.name.clone(),
                file: func.file.clone(),
                kind: VcKind::PostconditionPresent,
                description: format!("{}: #[ensures] specification present", func.name),
                outcome: StandaloneOutcome::Proved,
            });
        }

        // VC: unsafe function needs audit
        if func.is_unsafe {
            vcs.push(StandaloneVc {
                function: func.name.clone(),
                file: func.file.clone(),
                kind: VcKind::UnsafeFunction,
                description: format!("{}: unsafe function requires safety proof", func.name),
                outcome: StandaloneOutcome::Unknown,
            });
        }

        // VC: public function without specs
        if func.is_public && !func.has_requires && !func.has_ensures {
            vcs.push(StandaloneVc {
                function: func.name.clone(),
                file: func.file.clone(),
                kind: VcKind::UnspecifiedPublicApi,
                description: format!("{}: public function has no specification", func.name),
                outcome: StandaloneOutcome::Unknown,
            });
        }
    }

    vcs
}

// ---------------------------------------------------------------------------
// Full analysis pipeline
// ---------------------------------------------------------------------------

/// Run standalone source analysis on a crate directory.
pub(crate) fn analyze_crate(crate_root: &Path) -> SourceAnalysisSummary {
    let files = find_source_files(crate_root);
    let mut all_functions = Vec::new();

    for file in &files {
        all_functions.extend(extract_functions(file));
    }

    let vcs = generate_standalone_vcs(&all_functions);

    let proved = vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Proved).count();
    let failed = vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Failed).count();
    let unknown = vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Unknown).count();

    SourceAnalysisSummary {
        files_analyzed: files.len(),
        functions_found: all_functions.len(),
        public_functions: all_functions.iter().filter(|f| f.is_public).count(),
        unsafe_functions: all_functions.iter().filter(|f| f.is_unsafe).count(),
        specified_functions: all_functions
            .iter()
            .filter(|f| f.has_requires || f.has_ensures)
            .count(),
        total_vcs: vcs.len(),
        proved,
        failed,
        unknown,
        functions: all_functions,
        vcs,
    }
}

/// Run standalone source analysis on a single file.
pub(crate) fn analyze_file(file: &Path) -> SourceAnalysisSummary {
    let functions = extract_functions(file);
    let vcs = generate_standalone_vcs(&functions);

    let proved = vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Proved).count();
    let failed = vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Failed).count();
    let unknown = vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Unknown).count();

    SourceAnalysisSummary {
        files_analyzed: 1,
        functions_found: functions.len(),
        public_functions: functions.iter().filter(|f| f.is_public).count(),
        unsafe_functions: functions.iter().filter(|f| f.is_unsafe).count(),
        specified_functions: functions.iter().filter(|f| f.has_requires || f.has_ensures).count(),
        total_vcs: vcs.len(),
        proved,
        failed,
        unknown,
        functions,
        vcs,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temp_test_dir(label: &str) -> PathBuf {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|duration| duration.as_nanos())
            .unwrap_or(0);
        std::env::temp_dir().join(format!(
            "cargo_trust_source_analysis_{label}_{}_{}",
            std::process::id(),
            unique
        ))
    }

    #[test]
    fn test_extract_simple_function() {
        let source = "fn add(x: i32, y: i32) -> i32 {\n    x + y\n}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "add");
        assert!(!funcs[0].is_public);
        assert!(!funcs[0].is_unsafe);
        assert_eq!(funcs[0].line, 1);
        assert_eq!(funcs[0].params, vec!["x", "y"]);
        assert_eq!(funcs[0].return_type.as_deref(), Some("i32"));
    }

    #[test]
    fn test_extract_pub_function() {
        let source = "pub fn greet(name: &str) -> String {\n    format!(\"Hello, {name}\")\n}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].is_public);
        assert_eq!(funcs[0].name, "greet");
    }

    #[test]
    fn test_extract_pub_crate_function() {
        let source = "pub(crate) fn helper() {}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].is_public);
        assert_eq!(funcs[0].name, "helper");
    }

    #[test]
    fn test_extract_unsafe_function() {
        let source = "pub unsafe fn deref_raw(ptr: *const u8) -> u8 {\n    *ptr\n}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].is_unsafe);
        assert!(funcs[0].is_public);
    }

    #[test]
    fn test_extract_async_function() {
        let source = "pub async fn fetch(url: &str) -> Result<String> {}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "fetch");
        assert!(funcs[0].is_public);
    }

    #[test]
    fn test_extract_const_function() {
        let source = "const fn max(a: u32, b: u32) -> u32 {\n    if a > b { a } else { b }\n}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "max");
    }

    #[test]
    fn test_extract_with_requires() {
        let source = r#"
#[requires(x > 0)]
fn positive_only(x: i32) -> i32 {
    x
}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].has_requires);
        assert!(!funcs[0].has_ensures);
    }

    #[test]
    fn test_extract_with_ensures() {
        let source = r#"
#[ensures(result > 0)]
fn always_positive() -> i32 {
    42
}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(!funcs[0].has_requires);
        assert!(funcs[0].has_ensures);
    }

    #[test]
    fn test_extract_with_both_specs() {
        let source = r#"
#[requires(x > 0)]
#[ensures(result == x * 2)]
pub fn double(x: i32) -> i32 {
    x + x
}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].has_requires);
        assert!(funcs[0].has_ensures);
        assert!(funcs[0].is_public);
    }

    #[test]
    fn test_extract_with_namespaced_specs() {
        let source = r#"
#[trust::requires(x > 0)]
#[trust::ensures(result == x * 2)]
pub fn double(x: i32) -> i32 {
    x + x
}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].has_requires);
        assert!(funcs[0].has_ensures);
        assert!(funcs[0].is_public);
    }

    #[test]
    fn test_extract_multiple_functions() {
        let source = r#"
fn first() {}

pub fn second() {}

#[requires(true)]
fn third() {}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 3);
        assert_eq!(funcs[0].name, "first");
        assert_eq!(funcs[1].name, "second");
        assert_eq!(funcs[2].name, "third");
        assert!(funcs[2].has_requires);
    }

    #[test]
    fn test_extract_skips_comments() {
        let source = r#"
// fn not_a_function() {}
/* fn also_not() {} */
fn real() {}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "real");
    }

    #[test]
    fn test_extract_self_param() {
        let source = "pub fn method(&self, x: i32) -> bool {}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].params, vec!["self", "x"]);
    }

    #[test]
    fn test_extract_no_params() {
        let source = "fn empty() {}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].params.is_empty());
    }

    #[test]
    fn test_extract_extern_fn() {
        let source = "pub unsafe extern \"C\" fn callback(data: *const u8) {}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "callback");
        assert!(funcs[0].is_unsafe);
        assert!(funcs[0].is_public);
    }

    #[test]
    fn test_generate_vcs_public_unspecified() {
        let funcs = vec![ParsedFunction {
            name: "foo".into(),
            file: PathBuf::from("lib.rs"),
            line: 1,
            is_public: true,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: None,
            params: vec![],
            typed_params: vec![],
        }];
        let vcs = generate_standalone_vcs(&funcs);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].kind, VcKind::UnspecifiedPublicApi);
        assert_eq!(vcs[0].outcome, StandaloneOutcome::Unknown);
    }

    #[test]
    fn test_generate_vcs_unsafe() {
        let funcs = vec![ParsedFunction {
            name: "bar".into(),
            file: PathBuf::from("lib.rs"),
            line: 1,
            is_public: false,
            is_unsafe: true,
            has_requires: false,
            has_ensures: false,
            return_type: None,
            params: vec![],
            typed_params: vec![],
        }];
        let vcs = generate_standalone_vcs(&funcs);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].kind, VcKind::UnsafeFunction);
        assert_eq!(vcs[0].outcome, StandaloneOutcome::Unknown);
    }

    #[test]
    fn test_generate_vcs_specified() {
        let funcs = vec![ParsedFunction {
            name: "baz".into(),
            file: PathBuf::from("lib.rs"),
            line: 1,
            is_public: true,
            is_unsafe: false,
            has_requires: true,
            has_ensures: true,
            return_type: Some("i32".into()),
            params: vec!["x".into()],
            typed_params: vec![("x".into(), "i32".into())],
        }];
        let vcs = generate_standalone_vcs(&funcs);
        // 2 VCs: requires present + ensures present (no UnspecifiedPublicApi because has specs)
        assert_eq!(vcs.len(), 2);
        assert!(vcs.iter().any(|v| v.kind == VcKind::PreconditionPresent));
        assert!(vcs.iter().any(|v| v.kind == VcKind::PostconditionPresent));
        assert!(vcs.iter().all(|v| v.outcome == StandaloneOutcome::Proved));
    }

    #[test]
    fn test_generate_vcs_private_no_specs() {
        let funcs = vec![ParsedFunction {
            name: "helper".into(),
            file: PathBuf::from("lib.rs"),
            line: 1,
            is_public: false,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: None,
            params: vec![],
            typed_params: vec![],
        }];
        let vcs = generate_standalone_vcs(&funcs);
        // Private function with no specs and not unsafe generates no VCs
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_analyze_crate_with_temp_dir() {
        let dir = std::env::temp_dir().join("cargo_trust_test_analyze");
        let src_dir = dir.join("src");
        let _ = std::fs::create_dir_all(&src_dir);
        std::fs::write(
            src_dir.join("lib.rs"),
            r#"
pub fn add(x: i32, y: i32) -> i32 { x + y }

#[requires(n > 0)]
pub fn checked(n: u32) -> u32 { n }

unsafe fn raw() {}
"#,
        )
        .expect("write test file");

        let summary = analyze_crate(&dir);
        assert_eq!(summary.files_analyzed, 1);
        assert_eq!(summary.functions_found, 3);
        assert_eq!(summary.public_functions, 2);
        assert_eq!(summary.unsafe_functions, 1);
        assert_eq!(summary.specified_functions, 1);
        assert!(summary.total_vcs > 0);

        // Cleanup
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_no_src_dir() {
        let files = find_source_files(Path::new("/nonexistent/path"));
        assert!(files.is_empty());
    }

    #[test]
    fn test_manifest_path_from_args_parses_flag_forms() {
        let separated = manifest_path_from_args(vec![
            OsString::from("cargo-trust"),
            OsString::from("check"),
            OsString::from("--manifest-path"),
            OsString::from("demo/Cargo.toml"),
        ]);
        assert_eq!(separated, Some(PathBuf::from("demo/Cargo.toml")));

        let equals = manifest_path_from_args(vec![
            OsString::from("cargo-trust"),
            OsString::from("check"),
            OsString::from("--manifest-path=alt/Cargo.toml"),
        ]);
        assert_eq!(equals, Some(PathBuf::from("alt/Cargo.toml")));
    }

    #[test]
    fn test_find_source_files_honors_custom_lib_path() {
        let dir = temp_test_dir("custom-lib");
        let crate_dir = dir.join("crate_root");
        std::fs::create_dir_all(&crate_dir).expect("should create custom lib dir");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[package]
name = "custom-lib"
version = "0.1.0"
edition = "2021"

[lib]
path = "crate_root/lib.rs"
"#,
        )
        .expect("should write Cargo.toml");
        std::fs::write(
            crate_dir.join("lib.rs"),
            r#"

pub fn entry() {}
"#,
        )
        .expect("should write lib.rs");
        std::fs::write(crate_dir.join("helper.rs"), "pub fn helper() {}\n")
            .expect("should write helper.rs");

        let files = find_source_files(&dir);
        assert_eq!(files.len(), 2);
        assert!(files.contains(&crate_dir.join("lib.rs")));
        assert!(files.contains(&crate_dir.join("helper.rs")));

        let summary = analyze_crate(&dir);
        assert_eq!(summary.files_analyzed, 2);
        assert_eq!(summary.functions_found, 2);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_walks_up_to_manifest_ancestor() {
        let dir = temp_test_dir("ancestor");
        let nested = dir.join("src/nested/deeper");
        std::fs::create_dir_all(&nested).expect("should create nested dir");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[package]
name = "ancestor"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write Cargo.toml");
        std::fs::write(dir.join("src/lib.rs"), "pub fn from_root() {}\n")
            .expect("should write lib.rs");
        std::fs::write(dir.join("src/nested/mod.rs"), "pub fn nested() {}\n")
            .expect("should write nested module");

        let files = find_source_files(&nested);
        assert!(files.contains(&dir.join("src/lib.rs")));
        assert!(files.contains(&dir.join("src/nested/mod.rs")));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_accepts_manifest_path_input() {
        let dir = temp_test_dir("manifest-input");
        std::fs::create_dir_all(dir.join("src")).expect("should create src dir");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[package]
name = "manifest-input"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write Cargo.toml");
        std::fs::write(dir.join("src/lib.rs"), "pub fn lib_fn() {}\n")
            .expect("should write lib.rs");

        let files = find_source_files(&dir.join("Cargo.toml"));
        assert_eq!(files, vec![dir.join("src/lib.rs")]);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_supports_workspace_member_glob() {
        let dir = temp_test_dir("workspace");
        let member_a = dir.join("crates/a/src");
        let member_b = dir.join("crates/b/src");
        std::fs::create_dir_all(&member_a).expect("should create member a");
        std::fs::create_dir_all(&member_b).expect("should create member b");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[workspace]
members = ["crates/*"]
"#,
        )
        .expect("should write workspace Cargo.toml");
        std::fs::write(
            dir.join("crates/a/Cargo.toml"),
            r#"
[package]
name = "member-a"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write member a Cargo.toml");
        std::fs::write(
            dir.join("crates/b/Cargo.toml"),
            r#"
[package]
name = "member-b"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write member b Cargo.toml");
        std::fs::write(member_a.join("lib.rs"), "pub fn member_a() {}\n")
            .expect("should write member a lib");
        std::fs::write(member_b.join("main.rs"), "pub fn member_b() {}\n")
            .expect("should write member b main");

        let files = find_source_files(&dir);
        assert!(files.contains(&dir.join("crates/a/src/lib.rs")));
        assert!(files.contains(&dir.join("crates/b/src/main.rs")));

        let _ = std::fs::remove_dir_all(&dir);
    }
}
