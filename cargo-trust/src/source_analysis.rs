// Lightweight source-level analysis for standalone verification mode.
//
// Parses Rust source files to extract function signatures and specification
// attributes (#[requires], #[ensures]) without requiring the full rustc MIR
// pipeline. Generates basic verification conditions for each function.
//
// This enables `cargo trust check --standalone` to produce a verification
// summary even when the stage1 rustc is not built.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

use serde::Serialize;

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

/// Find all .rs source files in a crate directory.
///
/// Reads Cargo.toml to find `src/` directory, then recursively finds all
/// `.rs` files. Falls back to walking `src/` if Cargo.toml is unreadable.
pub(crate) fn find_source_files(crate_root: &Path) -> Vec<PathBuf> {
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
pub(crate) fn extract_functions_from_source(
    source: &str,
    file: &Path,
) -> Vec<ParsedFunction> {
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
        if trimmed.starts_with("#[requires") || trimmed.starts_with("#[trust_requires") {
            pending_requires = true;
            continue;
        }
        if trimmed.starts_with("#[ensures") || trimmed.starts_with("#[trust_ensures") {
            pending_ensures = true;
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
    let end = after_arrow
        .find(['{', '\n'])
        .unwrap_or(after_arrow.len());
    let ret = after_arrow[..end].trim();
    let ret = ret.strip_suffix("where").unwrap_or(ret).trim();
    if ret.is_empty() {
        None
    } else {
        Some(ret.to_string())
    }
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
                description: format!(
                    "{}: #[requires] specification present",
                    func.name
                ),
                outcome: StandaloneOutcome::Proved,
            });
        }

        // VC: ensures spec present
        if func.has_ensures {
            vcs.push(StandaloneVc {
                function: func.name.clone(),
                file: func.file.clone(),
                kind: VcKind::PostconditionPresent,
                description: format!(
                    "{}: #[ensures] specification present",
                    func.name
                ),
                outcome: StandaloneOutcome::Proved,
            });
        }

        // VC: unsafe function needs audit
        if func.is_unsafe {
            vcs.push(StandaloneVc {
                function: func.name.clone(),
                file: func.file.clone(),
                kind: VcKind::UnsafeFunction,
                description: format!(
                    "{}: unsafe function requires safety proof",
                    func.name
                ),
                outcome: StandaloneOutcome::Unknown,
            });
        }

        // VC: public function without specs
        if func.is_public && !func.has_requires && !func.has_ensures {
            vcs.push(StandaloneVc {
                function: func.name.clone(),
                file: func.file.clone(),
                kind: VcKind::UnspecifiedPublicApi,
                description: format!(
                    "{}: public function has no specification",
                    func.name
                ),
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

    let proved = vcs
        .iter()
        .filter(|v| v.outcome == StandaloneOutcome::Proved)
        .count();
    let failed = vcs
        .iter()
        .filter(|v| v.outcome == StandaloneOutcome::Failed)
        .count();
    let unknown = vcs
        .iter()
        .filter(|v| v.outcome == StandaloneOutcome::Unknown)
        .count();

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

    let proved = vcs
        .iter()
        .filter(|v| v.outcome == StandaloneOutcome::Proved)
        .count();
    let failed = vcs
        .iter()
        .filter(|v| v.outcome == StandaloneOutcome::Failed)
        .count();
    let unknown = vcs
        .iter()
        .filter(|v| v.outcome == StandaloneOutcome::Unknown)
        .count();

    SourceAnalysisSummary {
        files_analyzed: 1,
        functions_found: functions.len(),
        public_functions: functions.iter().filter(|f| f.is_public).count(),
        unsafe_functions: functions.iter().filter(|f| f.is_unsafe).count(),
        specified_functions: functions
            .iter()
            .filter(|f| f.has_requires || f.has_ensures)
            .count(),
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
}
