//! trust-mir-extract: Bridge from rustc MIR to trust-types verification model
//!
//! Walks rustc's Body<'tcx> and produces VerifiableFunction instances that
//! the downstream pipeline (trust-vcgen, trust-router) can operate on without
//! any rustc dependencies.
//!
//! Requires: #![feature(rustc_private)]
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// tRust: rustc_private + box_patterns needed when built standalone (cargo +nightly).
// When built as part of the compiler workspace (via x.py), the extern crates
// are resolved through Cargo.toml path dependencies.
#![feature(rustc_private)]
#![feature(box_patterns)]
#![allow(unused_extern_crates)]
#![allow(unknown_lints)]
#![allow(rustc::usage_of_ty_tykind)]
#![allow(rustc::usage_of_qualified_ty)]
#![allow(rustc::default_hash_types)]
// dead_code audit: crate-level suppression removed (#939)

extern crate rustc_abi;
extern crate rustc_ast_ir;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

// tRust #339: Call graph construction from MIR.
pub(crate) mod call_graph;
mod convert;
// tRust #232: Backward slicing for VC minimization.
pub(crate) mod slicing;
mod ty_convert;

use rustc_hir::attrs::AttributeKind;
use rustc_hir::{HirId, Node};
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_span::Symbol;
use rustc_span::def_id::DefId;
use trust_types::fx::FxHashMap;
use trust_types::*;

/// tRust: Get a def path string without triggering trimmed_def_paths panic.
/// The trimmed_def_paths query panics on drop if no diagnostics are emitted,
/// which happens in our read-only verification pass.
pub fn safe_def_path_str(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    with_no_trimmed_paths!(tcx.def_path_str(def_id))
}

/// Extract a VerifiableFunction from a rustc MIR Body.
///
/// This is the main entry point. Called once per function in the crate.
pub fn extract_function<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> VerifiableFunction {
    let def_id = body.source.def_id();
    let def_path = safe_def_path_str(tcx, def_id);
    let metadata = extract_metadata(tcx, body);
    // tRust: Use opt_item_name to avoid panic on closures/synthetic items
    // (e.g. `fmt::builders::{closure#0}`). Fall back to last segment of def_path.
    let name = tcx
        .opt_item_name(def_id)
        .map(|s| s.to_string())
        .unwrap_or_else(|| def_path.rsplit("::").next().unwrap_or(&def_path).to_string());

    // tRust #72: Parse contract bodies into formulas for direct consumption.
    let (preconditions, postconditions) = parse_contract_specs(&metadata.contracts);

    // tRust #119: Build structured FunctionSpec from contracts.
    let spec = metadata.spec.clone();

    VerifiableFunction {
        name,
        def_path,
        span: convert::convert_span(tcx, body.span),
        body: extract_body(tcx, body),
        contracts: metadata.contracts,
        preconditions,
        postconditions,
        spec,
    }
}

/// Extract trust-related metadata for a local MIR body.
///
/// This is a sidecar API for issue #10: it keeps the existing `VerifiableFunction`
/// shape intact while making trust annotations explicit and independently testable.
pub(crate) fn extract_metadata<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> TrustMetadata {
    let def_id = body.source.def_id();
    let contracts = extract_contracts(tcx, def_id);
    // tRust #119: Build structured FunctionSpec from contracts.
    let spec = build_function_spec(&contracts);
    TrustMetadata { contracts, trust_annotations: extract_trust_annotations(tcx, def_id), spec }
}

/// tRust: Safely get the span of an attribute. Returns None for parsed
/// built-in attributes that have no meaningful span (e.g., #[inline]).
/// Only `Unparsed` (custom/tool) attributes and a few known `Parsed` variants
/// carry a usable span; all others return None instead of panicking.
fn safe_attr_span(attr: &rustc_hir::Attribute) -> Option<rustc_span::Span> {
    match attr {
        // Custom / tool attributes always have a span.
        rustc_hir::Attribute::Unparsed(item) => Some(item.span),
        // Known Parsed variants with spans (mirrors AttributeExt::span).
        rustc_hir::Attribute::Parsed(AttributeKind::DocComment { span, .. }) => Some(*span),
        rustc_hir::Attribute::Parsed(AttributeKind::Deprecated { span, .. }) => Some(*span),
        // All other Parsed attributes don't have a reliably accessible span.
        rustc_hir::Attribute::Parsed(_) => None,
    }
}

fn extract_contracts(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<Contract> {
    let Some(local_def_id) = def_id.as_local() else {
        return vec![];
    };

    let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
    let source_map = tcx.sess.source_map();
    let contracts: Vec<_> = tcx
        .hir_attrs(hir_id)
        .iter()
        .filter_map(|attr| {
            let kind = attr.path().last().copied().and_then(contract_kind_from_symbol)?;
            let span = attr.value_span().or_else(|| safe_attr_span(attr))?;
            let body = attr
                .value_str()
                .map(|value| value.to_string())
                .or_else(|| {
                    safe_attr_span(attr).and_then(|s| {
                        source_map
                            .span_to_snippet(s)
                            .ok()
                            .map(|snippet| contract_body_from_attr_snippet(&snippet))
                    })
                })
                .unwrap_or_default();

            Some(Contract { kind, span: convert::convert_span(tcx, span), body })
        })
        .collect();

    if contracts.is_empty() && hir_node_supports_outer_attrs(tcx, hir_id) {
        extract_contracts_from_source(tcx, hir_id)
    } else {
        contracts
    }
}

fn hir_node_supports_outer_attrs(tcx: TyCtxt<'_>, hir_id: HirId) -> bool {
    matches!(
        tcx.hir_node(hir_id),
        Node::Item(..) | Node::TraitItem(..) | Node::ImplItem(..) | Node::ForeignItem(..)
    )
}

fn extract_trust_annotations(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<TrustAnnotation> {
    let Some(local_def_id) = def_id.as_local() else {
        return vec![];
    };

    let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
    let source_map = tcx.sess.source_map();

    tcx.hir_attrs(hir_id)
        .iter()
        .flat_map(|attr| {
            let span = match safe_attr_span(attr) {
                Some(s) => s,
                None => return vec![],
            };
            source_map
                .span_to_snippet(span)
                .ok()
                .map(|snippet| {
                    trust_annotations_from_attr_snippet(&snippet)
                        .into_iter()
                        .map(|(kind, body)| TrustAnnotation {
                            kind,
                            span: convert::convert_span(tcx, span),
                            body,
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default()
        })
        .collect()
}

fn contract_kind_from_symbol(name: Symbol) -> Option<ContractKind> {
    contract_kind_from_name(name.as_str().as_ref())
}

fn contract_kind_from_name(name: &str) -> Option<ContractKind> {
    let name = name.trim();
    let name = name.rsplit("::").next().unwrap_or(name);

    match name {
        "requires" | "contracts_requires" | "trust_requires" => Some(ContractKind::Requires),
        "ensures" | "contracts_ensures" | "trust_ensures" => Some(ContractKind::Ensures),
        "invariant" | "trust_invariant" => Some(ContractKind::Invariant),
        "decreases" | "trust_decreases" => Some(ContractKind::Decreases),
        _ => None,
    }
}

fn contract_body_from_attr_snippet(snippet: &str) -> String {
    let mut body = snippet.trim();

    if let Some(stripped) = body.strip_prefix("#[").and_then(|s| s.strip_suffix(']')) {
        body = stripped.trim();
    }

    if let Some(open_idx) = body.find('(') {
        if let Some(close_idx) = body.rfind(')') {
            if close_idx > open_idx {
                return body[open_idx + 1..close_idx].trim().to_string();
            }
        }
    }

    if let Some(eq_idx) = body.find('=') {
        return body[eq_idx + 1..].trim().trim_matches('"').to_string();
    }

    String::new()
}

fn extract_contracts_from_source(tcx: TyCtxt<'_>, hir_id: rustc_hir::HirId) -> Vec<Contract> {
    let Some((source_span, snippet)) = contract_source_window(tcx, hir_id) else {
        return vec![];
    };
    let header = item_source_header(&snippet);
    let span = convert::convert_span(tcx, source_span);

    collect_attr_snippets(header)
        .into_iter()
        .filter_map(|attr| {
            let kind = contract_kind_from_attr_snippet(&attr)?;
            Some(Contract {
                kind,
                span: span.clone(),
                body: contract_body_from_attr_snippet(&attr),
            })
        })
        .collect()
}

fn contract_source_window(
    tcx: TyCtxt<'_>,
    hir_id: rustc_hir::HirId,
) -> Option<(rustc_span::Span, String)> {
    // Native contracts are lowered away before `hir_attrs` reaches this crate.
    // Recover them from the source lines immediately above the function item.
    let body_span = tcx.hir_span_with_body(hir_id);
    let source_map = tcx.sess.source_map();
    let path = source_map.span_to_filename(body_span).into_local_path()?;
    let source = std::fs::read_to_string(path).ok()?;
    let lines: Vec<&str> = source.lines().collect();
    if lines.is_empty() {
        return None;
    }

    let item_line = source_map.lookup_char_pos(body_span.lo()).line.saturating_sub(1);
    let item_line = item_line.min(lines.len().saturating_sub(1));
    let mut start_line = item_line;
    while start_line > 0 {
        let prev = lines[start_line - 1].trim();
        if prev.is_empty() {
            break;
        }
        if prev.starts_with("#[")
            || prev.starts_with("#![")
            || prev.starts_with("///")
            || prev.starts_with("//!")
            || prev.starts_with(']')
            || prev.starts_with(')')
            || prev.ends_with(']')
            || prev.ends_with(')')
        {
            start_line -= 1;
            continue;
        }
        break;
    }

    let window = lines[start_line..=item_line].join("\n");
    Some((body_span, window))
}

fn item_source_header(snippet: &str) -> &str {
    if let Some(idx) = snippet.find("fn") { &snippet[..idx] } else { snippet }
}

fn collect_attr_snippets(text: &str) -> Vec<String> {
    let mut attrs = Vec::new();
    let mut offset = 0usize;

    while let Some(rel_start) = text[offset..].find("#[") {
        let start = offset + rel_start;
        let mut in_string = false;
        let mut escape = false;
        let mut bracket_depth = 1usize;
        let mut end = None;

        for (rel_idx, ch) in text[start + 2..].char_indices() {
            if in_string {
                if escape {
                    escape = false;
                } else if ch == '\\' {
                    escape = true;
                } else if ch == '"' {
                    in_string = false;
                }
                continue;
            }

            match ch {
                '"' => in_string = true,
                '[' => bracket_depth += 1,
                ']' => {
                    bracket_depth = bracket_depth.saturating_sub(1);
                    if bracket_depth == 0 {
                        end = Some(start + 2 + rel_idx + ch.len_utf8());
                        break;
                    }
                }
                _ => {}
            }
        }

        let Some(end) = end else {
            break;
        };
        attrs.push(text[start..end].to_string());
        offset = end;
    }

    attrs
}

fn contract_kind_from_attr_snippet(snippet: &str) -> Option<ContractKind> {
    let inner = snippet.trim().strip_prefix("#[")?.strip_suffix(']')?.trim();
    let name_end = inner.find(['(', '=', ' ']).unwrap_or(inner.len());
    let name = inner[..name_end].trim().rsplit("::").next()?;
    contract_kind_from_name(name)
}

fn normalized_contract_spec_body(kind: ContractKind, body: &str) -> Option<String> {
    let body = strip_string_literal(body);
    let body = body.trim();
    if body.is_empty() {
        return None;
    }

    match kind {
        ContractKind::Ensures => {
            Some(normalize_ensures_closure_body(body).unwrap_or_else(|| body.to_string()))
        }
        _ => Some(body.to_string()),
    }
}

fn build_function_spec(contracts: &[Contract]) -> trust_types::FunctionSpec {
    let mut spec = trust_types::FunctionSpec::default();
    for contract in contracts {
        let Some(body) = normalized_contract_spec_body(contract.kind, &contract.body) else {
            continue;
        };
        match contract.kind {
            ContractKind::Requires => spec.requires.push(body),
            ContractKind::Ensures => spec.ensures.push(body),
            ContractKind::Invariant | ContractKind::LoopInvariant => spec.invariants.push(body),
            ContractKind::Decreases | ContractKind::TypeRefinement | ContractKind::Modifies => {}
            _ => {}
        }
    }
    spec
}

fn normalize_ensures_closure_body(body: &str) -> Option<String> {
    let mut rest = body.trim();
    if let Some(stripped) = rest.strip_prefix("move") {
        rest = stripped.trim_start();
    }
    if !rest.starts_with('|') {
        return None;
    }

    let after_open = &rest[1..];
    let close_idx = after_open.find('|')?;
    let arg_spec = after_open[..close_idx].trim();
    if arg_spec.is_empty() || arg_spec.contains(',') {
        return None;
    }

    let arg_name = arg_spec.split(':').next()?.trim();
    if arg_name.is_empty() || !arg_name.chars().all(|ch| ch == '_' || ch.is_ascii_alphanumeric()) {
        return None;
    }

    let mut expr = after_open[close_idx + 1..].trim();
    if let Some(block_expr) = strip_single_expr_block(expr) {
        expr = block_expr;
    }
    if expr.is_empty() {
        return None;
    }

    let expr = replace_deref_ident(expr, arg_name, "result");
    Some(replace_ident(expr.as_str(), arg_name, "result"))
}

fn strip_single_expr_block(expr: &str) -> Option<&str> {
    let expr = expr.trim();
    let inner = expr.strip_prefix('{')?.strip_suffix('}')?.trim();
    if inner.is_empty() || inner.contains(';') {
        return None;
    }
    Some(inner)
}

fn replace_deref_ident(expr: &str, ident: &str, replacement: &str) -> String {
    let mut out = String::with_capacity(expr.len());
    let bytes = expr.as_bytes();
    let ident_bytes = ident.as_bytes();
    let mut i = 0usize;

    while i < bytes.len() {
        if bytes[i] == b'*' {
            let mut j = i + 1;
            while j < bytes.len() && bytes[j].is_ascii_whitespace() {
                j += 1;
            }
            if bytes.get(j..j + ident_bytes.len()) == Some(ident_bytes)
                && is_ident_start_boundary(expr, j)
                && is_ident_end_boundary(expr, j + ident_bytes.len())
            {
                out.push_str(replacement);
                i = j + ident_bytes.len();
                continue;
            }
        }
        out.push(bytes[i] as char);
        i += 1;
    }

    out
}

fn replace_ident(expr: &str, ident: &str, replacement: &str) -> String {
    let mut out = String::with_capacity(expr.len());
    let bytes = expr.as_bytes();
    let ident_bytes = ident.as_bytes();
    let mut i = 0usize;

    while i < bytes.len() {
        if bytes.get(i..i + ident_bytes.len()) == Some(ident_bytes)
            && is_ident_start_boundary(expr, i)
            && is_ident_end_boundary(expr, i + ident_bytes.len())
        {
            out.push_str(replacement);
            i += ident_bytes.len();
            continue;
        }
        out.push(bytes[i] as char);
        i += 1;
    }

    out
}

fn is_ident_start_boundary(text: &str, start: usize) -> bool {
    start == 0 || !is_ident_char(text.as_bytes()[start - 1])
}

fn is_ident_end_boundary(text: &str, end: usize) -> bool {
    end == text.len() || !is_ident_char(text.as_bytes()[end])
}

fn is_ident_char(b: u8) -> bool {
    (b as char).is_ascii_alphanumeric() || b == b'_'
}

fn trust_annotations_from_attr_snippet(snippet: &str) -> Vec<(TrustAnnotationKind, String)> {
    let mut body = snippet.trim();

    if let Some(stripped) = body.strip_prefix("#[").and_then(|s| s.strip_suffix(']')) {
        body = stripped.trim();
    }

    trust_annotations_from_attr_body(body)
}

fn trust_annotations_from_attr_body(body: &str) -> Vec<(TrustAnnotationKind, String)> {
    let body = body.trim();

    if let Some(rest) = body.strip_prefix("trust(").and_then(|s| s.strip_suffix(')')) {
        return split_trust_annotation_items(rest)
            .into_iter()
            .flat_map(trust_annotation_from_item)
            .collect();
    }

    trust_annotation_from_item(body)
}

fn split_trust_annotation_items(body: &str) -> Vec<&str> {
    let mut items = Vec::new();
    let mut start = 0usize;
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escape = false;

    for (idx, ch) in body.char_indices() {
        if in_string {
            if escape {
                escape = false;
            } else if ch == '\\' {
                escape = true;
            } else if ch == '"' {
                in_string = false;
            }
            continue;
        }

        match ch {
            '"' => in_string = true,
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                items.push(body[start..idx].trim());
                start = idx + ch.len_utf8();
            }
            _ => {}
        }
    }

    let tail = body[start..].trim();
    if !tail.is_empty() {
        items.push(tail);
    }

    items
}

fn trust_annotation_from_item(item: &str) -> Vec<(TrustAnnotationKind, String)> {
    let item = item.trim();
    if item.is_empty() {
        return vec![];
    }

    match item {
        "boundary" | "trust_boundary" => {
            vec![(TrustAnnotationKind::Boundary, String::new())]
        }
        "model" | "trust_model" => vec![(TrustAnnotationKind::Model, String::new())],
        _ => {
            if let Some(body) = trust_assumption_body(item) {
                vec![(TrustAnnotationKind::Assumption, body)]
            } else {
                vec![]
            }
        }
    }
}

fn trust_assumption_body(item: &str) -> Option<String> {
    let item = item.trim();

    if let Some(rest) = item.strip_prefix("assume").or_else(|| item.strip_prefix("trust_assume")) {
        let rest = rest.trim();
        if rest.is_empty() {
            return Some(String::new());
        }

        if let Some(rest) = rest.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
            return Some(strip_string_literal(rest.trim()));
        }

        if let Some(rest) = rest.strip_prefix('=') {
            return Some(strip_string_literal(rest.trim()));
        }
    }

    None
}

fn strip_string_literal(text: &str) -> String {
    let trimmed = text.trim();
    trimmed.strip_prefix('"').and_then(|s| s.strip_suffix('"')).unwrap_or(trimmed).to_string()
}

/// tRust #72: Parse contract bodies into precondition and postcondition formulas.
///
/// Uses `trust_types::parse_spec_expr` to convert textual contract bodies from
/// `#[requires("expr")]` and `#[ensures("expr")]` attributes into `Formula` values.
/// Unparseable specs are silently skipped (they will still appear in `contracts`
/// for downstream diagnostics).
fn parse_contract_specs(contracts: &[Contract]) -> (Vec<Formula>, Vec<Formula>) {
    let mut preconditions = Vec::new();
    let mut postconditions = Vec::new();

    for contract in contracts {
        let Some(body) = normalized_contract_spec_body(contract.kind, &contract.body) else {
            continue;
        };
        let Some(formula) = trust_types::parse_spec_expr(&body) else {
            continue;
        };
        match contract.kind {
            ContractKind::Requires => preconditions.push(formula),
            ContractKind::Ensures => postconditions.push(formula),
            ContractKind::Invariant | ContractKind::Decreases => {}
            _ => {}
        }
    }

    (preconditions, postconditions)
}

fn extract_body<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> VerifiableBody {
    // Build local variable name lookup from debug info
    let debug_names = build_debug_name_map(body);

    let locals = body
        .local_decls
        .iter_enumerated()
        .map(|(local, decl)| {
            let index = local.as_usize();
            LocalDecl {
                index,
                ty: ty_convert::convert_ty(tcx, decl.ty),
                name: debug_names.get(&index).cloned(),
            }
        })
        .collect();

    let blocks = body
        .basic_blocks
        .iter_enumerated()
        .map(|(bb, bb_data)| convert::convert_basic_block(tcx, bb, bb_data))
        .collect();

    let return_ty = ty_convert::convert_ty(tcx, body.local_decls[mir::RETURN_PLACE].ty);

    VerifiableBody { locals, blocks, arg_count: body.arg_count, return_ty }
}

/// Build a map from Local index to user-visible variable name using debug info.
fn build_debug_name_map(body: &mir::Body<'_>) -> FxHashMap<usize, String> {
    use rustc_middle::mir::VarDebugInfoContents;
    let mut names = FxHashMap::default();

    for debug_info in &body.var_debug_info {
        if let VarDebugInfoContents::Place(place) = &debug_info.value {
            if place.projection.is_empty() {
                names.insert(place.local.as_usize(), debug_info.name.to_string());
            }
        }
    }

    names
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate rustc_driver;
    extern crate rustc_hir;
    extern crate rustc_interface;

    use std::collections::BTreeMap;
    use std::io;
    use std::path::Path;
    use std::process::Command;
    use std::sync::Arc;

    use rustc_driver::Compilation;
    use rustc_interface::interface::{Compiler, Config};

    const CONTRACT_FIXTURE_SOURCE: &str = r#"
#![feature(contracts)]

use core::contracts::{ensures, requires};

#[requires(n > 0)]
fn reciprocal(n: u32) -> f64 {
    1.0 / (n as f64)
}

#[ensures(|ret: &i32| *ret >= 0)]
fn abs_broken(x: i32) -> i32 {
    x
}
"#;
    const CONTRACT_FIXTURE_PATH: &str = "contracts_fixture.rs";
    const CALL_TARGET_FIXTURE_SOURCE: &str = r#"
#[inline(never)]
pub fn helper() -> i32 {
    7
}

pub fn caller() -> i32 {
    helper()
}

pub fn exit_wrapper() -> ! {
    std::process::exit(1)
}
"#;
    const CALL_TARGET_FIXTURE_PATH: &str = "call_target_fixture.rs";

    struct InMemoryContractFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryContractFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(CONTRACT_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CONTRACT_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected contract fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in contract tests"))
        }
    }

    struct InMemoryCallTargetFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryCallTargetFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(CALL_TARGET_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CALL_TARGET_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected call target fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in call-target tests"))
        }
    }

    struct ContractExtractionCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for ContractExtractionCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryContractFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.functions.insert(ident.name.to_string(), extract_function(tcx, body));
                }
            }

            Compilation::Stop
        }
    }

    #[derive(Debug, Default)]
    struct CallTargetFixture {
        functions: BTreeMap<String, VerifiableFunction>,
        direct_call_symbols: BTreeMap<String, Vec<String>>,
    }

    struct CallTargetCallbacks {
        fixture: CallTargetFixture,
    }

    impl rustc_driver::Callbacks for CallTargetCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryCallTargetFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let fn_name = ident.name.to_string();
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.fixture.functions.insert(fn_name.clone(), extract_function(tcx, body));
                    self.fixture
                        .direct_call_symbols
                        .insert(fn_name, direct_call_symbol_names(tcx, body));
                }
            }

            Compilation::Stop
        }
    }

    fn compiler_sysroot() -> Option<String> {
        option_env!("TEST_SYSROOT")
            .map(str::to_owned)
            .or_else(|| std::env::var("RUSTC_SYSROOT").ok())
            .or_else(|| std::env::var("SYSROOT").ok())
            .or_else(|| {
                let rustc = std::env::var("RUSTC")
                    .ok()
                    .or_else(|| option_env!("RUSTC").map(str::to_owned))
                    .unwrap_or_else(|| "rustc".to_string());
                let output = Command::new(rustc).args(["--print", "sysroot"]).output().ok()?;
                if !output.status.success() {
                    return None;
                }
                let sysroot = String::from_utf8_lossy(&output.stdout).trim().to_string();
                (!sysroot.is_empty()).then_some(sysroot)
            })
    }

    fn extract_contract_fixture_functions() -> BTreeMap<String, VerifiableFunction> {
        let mut callbacks = ContractExtractionCallbacks { functions: BTreeMap::new() };
        let mut args = vec![
            "rustc".to_string(),
            CONTRACT_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_contracts_fixture".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
        ];
        if let Some(sysroot) = compiler_sysroot() {
            args.push("--sysroot".to_string());
            args.push(sysroot);
        }

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile contract fixture");

        callbacks.functions
    }

    fn extract_call_target_fixture() -> CallTargetFixture {
        let mut callbacks = CallTargetCallbacks { fixture: CallTargetFixture::default() };
        let mut args = vec![
            "rustc".to_string(),
            CALL_TARGET_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_call_target_fixture".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
        ];
        if let Some(sysroot) = compiler_sysroot() {
            args.push("--sysroot".to_string());
            args.push(sysroot);
        }

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile call-target fixture");

        callbacks.fixture
    }

    fn direct_call_symbol_names<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Vec<String> {
        let typing_env = body.typing_env(tcx);

        body.basic_blocks
            .iter()
            .filter_map(|bb| match &bb.terminator().kind {
                mir::TerminatorKind::Call { func, .. } => match func {
                    mir::Operand::Constant(box const_op) => match const_op.const_.ty().kind() {
                        rustc_middle::ty::TyKind::FnDef(def_id, generic_args) => {
                            rustc_middle::ty::Instance::try_resolve(
                                tcx,
                                typing_env,
                                *def_id,
                                *generic_args,
                            )
                            .ok()
                            .flatten()
                            .map(|instance| tcx.symbol_name(instance).name.to_string())
                        }
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            })
            .collect()
    }

    fn extracted_call_targets(func: &VerifiableFunction) -> Vec<String> {
        func.body
            .blocks
            .iter()
            .filter_map(|bb| match &bb.terminator {
                Terminator::Call { func, .. } => Some(func.clone()),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn trust_annotation_snippets_parse_conservatively() {
        let boundary = trust_annotations_from_attr_snippet("#[trust(boundary)]");
        assert_eq!(boundary.len(), 1);
        assert_eq!(boundary[0].0, TrustAnnotationKind::Boundary);
        assert!(boundary[0].1.is_empty());

        let model = trust_annotations_from_attr_snippet("#[trust(model)]");
        assert_eq!(model.len(), 1);
        assert_eq!(model[0].0, TrustAnnotationKind::Model);
        assert!(model[0].1.is_empty());

        let assume = trust_annotations_from_attr_snippet(
            "#[trust(assume = \"calls an authenticated gateway\")]",
        );
        assert_eq!(assume.len(), 1);
        assert_eq!(assume[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(assume[0].1, "calls an authenticated gateway");

        let nested = trust_annotations_from_attr_snippet(
            "#[trust(boundary, assume(\"exactly once\"), model)]",
        );
        assert_eq!(nested.len(), 3);
        assert_eq!(nested[0].0, TrustAnnotationKind::Boundary);
        assert_eq!(nested[1].0, TrustAnnotationKind::Assumption);
        assert_eq!(nested[1].1, "exactly once");
        assert_eq!(nested[2].0, TrustAnnotationKind::Model);

        let direct = trust_annotations_from_attr_snippet(
            "#[trust_assume = \"state transitions are explicit\"]",
        );
        assert_eq!(direct.len(), 1);
        assert_eq!(direct[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(direct[0].1, "state transitions are explicit");
    }

    #[test]
    fn trust_annotation_snippets_ignore_unrelated_attrs() {
        assert!(trust_annotations_from_attr_snippet("#[doc = \"hello\"]").is_empty());
        assert!(trust_annotations_from_attr_snippet("#[trust(other)]").is_empty());
    }

    #[test]
    fn extracted_call_targets_use_semantic_paths_not_codegen_symbols() {
        let fixture = extract_call_target_fixture();

        let helper = fixture.functions.get("helper").expect("helper should be extracted");
        let caller = fixture.functions.get("caller").expect("caller should be extracted");
        let exit_wrapper =
            fixture.functions.get("exit_wrapper").expect("exit_wrapper should be extracted");

        assert_eq!(helper.name, "helper");
        assert!(
            helper.def_path.ends_with("::helper"),
            "expected semantic def_path for helper, got `{}`",
            helper.def_path
        );

        let caller_targets = extracted_call_targets(caller);
        assert_eq!(caller_targets, vec![helper.def_path.clone()]);
        assert_ne!(caller_targets[0], helper.name);

        let caller_symbols = fixture
            .direct_call_symbols
            .get("caller")
            .expect("caller direct-call symbols should be captured");
        assert_eq!(caller_symbols.len(), 1);
        assert_ne!(caller_targets[0], caller_symbols[0]);

        let exit_targets = extracted_call_targets(exit_wrapper);
        assert_eq!(exit_targets, vec!["std::process::exit".to_string()]);

        let exit_symbols = fixture
            .direct_call_symbols
            .get("exit_wrapper")
            .expect("exit_wrapper direct-call symbols should be captured");
        assert_eq!(exit_symbols.len(), 1);
        assert_ne!(exit_targets[0], exit_symbols[0]);
    }

    // tRust #72: Tests for parse_contract_specs

    #[test]
    fn parse_contract_specs_extracts_requires_as_preconditions() {
        let contracts = vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre.len(), 1);
        assert!(post.is_empty());
        assert_eq!(
            pre[0],
            Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );
    }

    #[test]
    fn parse_contract_specs_extracts_ensures_as_postconditions() {
        let contracts = vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result >= 0".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert_eq!(post.len(), 1);
        // "result" maps to "_0" in the spec parser
        assert_eq!(
            post[0],
            Formula::Ge(
                Box::new(Formula::Var("_0".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );
    }

    #[test]
    fn parse_contract_specs_extracts_closure_ensures_as_postconditions() {
        let contracts = vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "|ret: &i32| *ret >= 0".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert_eq!(post.len(), 1);
        assert_eq!(
            post[0],
            Formula::Ge(
                Box::new(Formula::Var("_0".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );
    }

    #[test]
    fn parse_contract_specs_handles_multiple_contracts() {
        let contracts = vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "n > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "n < 100".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result >= n".to_string(),
            },
        ];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre.len(), 2);
        assert_eq!(post.len(), 1);
    }

    #[test]
    fn parse_contract_specs_skips_unparseable_bodies() {
        let contracts = vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "???invalid".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert!(post.is_empty());
    }

    #[test]
    fn parse_contract_specs_skips_empty_bodies() {
        let contracts = vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "  ".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert!(post.is_empty());
    }

    #[test]
    fn parse_contract_specs_ignores_invariant_and_decreases() {
        let contracts = vec![
            Contract {
                kind: ContractKind::Invariant,
                span: SourceSpan::default(),
                body: "x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Decreases,
                span: SourceSpan::default(),
                body: "n".to_string(),
            },
        ];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert!(post.is_empty());
    }

    // tRust: #472 — Additional tests to increase test density

    // --- contract_body_from_attr_snippet tests ---

    #[test]
    fn test_contract_body_from_attr_snippet_parenthesized() {
        assert_eq!(contract_body_from_attr_snippet("#[requires(x > 0)]"), "x > 0");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_with_quotes() {
        assert_eq!(
            contract_body_from_attr_snippet("#[ensures(\"result >= 0\")]"),
            "\"result >= 0\""
        );
    }

    #[test]
    fn test_contract_body_from_attr_snippet_eq_form() {
        assert_eq!(contract_body_from_attr_snippet("#[requires = \"x > 0\"]"), "x > 0");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_no_body_returns_empty() {
        assert_eq!(contract_body_from_attr_snippet("#[requires]"), "");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_raw_text() {
        // No #[...] wrapper
        assert_eq!(contract_body_from_attr_snippet("requires(a + b < c)"), "a + b < c");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_nested_parens() {
        assert_eq!(contract_body_from_attr_snippet("#[requires(f(x) > g(y))]"), "f(x) > g(y)");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_whitespace_trimmed() {
        assert_eq!(contract_body_from_attr_snippet("  #[requires(  a > b  )]  "), "a > b");
    }

    #[test]
    fn test_contract_kind_from_name_supports_namespaced_requires() {
        assert_eq!(contract_kind_from_name("trust::requires"), Some(ContractKind::Requires));
    }

    #[test]
    fn test_contract_kind_from_name_supports_namespaced_ensures() {
        assert_eq!(contract_kind_from_name("trust::ensures"), Some(ContractKind::Ensures));
    }

    #[test]
    fn test_normalized_contract_spec_body_unquotes_string_literal() {
        assert_eq!(
            normalized_contract_spec_body(ContractKind::Requires, "\"x > 0\""),
            Some("x > 0".to_string())
        );
    }

    #[test]
    fn test_normalized_contract_spec_body_maps_ensures_closure_to_result() {
        assert_eq!(
            normalized_contract_spec_body(ContractKind::Ensures, "move |ret: &i32| { *ret >= 0 }"),
            Some("result >= 0".to_string())
        );
    }

    // --- strip_string_literal tests ---

    #[test]
    fn test_strip_string_literal_removes_quotes() {
        assert_eq!(strip_string_literal("\"hello world\""), "hello world");
    }

    #[test]
    fn test_strip_string_literal_no_quotes_passthrough() {
        assert_eq!(strip_string_literal("no_quotes"), "no_quotes");
    }

    #[test]
    fn test_strip_string_literal_empty_quoted() {
        assert_eq!(strip_string_literal("\"\""), "");
    }

    #[test]
    fn test_strip_string_literal_trims_whitespace() {
        assert_eq!(strip_string_literal("  \"trimmed\"  "), "trimmed");
    }

    #[test]
    fn test_strip_string_literal_single_quote_no_strip() {
        // Only matching double quotes are stripped
        assert_eq!(strip_string_literal("\"unmatched"), "\"unmatched");
    }

    // --- trust_annotation_from_item tests ---

    #[test]
    fn test_trust_annotation_from_item_boundary() {
        let result = trust_annotation_from_item("boundary");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Boundary);
        assert!(result[0].1.is_empty());
    }

    #[test]
    fn test_trust_annotation_from_item_trust_boundary() {
        let result = trust_annotation_from_item("trust_boundary");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Boundary);
    }

    #[test]
    fn test_trust_annotation_from_item_model() {
        let result = trust_annotation_from_item("model");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Model);
        assert!(result[0].1.is_empty());
    }

    #[test]
    fn test_trust_annotation_from_item_trust_model() {
        let result = trust_annotation_from_item("trust_model");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Model);
    }

    #[test]
    fn test_trust_annotation_from_item_assume_empty() {
        let result = trust_annotation_from_item("assume");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Assumption);
        assert!(result[0].1.is_empty());
    }

    #[test]
    fn test_trust_annotation_from_item_assume_with_parens() {
        let result = trust_annotation_from_item("assume(\"safe by design\")");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(result[0].1, "safe by design");
    }

    #[test]
    fn test_trust_annotation_from_item_assume_with_eq() {
        let result = trust_annotation_from_item("assume = \"always valid\"");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(result[0].1, "always valid");
    }

    #[test]
    fn test_trust_annotation_from_item_empty_returns_empty() {
        assert!(trust_annotation_from_item("").is_empty());
    }

    #[test]
    fn test_trust_annotation_from_item_unknown_returns_empty() {
        assert!(trust_annotation_from_item("whatever").is_empty());
        assert!(trust_annotation_from_item("debug").is_empty());
        assert!(trust_annotation_from_item("inline").is_empty());
    }

    // --- trust_assumption_body tests ---

    #[test]
    fn test_trust_assumption_body_bare_assume() {
        assert_eq!(trust_assumption_body("assume"), Some(String::new()));
    }

    #[test]
    fn test_trust_assumption_body_trust_assume() {
        assert_eq!(trust_assumption_body("trust_assume"), Some(String::new()));
    }

    #[test]
    fn test_trust_assumption_body_paren_form() {
        assert_eq!(trust_assumption_body("assume(\"reason\")"), Some("reason".to_string()));
    }

    #[test]
    fn test_trust_assumption_body_eq_form() {
        assert_eq!(trust_assumption_body("assume = \"reason\""), Some("reason".to_string()));
    }

    #[test]
    fn test_trust_assumption_body_trust_assume_paren() {
        assert_eq!(trust_assumption_body("trust_assume(\"safe\")"), Some("safe".to_string()));
    }

    #[test]
    fn test_trust_assumption_body_not_assume_returns_none() {
        assert_eq!(trust_assumption_body("boundary"), None);
        assert_eq!(trust_assumption_body("model"), None);
        assert_eq!(trust_assumption_body("other"), None);
    }

    // --- split_trust_annotation_items tests ---

    #[test]
    fn test_split_trust_annotation_items_single() {
        let items = split_trust_annotation_items("boundary");
        assert_eq!(items, vec!["boundary"]);
    }

    #[test]
    fn test_split_trust_annotation_items_multiple() {
        let items = split_trust_annotation_items("boundary, model, assume");
        assert_eq!(items, vec!["boundary", "model", "assume"]);
    }

    #[test]
    fn test_split_trust_annotation_items_nested_parens() {
        let items = split_trust_annotation_items("assume(\"a, b\"), model");
        assert_eq!(items, vec!["assume(\"a, b\")", "model"]);
    }

    #[test]
    fn test_split_trust_annotation_items_empty() {
        let items = split_trust_annotation_items("");
        assert!(items.is_empty());
    }

    #[test]
    fn test_split_trust_annotation_items_escaped_strings() {
        let items = split_trust_annotation_items("assume(\"contains \\\"escaped\\\"\"), boundary");
        assert_eq!(items.len(), 2);
        assert_eq!(items[1], "boundary");
    }

    // --- trust_annotations_from_attr_body tests ---

    #[test]
    fn test_trust_annotations_from_attr_body_trust_wrapper() {
        let anns = trust_annotations_from_attr_body("trust(boundary)");
        assert_eq!(anns.len(), 1);
        assert_eq!(anns[0].0, TrustAnnotationKind::Boundary);
    }

    #[test]
    fn test_trust_annotations_from_attr_body_direct_item() {
        let anns = trust_annotations_from_attr_body("boundary");
        assert_eq!(anns.len(), 1);
        assert_eq!(anns[0].0, TrustAnnotationKind::Boundary);
    }

    #[test]
    fn test_trust_annotations_from_attr_body_trust_multi() {
        let anns = trust_annotations_from_attr_body("trust(boundary, model)");
        assert_eq!(anns.len(), 2);
        assert_eq!(anns[0].0, TrustAnnotationKind::Boundary);
        assert_eq!(anns[1].0, TrustAnnotationKind::Model);
    }

    // --- parse_contract_specs edge cases ---

    #[test]
    fn test_parse_contract_specs_empty_contracts() {
        let (pre, post) = parse_contract_specs(&[]);
        assert!(pre.is_empty());
        assert!(post.is_empty());
    }

    #[test]
    fn test_parse_contract_specs_mixed_valid_invalid() {
        let contracts = vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "!!!invalid".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result == 1".to_string(),
            },
        ];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre.len(), 1, "only valid requires should be parsed");
        assert_eq!(post.len(), 1, "valid ensures should be parsed");
    }

    #[test]
    fn test_parse_contract_specs_only_whitespace_body() {
        let contracts = vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "\t\n  ".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert!(post.is_empty());
    }

    // --- trust_annotations_from_attr_snippet edge cases ---

    #[test]
    fn test_trust_annotations_from_attr_snippet_empty() {
        assert!(trust_annotations_from_attr_snippet("").is_empty());
    }

    #[test]
    fn test_trust_annotations_from_attr_snippet_whitespace_only() {
        assert!(trust_annotations_from_attr_snippet("   ").is_empty());
    }

    #[test]
    fn test_trust_annotations_from_attr_snippet_trust_assume_eq_form() {
        let result =
            trust_annotations_from_attr_snippet("#[trust_assume = \"sound by construction\"]");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(result[0].1, "sound by construction");
    }

    #[test]
    fn test_trust_annotations_from_attr_snippet_bare_boundary() {
        let result = trust_annotations_from_attr_snippet("boundary");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Boundary);
    }

    #[test]
    fn compiler_contract_attrs_extract_into_pre_and_postconditions() {
        let functions = extract_contract_fixture_functions();

        let reciprocal = functions.get("reciprocal").expect("reciprocal should be extracted");
        assert_eq!(reciprocal.contracts.len(), 1);
        assert_eq!(reciprocal.contracts[0].body, "n > 0");
        assert_eq!(reciprocal.spec.requires, vec!["n > 0".to_string()]);
        assert_eq!(
            reciprocal.preconditions,
            vec![Formula::Gt(
                Box::new(Formula::Var("n".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )]
        );

        let abs_broken = functions.get("abs_broken").expect("abs_broken should be extracted");
        assert_eq!(abs_broken.contracts.len(), 1);
        assert_eq!(abs_broken.contracts[0].body, "|ret: &i32| *ret >= 0");
        assert_eq!(abs_broken.spec.ensures, vec!["result >= 0".to_string()]);
        assert_eq!(
            abs_broken.postconditions,
            vec![Formula::Ge(
                Box::new(Formula::Var("_0".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )]
        );
    }
}
