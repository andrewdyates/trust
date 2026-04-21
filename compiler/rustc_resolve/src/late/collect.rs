// tRust: Split from late.rs -- ItemInfoCollector, Resolver::late_resolve_crate, and helpers.
// Part of #843, #838

use std::borrow::Cow;
use std::collections::hash_map::Entry;
use std::debug_assert_matches;
use std::mem::{replace, swap, take};
use std::ops::{ControlFlow, Range};

use rustc_ast::visit::{
    AssocCtxt, BoundKind, FnCtxt, FnKind, Visitor, try_visit, visit_opt, walk_list,
};
use rustc_ast::*;
use rustc_data_structures::either::Either;
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap};
use rustc_data_structures::unord::{UnordMap, UnordSet};
use rustc_errors::codes::*;
use rustc_errors::{
    Applicability, Diag, DiagArgValue, ErrorGuaranteed, IntoDiagArg, MultiSpan, StashKey,
    Suggestions, pluralize,
};
use rustc_hir::def::Namespace::{self, *};
use rustc_hir::def::{self, CtorKind, DefKind, LifetimeRes, NonMacroAttrKind, PartialRes, PerNS};
use rustc_hir::def_id::{CRATE_DEF_ID, DefId, LOCAL_CRATE, LocalDefId};
use rustc_hir::{MissingLifetimeKind, PrimTy, TraitCandidate};
use rustc_middle::middle::resolve_bound_vars::Set1;
use rustc_middle::ty::{AssocTag, DelegationInfo, Visibility};
use rustc_middle::{bug, span_bug};
use rustc_session::config::{CrateType, ResolveDocLinks};
use rustc_session::lint;
use rustc_session::parse::feature_err;
use rustc_span::{BytePos, DUMMY_SP, Ident, Span, Spanned, Symbol, kw, respan, sym};
use smallvec::{SmallVec, smallvec};
use thin_vec::ThinVec;
use tracing::{debug, instrument, trace};

use crate::{
    BindingError, BindingKey, Decl, DelegationFnSig, Finalize, IdentKey, LateDecl, Module,
    ModuleOrUniformRoot, ParentScope, PathResult, ResolutionError, Resolver, Segment, Stage,
    TyCtxt, UseError, Used, errors, path_names_to_string, rustdoc,
};


use super::diagnostics::{ElisionFnParameter, LifetimeElisionCandidate, MissingLifetime};
use super::types::*;
use super::*;


/// Walks the whole crate in DFS order, visiting each item, counting the declared number of
/// lifetime generic parameters and function parameters.
struct ItemInfoCollector<'a, 'ra, 'tcx> {
    r: &'a mut Resolver<'ra, 'tcx>,
}

impl ItemInfoCollector<'_, '_, '_> {
    fn collect_fn_info(&mut self, decl: &FnDecl, id: NodeId) {
        self.r
            .delegation_fn_sigs
            .insert(self.r.local_def_id(id), DelegationFnSig { has_self: decl.has_self() });
    }
}

fn required_generic_args_suggestion(generics: &ast::Generics) -> Option<String> {
    let required = generics
        .params
        .iter()
        .filter_map(|param| match &param.kind {
            ast::GenericParamKind::Lifetime => Some("'_"),
            ast::GenericParamKind::Type { default } => {
                if default.is_none() {
                    Some("_")
                } else {
                    None
                }
            }
            ast::GenericParamKind::Const { default, .. } => {
                if default.is_none() {
                    Some("_")
                } else {
                    None
                }
            }
        })
        .collect::<Vec<_>>();

    if required.is_empty() { None } else { Some(format!("<{}>", required.join(", "))) }
}

impl<'ast> Visitor<'ast> for ItemInfoCollector<'_, '_, '_> {
    fn visit_item(&mut self, item: &'ast Item) {
        match &item.kind {
            ItemKind::TyAlias(box TyAlias { generics, .. })
            | ItemKind::Const(box ConstItem { generics, .. })
            | ItemKind::Fn(box Fn { generics, .. })
            | ItemKind::Enum(_, generics, _)
            | ItemKind::Struct(_, generics, _)
            | ItemKind::Union(_, generics, _)
            | ItemKind::Impl(Impl { generics, .. })
            | ItemKind::Trait(box Trait { generics, .. })
            | ItemKind::TraitAlias(box TraitAlias { generics, .. }) => {
                if let ItemKind::Fn(box Fn { sig, .. }) = &item.kind {
                    self.collect_fn_info(&sig.decl, item.id);
                }

                let def_id = self.r.local_def_id(item.id);
                let count = generics
                    .params
                    .iter()
                    .filter(|param| matches!(param.kind, ast::GenericParamKind::Lifetime { .. }))
                    .count();
                self.r.item_generics_num_lifetimes.insert(def_id, count);
            }

            ItemKind::ForeignMod(ForeignMod { items, .. }) => {
                for foreign_item in items {
                    if let ForeignItemKind::Fn(box Fn { sig, .. }) = &foreign_item.kind {
                        self.collect_fn_info(&sig.decl, foreign_item.id);
                    }
                }
            }

            ItemKind::Mod(..)
            | ItemKind::Static(..)
            | ItemKind::ConstBlock(..)
            | ItemKind::Use(..)
            | ItemKind::ExternCrate(..)
            | ItemKind::MacroDef(..)
            | ItemKind::GlobalAsm(..)
            | ItemKind::MacCall(..)
            | ItemKind::DelegationMac(..) => {}
            ItemKind::Delegation(..) => {
                // Delegated functions have lifetimes, their count is not necessarily zero.
                // But skipping the delegation items here doesn't mean that the count will be considered zero,
                // it means there will be a panic when retrieving the count,
                // but for delegation items we are never actually retrieving that count in practice.
            }
        }
        visit::walk_item(self, item)
    }

    fn visit_assoc_item(&mut self, item: &'ast AssocItem, ctxt: AssocCtxt) {
        if let AssocItemKind::Fn(box Fn { sig, .. }) = &item.kind {
            self.collect_fn_info(&sig.decl, item.id);
        }

        if let AssocItemKind::Type(box ast::TyAlias { generics, .. }) = &item.kind {
            let def_id = self.r.local_def_id(item.id);
            if let Some(suggestion) = required_generic_args_suggestion(generics) {
                self.r.item_required_generic_args_suggestions.insert(def_id, suggestion);
            }
        }
        visit::walk_assoc_item(self, item, ctxt);
    }
}

impl<'ra, 'tcx> Resolver<'ra, 'tcx> {
    pub(crate) fn late_resolve_crate(&mut self, krate: &Crate) {
        visit::walk_crate(&mut ItemInfoCollector { r: self }, krate);
        let mut late_resolution_visitor = LateResolutionVisitor::new(self);
        late_resolution_visitor.resolve_doc_links(&krate.attrs, MaybeExported::Ok(CRATE_NODE_ID));
        visit::walk_crate(&mut late_resolution_visitor, krate);
        for (id, span) in late_resolution_visitor.diag_metadata.unused_labels.iter() {
            self.lint_buffer.buffer_lint(
                lint::builtin::UNUSED_LABELS,
                *id,
                *span,
                errors::UnusedLabel,
            );
        }
    }
}

/// Check if definition matches a path
fn def_id_matches_path(tcx: TyCtxt<'_>, mut def_id: DefId, expected_path: &[&str]) -> bool {
    let mut path = expected_path.iter().rev();
    while let (Some(parent), Some(next_step)) = (tcx.opt_parent(def_id), path.next()) {
        if !tcx.opt_item_name(def_id).is_some_and(|n| n.as_str() == *next_step) {
            return false;
        }
        def_id = parent;
    }
    true
}
