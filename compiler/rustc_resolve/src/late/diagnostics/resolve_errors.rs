// tRust: split from diagnostics.rs

use std::borrow::Cow;
use std::iter;
use std::ops::Deref;

use rustc_ast::visit::{FnCtxt, FnKind, LifetimeCtxt, Visitor, walk_ty};
use rustc_ast::{
    self as ast, AngleBracketedArg, AssocItemKind, DUMMY_NODE_ID, Expr, ExprKind, GenericArg,
    GenericArgs, GenericParam, GenericParamKind, Item, ItemKind, MethodCall, NodeId, Path,
    PathSegment, Ty, TyKind,
};
use rustc_ast_pretty::pprust::{path_to_string, where_bound_predicate_to_string};
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet};
use rustc_errors::codes::*;
use rustc_errors::{
    Applicability, Diag, ErrorGuaranteed, MultiSpan, SuggestionStyle, pluralize,
    struct_span_code_err,
};
use rustc_hir as hir;
use rustc_hir::def::Namespace::{self, *};
use rustc_hir::def::{self, CtorKind, CtorOf, DefKind, MacroKinds};
use rustc_hir::def_id::{CRATE_DEF_ID, DefId};
use rustc_hir::{MissingLifetimeKind, PrimTy, find_attr};
use rustc_middle::ty;
use rustc_session::{Session, lint};
use rustc_span::edit_distance::{edit_distance, find_best_match_for_name};
use rustc_span::edition::Edition;
use rustc_span::{DUMMY_SP, Ident, Span, Symbol, kw, sym};
use thin_vec::ThinVec;
use tracing::debug;

use super::NoConstantGenericsReason;
use crate::diagnostics::{ImportSuggestion, LabelSuggestion, TypoSuggestion};
use crate::late::{
    AliasPossibility, LateResolutionVisitor, LifetimeBinderKind, LifetimeRes, LifetimeRibKind,
    LifetimeUseSet, QSelf, RibKind,
};
use crate::ty::fast_reject::SimplifiedType;
use crate::{
    Finalize, Module, ModuleKind, ModuleOrUniformRoot, ParentScope, PathResult, PathSource,
    Resolver, ScopeSet, Segment, errors, path_names_to_string,
};
use super::*;

impl<'ast, 'ra, 'tcx> LateResolutionVisitor<'_, 'ast, 'ra, 'tcx> {
    fn trait_assoc_type_def_id_by_name(
        &mut self,
        trait_def_id: DefId,
        assoc_name: Symbol,
    ) -> Option<DefId> {
        let module = self.r.get_module(trait_def_id)?;
        self.r.resolutions(module).borrow().iter().find_map(|(key, resolution)| {
            if key.ident.name != assoc_name {
                return None;
            }
            let resolution = resolution.borrow();
            let binding = resolution.best_decl()?;
            match binding.res() {
                Res::Def(DefKind::AssocTy, def_id) => Some(def_id),
                _ => None,
            }
        })
    }

    /// This does best-effort work to generate suggestions for associated types.
    fn suggest_assoc_type_from_bounds(
        &mut self,
        err: &mut Diag<'_>,
        source: PathSource<'_, 'ast, 'ra>,
        path: &[Segment],
        ident_span: Span,
    ) -> bool {
        // Filter out cases where we cannot emit meaningful suggestions.
        if source.namespace() != TypeNS {
            return false;
        }
        let [segment] = path else { return false };
        if segment.has_generic_args {
            return false;
        }
        if !ident_span.can_be_used_for_suggestions() {
            return false;
        }
        let assoc_name = segment.ident.name;
        if assoc_name == kw::Underscore {
            return false;
        }

        // Map: type parameter name -> (trait def id -> (assoc type def id, trait paths as written)).
        // We keep a set of paths per trait so we can detect cases like
        // `T: Trait<i32> + Trait<u32>` where suggesting `T::Assoc` would be ambiguous.
        let mut matching_bounds: FxIndexMap<
            Symbol,
            FxIndexMap<DefId, (DefId, FxIndexSet<String>)>,
        > = FxIndexMap::default();

        let mut record_bound = |this: &mut Self,
                                ty_param: Symbol,
                                poly_trait_ref: &ast::PolyTraitRef| {
            // Avoid generating suggestions we can't print in a well-formed way.
            if !poly_trait_ref.bound_generic_params.is_empty() {
                return;
            }
            if poly_trait_ref.modifiers != ast::TraitBoundModifiers::NONE {
                return;
            }
            let Some(trait_seg) = poly_trait_ref.trait_ref.path.segments.last() else {
                return;
            };
            let Some(partial_res) = this.r.partial_res_map.get(&trait_seg.id) else {
                return;
            };
            let Some(trait_def_id) = partial_res.full_res().and_then(|res| res.opt_def_id()) else {
                return;
            };
            let Some(assoc_type_def_id) =
                this.trait_assoc_type_def_id_by_name(trait_def_id, assoc_name)
            else {
                return;
            };

            // Preserve `::` and generic args so we don't generate broken suggestions like
            // `<T as Foo>::Assoc` for bounds written as `T: ::Foo<'a>`, while stripping
            // associated-item bindings that are rejected in qualified paths.
            let trait_path =
                path_to_string_without_assoc_item_bindings(&poly_trait_ref.trait_ref.path);
            let trait_bounds = matching_bounds.entry(ty_param).or_default();
            let trait_bounds = trait_bounds
                .entry(trait_def_id)
                .or_insert_with(|| (assoc_type_def_id, FxIndexSet::default()));
            debug_assert_eq!(trait_bounds.0, assoc_type_def_id);
            trait_bounds.1.insert(trait_path);
        };

        let mut record_from_generics = |this: &mut Self, generics: &ast::Generics| {
            for param in &generics.params {
                let ast::GenericParamKind::Type { .. } = param.kind else { continue };
                for bound in &param.bounds {
                    let ast::GenericBound::Trait(poly_trait_ref) = bound else { continue };
                    record_bound(this, param.ident.name, poly_trait_ref);
                }
            }

            for predicate in &generics.where_clause.predicates {
                let ast::WherePredicateKind::BoundPredicate(where_bound) = &predicate.kind else {
                    continue;
                };

                let ast::TyKind::Path(None, bounded_path) = &where_bound.bounded_ty.kind else {
                    continue;
                };
                let [ast::PathSegment { ident, args: None, .. }] = &bounded_path.segments[..]
                else {
                    continue;
                };

                // Only suggest for bounds that are explicitly on an in-scope type parameter.
                let Some(partial_res) = this.r.partial_res_map.get(&where_bound.bounded_ty.id)
                else {
                    continue;
                };
                if !matches!(partial_res.full_res(), Some(Res::Def(DefKind::TyParam, _))) {
                    continue;
                }

                for bound in &where_bound.bounds {
                    let ast::GenericBound::Trait(poly_trait_ref) = bound else { continue };
                    record_bound(this, ident.name, poly_trait_ref);
                }
            }
        };

        if let Some(item) = self.diag_metadata.current_item
            && let Some(generics) = item.kind.generics()
        {
            record_from_generics(self, generics);
        }

        if let Some(item) = self.diag_metadata.current_item
            && matches!(item.kind, ItemKind::Impl(..))
            && let Some(assoc) = self.diag_metadata.current_impl_item
        {
            let generics = match &assoc.kind {
                AssocItemKind::Const(box ast::ConstItem { generics, .. })
                | AssocItemKind::Fn(box ast::Fn { generics, .. })
                | AssocItemKind::Type(box ast::TyAlias { generics, .. }) => Some(generics),
                AssocItemKind::Delegation(..)
                | AssocItemKind::MacCall(..)
                | AssocItemKind::DelegationMac(..) => None,
            };
            if let Some(generics) = generics {
                record_from_generics(self, generics);
            }
        }

        let mut suggestions: FxIndexSet<String> = FxIndexSet::default();
        for (ty_param, traits) in matching_bounds {
            let ty_param = ty_param.to_ident_string();
            let trait_paths_len: usize = traits.values().map(|(_, paths)| paths.len()).sum();
            if traits.len() == 1 && trait_paths_len == 1 {
                let assoc_type_def_id = traits.values().next().expect("invariant: iterator is non-empty").0;
                let assoc_segment = format!(
                    "{}{}",
                    assoc_name,
                    self.r.item_required_generic_args_suggestion(assoc_type_def_id)
                );
                suggestions.insert(format!("{ty_param}::{assoc_segment}"));
            } else {
                for (assoc_type_def_id, trait_paths) in traits.into_values() {
                    let assoc_segment = format!(
                        "{}{}",
                        assoc_name,
                        self.r.item_required_generic_args_suggestion(assoc_type_def_id)
                    );
                    for trait_path in trait_paths {
                        suggestions
                            .insert(format!("<{ty_param} as {trait_path}>::{assoc_segment}"));
                    }
                }
            }
        }

        if suggestions.is_empty() {
            return false;
        }

        let mut suggestions: Vec<String> = suggestions.into_iter().collect();
        suggestions.sort();

        err.span_suggestions_with_style(
            ident_span,
            "you might have meant to use an associated type of the same name",
            suggestions,
            Applicability::MaybeIncorrect,
            SuggestionStyle::ShowAlways,
        );

        true
    }

    fn make_base_error(
        &mut self,
        path: &[Segment],
        span: Span,
        source: PathSource<'_, 'ast, 'ra>,
        res: Option<Res>,
    ) -> BaseError {
        // Make the base error.
        let mut expected = source.descr_expected();
        let path_str = Segment::names_to_string(path);
        let item_str = path.last().expect("invariant: non-empty collection").ident;

        if let Some(res) = res {
            BaseError {
                msg: format!("expected {}, found {} `{}`", expected, res.descr(), path_str),
                fallback_label: format!("not a {expected}"),
                span,
                span_label: match res {
                    Res::Def(DefKind::TyParam, def_id) => {
                        Some((self.r.def_span(def_id), "found this type parameter"))
                    }
                    _ => None,
                },
                could_be_expr: match res {
                    Res::Def(DefKind::Fn, _) => {
                        // Verify whether this is a fn call or an Fn used as a type.
                        self.r
                            .tcx
                            .sess
                            .source_map()
                            .span_to_snippet(span)
                            .is_ok_and(|snippet| snippet.ends_with(')'))
                    }
                    Res::Def(
                        DefKind::Ctor(..)
                        | DefKind::AssocFn
                        | DefKind::Const { .. }
                        | DefKind::AssocConst { .. },
                        _,
                    )
                    | Res::SelfCtor(_)
                    | Res::PrimTy(_)
                    | Res::Local(_) => true,
                    _ => false,
                },
                suggestion: None,
                module: None,
            }
        } else {
            let mut span_label = None;
            let item_ident = path.last().expect("invariant: non-empty collection").ident;
            let item_span = item_ident.span;
            let (mod_prefix, mod_str, module, suggestion) = if path.len() == 1 {
                debug!(?self.diag_metadata.current_impl_items);
                debug!(?self.diag_metadata.current_function);
                let suggestion = if self.current_trait_ref.is_none()
                    && let Some((fn_kind, _)) = self.diag_metadata.current_function
                    && let Some(FnCtxt::Assoc(_)) = fn_kind.ctxt()
                    && let FnKind::Fn(_, _, ast::Fn { sig, .. }) = fn_kind
                    && let Some(items) = self.diag_metadata.current_impl_items
                    && let Some(item) = items.iter().find(|i| {
                        i.kind.ident().is_some_and(|ident| {
                            // Don't suggest if the item is in Fn signature arguments (#112590).
                            ident.name == item_str.name && !sig.span.contains(item_span)
                        })
                    }) {
                    let sp = item_span.shrink_to_lo();

                    // Account for `Foo { field }` when suggesting `self.field` so we result on
                    // `Foo { field: self.field }`.
                    let field = match source {
                        PathSource::Expr(Some(Expr { kind: ExprKind::Struct(expr), .. })) => {
                            expr.fields.iter().find(|f| f.ident == item_ident)
                        }
                        _ => None,
                    };
                    let pre = if let Some(field) = field
                        && field.is_shorthand
                    {
                        format!("{item_ident}: ")
                    } else {
                        String::new()
                    };
                    // Ensure we provide a structured suggestion for an assoc fn only for
                    // expressions that are actually a fn call.
                    let is_call = match field {
                        Some(ast::ExprField { expr, .. }) => {
                            matches!(expr.kind, ExprKind::Call(..))
                        }
                        _ => matches!(
                            source,
                            PathSource::Expr(Some(Expr { kind: ExprKind::Call(..), .. })),
                        ),
                    };

                    match &item.kind {
                        AssocItemKind::Fn(fn_)
                            if (!sig.decl.has_self() || !is_call) && fn_.sig.decl.has_self() =>
                        {
                            // Ensure that we only suggest `self.` if `self` is available,
                            // you can't call `fn foo(&self)` from `fn bar()` (#115992).
                            // We also want to mention that the method exists.
                            span_label = Some((
                                fn_.ident.span,
                                "a method by that name is available on `Self` here",
                            ));
                            None
                        }
                        AssocItemKind::Fn(fn_) if !fn_.sig.decl.has_self() && !is_call => {
                            span_label = Some((
                                fn_.ident.span,
                                "an associated function by that name is available on `Self` here",
                            ));
                            None
                        }
                        AssocItemKind::Fn(fn_) if fn_.sig.decl.has_self() => {
                            Some((sp, "consider using the method on `Self`", format!("{pre}self.")))
                        }
                        AssocItemKind::Fn(_) => Some((
                            sp,
                            "consider using the associated function on `Self`",
                            format!("{pre}Self::"),
                        )),
                        AssocItemKind::Const(..) => Some((
                            sp,
                            "consider using the associated constant on `Self`",
                            format!("{pre}Self::"),
                        )),
                        _ => None,
                    }
                } else {
                    None
                };
                (String::new(), "this scope".to_string(), None, suggestion)
            } else if path.len() == 2 && path[0].ident.name == kw::PathRoot {
                if self.r.tcx.sess.edition() > Edition::Edition2015 {
                    // In edition 2018 onwards, the `::foo` syntax may only pull from the extern prelude
                    // which overrides all other expectations of item type
                    expected = "crate";
                    (String::new(), "the list of imported crates".to_string(), None, None)
                } else {
                    (
                        String::new(),
                        "the crate root".to_string(),
                        Some(CRATE_DEF_ID.to_def_id()),
                        None,
                    )
                }
            } else if path.len() == 2 && path[0].ident.name == kw::Crate {
                (String::new(), "the crate root".to_string(), Some(CRATE_DEF_ID.to_def_id()), None)
            } else {
                let mod_path = &path[..path.len() - 1];
                let mod_res = self.resolve_path(mod_path, Some(TypeNS), None, source);
                let mod_prefix = match mod_res {
                    PathResult::Module(ModuleOrUniformRoot::Module(module)) => module.res(),
                    _ => None,
                };

                let module_did = mod_prefix.as_ref().and_then(Res::mod_def_id);

                let mod_prefix =
                    mod_prefix.map_or_else(String::new, |res| format!("{} ", res.descr()));
                (mod_prefix, format!("`{}`", Segment::names_to_string(mod_path)), module_did, None)
            };

            let (fallback_label, suggestion) = if path_str == "async"
                && expected.starts_with("struct")
            {
                ("`async` blocks are only allowed in Rust 2018 or later".to_string(), suggestion)
            } else {
                // check if we are in situation of typo like `True` instead of `true`.
                let override_suggestion =
                    if ["true", "false"].contains(&item_str.to_string().to_lowercase().as_str()) {
                        let item_typo = item_str.to_string().to_lowercase();
                        Some((item_span, "you may want to use a bool value instead", item_typo))
                    // NOTE(vincenzopalazzo): make the check smarter,
                    // and maybe expand with levenshtein distance checks
                    } else if item_str.as_str() == "printf" {
                        Some((
                            item_span,
                            "you may have meant to use the `print` macro",
                            "print!".to_owned(),
                        ))
                    } else {
                        suggestion
                    };
                (format!("not found in {mod_str}"), override_suggestion)
            };

            BaseError {
                msg: format!("cannot find {expected} `{item_str}` in {mod_prefix}{mod_str}"),
                fallback_label,
                span: item_span,
                span_label,
                could_be_expr: false,
                suggestion,
                module,
            }
        }
    }

    /// Try to suggest for a module path that cannot be resolved.
    /// Such as `fmt::Debug` where `fmt` is not resolved without importing,
    /// here we search with `lookup_import_candidates` for a module named `fmt`
    /// with `TypeNS` as namespace.
    ///
    /// We need a separate function here because we won't suggest for a path with single segment
    /// and we won't change `SourcePath` api `is_expected` to match `Type` with `DefKind::Mod`
    pub(crate) fn smart_resolve_partial_mod_path_errors(
        &mut self,
        prefix_path: &[Segment],
        following_seg: Option<&Segment>,
    ) -> Vec<ImportSuggestion> {
        if let Some(segment) = prefix_path.last()
            && let Some(following_seg) = following_seg
        {
            let candidates = self.r.lookup_import_candidates(
                segment.ident,
                Namespace::TypeNS,
                &self.parent_scope,
                &|res: Res| matches!(res, Res::Def(DefKind::Mod, _)),
            );
            // double check next seg is valid
            candidates
                .into_iter()
                .filter(|candidate| {
                    if let Some(def_id) = candidate.did
                        && let Some(module) = self.r.get_module(def_id)
                    {
                        Some(def_id) != self.parent_scope.module.opt_def_id()
                            && self
                                .r
                                .resolutions(module)
                                .borrow()
                                .iter()
                                .any(|(key, _r)| key.ident.name == following_seg.ident.name)
                    } else {
                        false
                    }
                })
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        }
    }

    /// Handles error reporting for `smart_resolve_path_fragment` function.
    /// Creates base error and amends it with one short label and possibly some longer helps/notes.
    #[tracing::instrument(skip(self), level = "debug")]
    pub(crate) fn smart_resolve_report_errors(
        &mut self,
        path: &[Segment],
        following_seg: Option<&Segment>,
        span: Span,
        source: PathSource<'_, 'ast, 'ra>,
        res: Option<Res>,
        qself: Option<&QSelf>,
    ) -> (Diag<'tcx>, Vec<ImportSuggestion>) {
        debug!(?res, ?source);
        let base_error = self.make_base_error(path, span, source, res);

        let code = source.error_code(res.is_some());
        let mut err = self.r.dcx().struct_span_err(base_error.span, base_error.msg.clone());
        err.code(code);

        // Try to get the span of the identifier within the path's syntax context
        // (if that's different).
        if let Some(within_macro_span) =
            base_error.span.within_macro(span, self.r.tcx.sess.source_map())
        {
            err.span_label(within_macro_span, "due to this macro variable");
        }

        self.detect_missing_binding_available_from_pattern(&mut err, path, following_seg);
        self.suggest_at_operator_in_slice_pat_with_range(&mut err, path);
        self.suggest_range_struct_destructuring(&mut err, path, source);
        self.suggest_swapping_misplaced_self_ty_and_trait(&mut err, source, res, base_error.span);

        if let Some((span, label)) = base_error.span_label {
            err.span_label(span, label);
        }

        if let Some(ref sugg) = base_error.suggestion {
            err.span_suggestion_verbose(sugg.0, sugg.1, &sugg.2, Applicability::MaybeIncorrect);
        }

        self.suggest_changing_type_to_const_param(&mut err, res, source, path, following_seg, span);
        self.explain_functions_in_pattern(&mut err, res, source);

        if self.suggest_pattern_match_with_let(&mut err, source, span) {
            // Fallback label.
            err.span_label(base_error.span, base_error.fallback_label);
            return (err, Vec::new());
        }

        self.suggest_self_or_self_ref(&mut err, path, span);
        self.detect_assoc_type_constraint_meant_as_path(&mut err, &base_error);
        self.detect_rtn_with_fully_qualified_path(
            &mut err,
            path,
            following_seg,
            span,
            source,
            res,
            qself,
        );
        if self.suggest_self_ty(&mut err, source, path, span)
            || self.suggest_self_value(&mut err, source, path, span)
        {
            return (err, Vec::new());
        }

        if let Some((did, item)) = self.lookup_doc_alias_name(path, source.namespace()) {
            let item_name = item.name;
            let suggestion_name = self.r.tcx.item_name(did);
            err.span_suggestion(
                item.span,
                format!("`{suggestion_name}` has a name defined in the doc alias attribute as `{item_name}`"),
                    suggestion_name,
                    Applicability::MaybeIncorrect
                );

            return (err, Vec::new());
        };

        let (found, suggested_candidates, mut candidates) = self.try_lookup_name_relaxed(
            &mut err,
            source,
            path,
            following_seg,
            span,
            res,
            &base_error,
        );
        if found {
            return (err, candidates);
        }

        if self.suggest_shadowed(&mut err, source, path, following_seg, span) {
            // if there is already a shadowed name, don'suggest candidates for importing
            candidates.clear();
        }

        let mut fallback = self.suggest_trait_and_bounds(&mut err, source, res, span, &base_error);
        fallback |= self.suggest_typo(
            &mut err,
            source,
            path,
            following_seg,
            span,
            &base_error,
            suggested_candidates,
        );

        if fallback {
            // Fallback label.
            err.span_label(base_error.span, base_error.fallback_label);
        }
        self.err_code_special_cases(&mut err, source, path, span);

        let module = base_error.module.unwrap_or_else(|| CRATE_DEF_ID.to_def_id());
        self.r.find_cfg_stripped(&mut err, &path.last().expect("invariant: non-empty collection").ident.name, module);

        (err, candidates)
    }

    fn detect_rtn_with_fully_qualified_path(
        &self,
        err: &mut Diag<'_>,
        path: &[Segment],
        following_seg: Option<&Segment>,
        span: Span,
        source: PathSource<'_, '_, '_>,
        res: Option<Res>,
        qself: Option<&QSelf>,
    ) {
        if let Some(Res::Def(DefKind::AssocFn, _)) = res
            && let PathSource::TraitItem(TypeNS, _) = source
            && let None = following_seg
            && let Some(qself) = qself
            && let TyKind::Path(None, ty_path) = &qself.ty.kind
            && ty_path.segments.len() == 1
            && self.diag_metadata.current_where_predicate.is_some()
        {
            err.span_suggestion_verbose(
                span,
                "you might have meant to use the return type notation syntax",
                format!("{}::{}(..)", ty_path.segments[0].ident, path[path.len() - 1].ident),
                Applicability::MaybeIncorrect,
            );
        }
    }

    fn detect_assoc_type_constraint_meant_as_path(
        &self,
        err: &mut Diag<'_>,
        base_error: &BaseError,
    ) {
        let Some(ty) = self.diag_metadata.current_type_path else {
            return;
        };
        let TyKind::Path(_, path) = &ty.kind else {
            return;
        };
        for segment in &path.segments {
            let Some(params) = &segment.args else {
                continue;
            };
            let ast::GenericArgs::AngleBracketed(params) = params.deref() else {
                continue;
            };
            for param in &params.args {
                let ast::AngleBracketedArg::Constraint(constraint) = param else {
                    continue;
                };
                let ast::AssocItemConstraintKind::Bound { bounds } = &constraint.kind else {
                    continue;
                };
                for bound in bounds {
                    let ast::GenericBound::Trait(trait_ref) = bound else {
                        continue;
                    };
                    if trait_ref.modifiers == ast::TraitBoundModifiers::NONE
                        && base_error.span == trait_ref.span
                    {
                        err.span_suggestion_verbose(
                            constraint.ident.span.between(trait_ref.span),
                            "you might have meant to write a path instead of an associated type bound",
                            "::",
                            Applicability::MachineApplicable,
                        );
                    }
                }
            }
        }
    }

    fn suggest_self_or_self_ref(&mut self, err: &mut Diag<'_>, path: &[Segment], span: Span) {
        if !self.self_type_is_available() {
            return;
        }
        let Some(path_last_segment) = path.last() else { return };
        let item_str = path_last_segment.ident;
        // Emit help message for fake-self from other languages (e.g., `this` in JavaScript).
        if ["this", "my"].contains(&item_str.as_str()) {
            err.span_suggestion_short(
                span,
                "you might have meant to use `self` here instead",
                "self",
                Applicability::MaybeIncorrect,
            );
            if !self.self_value_is_available(path[0].ident.span) {
                if let Some((FnKind::Fn(_, _, ast::Fn { sig, .. }), fn_span)) =
                    &self.diag_metadata.current_function
                {
                    let (span, sugg) = if let Some(param) = sig.decl.inputs.get(0) {
                        (param.span.shrink_to_lo(), "&self, ")
                    } else {
                        (
                            self.r
                                .tcx
                                .sess
                                .source_map()
                                .span_through_char(*fn_span, '(')
                                .shrink_to_hi(),
                            "&self",
                        )
                    };
                    err.span_suggestion_verbose(
                        span,
                        "if you meant to use `self`, you are also missing a `self` receiver \
                         argument",
                        sugg,
                        Applicability::MaybeIncorrect,
                    );
                }
            }
        }
    }

    fn try_lookup_name_relaxed(
        &mut self,
        err: &mut Diag<'_>,
        source: PathSource<'_, '_, '_>,
        path: &[Segment],
        following_seg: Option<&Segment>,
        span: Span,
        res: Option<Res>,
        base_error: &BaseError,
    ) -> (bool, FxHashSet<String>, Vec<ImportSuggestion>) {
        let span = match following_seg {
            Some(_) if path[0].ident.span.eq_ctxt(path[path.len() - 1].ident.span) => {
                // The path `span` that comes in includes any following segments, which we don't
                // want to replace in the suggestions.
                path[0].ident.span.to(path[path.len() - 1].ident.span)
            }
            _ => span,
        };
        let mut suggested_candidates = FxHashSet::default();
        // Try to lookup name in more relaxed fashion for better error reporting.
        let ident = path.last().expect("invariant: non-empty collection").ident;
        let is_expected = &|res| source.is_expected(res);
        let ns = source.namespace();
        let is_enum_variant = &|res| matches!(res, Res::Def(DefKind::Variant, _));
        let path_str = Segment::names_to_string(path);
        let ident_span = path.last().map_or(span, |ident| ident.ident.span);
        let mut candidates = self
            .r
            .lookup_import_candidates(ident, ns, &self.parent_scope, is_expected)
            .into_iter()
            .filter(|ImportSuggestion { did, .. }| {
                match (did, res.and_then(|res| res.opt_def_id())) {
                    (Some(suggestion_did), Some(actual_did)) => *suggestion_did != actual_did,
                    _ => true,
                }
            })
            .collect::<Vec<_>>();
        // Try to filter out intrinsics candidates, as long as we have
        // some other candidates to suggest.
        let intrinsic_candidates: Vec<_> = candidates
            .extract_if(.., |sugg| {
                let path = path_names_to_string(&sugg.path);
                path.starts_with("core::intrinsics::") || path.starts_with("std::intrinsics::")
            })
            .collect();
        if candidates.is_empty() {
            // Put them back if we have no more candidates to suggest...
            candidates = intrinsic_candidates;
        }
        let crate_def_id = CRATE_DEF_ID.to_def_id();
        if candidates.is_empty() && is_expected(Res::Def(DefKind::Enum, crate_def_id)) {
            let mut enum_candidates: Vec<_> = self
                .r
                .lookup_import_candidates(ident, ns, &self.parent_scope, is_enum_variant)
                .into_iter()
                .map(|suggestion| import_candidate_to_enum_paths(&suggestion))
                .filter(|(_, enum_ty_path)| !enum_ty_path.starts_with("std::prelude::"))
                .collect();
            if !enum_candidates.is_empty() {
                enum_candidates.sort();

                // Contextualize for E0425 "cannot find type", but don't belabor the point
                // (that it's a variant) for E0573 "expected type, found variant".
                let preamble = if res.is_none() {
                    let others = match enum_candidates.len() {
                        1 => String::new(),
                        2 => " and 1 other".to_owned(),
                        n => format!(" and {n} others"),
                    };
                    format!("there is an enum variant `{}`{}; ", enum_candidates[0].0, others)
                } else {
                    String::new()
                };
                let msg = format!("{preamble}try using the variant's enum");

                suggested_candidates.extend(
                    enum_candidates
                        .iter()
                        .map(|(_variant_path, enum_ty_path)| enum_ty_path.clone()),
                );
                err.span_suggestions(
                    span,
                    msg,
                    enum_candidates.into_iter().map(|(_variant_path, enum_ty_path)| enum_ty_path),
                    Applicability::MachineApplicable,
                );
            }
        }

        // Try finding a suitable replacement.
        let typo_sugg = self
            .lookup_typo_candidate(path, following_seg, source.namespace(), is_expected)
            .to_opt_suggestion()
            .filter(|sugg| !suggested_candidates.contains(sugg.candidate.as_str()));
        if let [segment] = path
            && !matches!(source, PathSource::Delegation)
            && self.self_type_is_available()
        {
            if let Some(candidate) =
                self.lookup_assoc_candidate(ident, ns, is_expected, source.is_call())
            {
                let self_is_available = self.self_value_is_available(segment.ident.span);
                // Account for `Foo { field }` when suggesting `self.field` so we result on
                // `Foo { field: self.field }`.
                let pre = match source {
                    PathSource::Expr(Some(Expr { kind: ExprKind::Struct(expr), .. }))
                        if expr
                            .fields
                            .iter()
                            .any(|f| f.ident == segment.ident && f.is_shorthand) =>
                    {
                        format!("{path_str}: ")
                    }
                    _ => String::new(),
                };
                match candidate {
                    AssocSuggestion::Field(field_span) => {
                        if self_is_available {
                            let source_map = self.r.tcx.sess.source_map();
                            // check if the field is used in a format string, such as `"{x}"`
                            let field_is_format_named_arg = source_map
                                .span_to_source(span, |s, start, _| {
                                    Ok(s.get(start - 1..start) == Some("{"))
                                });
                            if let Ok(true) = field_is_format_named_arg {
                                err.help(
                                    format!("you might have meant to use the available field in a format string: `\"{{}}\", self.{}`", segment.ident.name),
                                );
                            } else {
                                err.span_suggestion_verbose(
                                    span.shrink_to_lo(),
                                    "you might have meant to use the available field",
                                    format!("{pre}self."),
                                    Applicability::MaybeIncorrect,
                                );
                            }
                        } else {
                            err.span_label(field_span, "a field by that name exists in `Self`");
                        }
                    }
                    AssocSuggestion::MethodWithSelf { called } if self_is_available => {
                        let msg = if called {
                            "you might have meant to call the method"
                        } else {
                            "you might have meant to refer to the method"
                        };
                        err.span_suggestion_verbose(
                            span.shrink_to_lo(),
                            msg,
                            "self.",
                            Applicability::MachineApplicable,
                        );
                    }
                    AssocSuggestion::MethodWithSelf { .. }
                    | AssocSuggestion::AssocFn { .. }
                    | AssocSuggestion::AssocConst
                    | AssocSuggestion::AssocType => {
                        err.span_suggestion_verbose(
                            span.shrink_to_lo(),
                            format!("you might have meant to {}", candidate.action()),
                            "Self::",
                            Applicability::MachineApplicable,
                        );
                    }
                }
                self.r.add_typo_suggestion(err, typo_sugg, ident_span);
                return (true, suggested_candidates, candidates);
            }

            // If the first argument in call is `self` suggest calling a method.
            if let Some((call_span, args_span)) = self.call_has_self_arg(source) {
                let mut args_snippet = String::new();
                if let Some(args_span) = args_span
                    && let Ok(snippet) = self.r.tcx.sess.source_map().span_to_snippet(args_span)
                {
                    args_snippet = snippet;
                }

                if let Some(Res::Def(DefKind::Struct, def_id)) = res {
                    let private_fields = self.has_private_fields(def_id);
                    let adjust_error_message =
                        private_fields && self.is_struct_with_fn_ctor(def_id);
                    if adjust_error_message {
                        self.update_err_for_private_tuple_struct_fields(err, &source, def_id);
                    }

                    if private_fields {
                        err.note("constructor is not visible here due to private fields");
                    }
                } else {
                    err.span_suggestion(
                        call_span,
                        format!("try calling `{ident}` as a method"),
                        format!("self.{path_str}({args_snippet})"),
                        Applicability::MachineApplicable,
                    );
                }

                return (true, suggested_candidates, candidates);
            }
        }

        // Try context-dependent help if relaxed lookup didn't work.
        if let Some(res) = res {
            if self.smart_resolve_context_dependent_help(
                err,
                span,
                source,
                path,
                res,
                &path_str,
                &base_error.fallback_label,
            ) {
                // We do this to avoid losing a secondary span when we override the main error span.
                self.r.add_typo_suggestion(err, typo_sugg, ident_span);
                return (true, suggested_candidates, candidates);
            }
        }

        // Try to find in last block rib
        if let Some(rib) = &self.last_block_rib {
            for (ident, &res) in &rib.bindings {
                if let Res::Local(_) = res
                    && path.len() == 1
                    && ident.span.eq_ctxt(path[0].ident.span)
                    && ident.name == path[0].ident.name
                {
                    err.span_help(
                        ident.span,
                        format!("the binding `{path_str}` is available in a different scope in the same function"),
                    );
                    return (true, suggested_candidates, candidates);
                }
            }
        }

        if candidates.is_empty() {
            candidates = self.smart_resolve_partial_mod_path_errors(path, following_seg);
        }

        (false, suggested_candidates, candidates)
    }

}
