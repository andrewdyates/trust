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
    fn lookup_doc_alias_name(&mut self, path: &[Segment], ns: Namespace) -> Option<(DefId, Ident)> {
        let find_doc_alias_name = |r: &mut Resolver<'ra, '_>, m: Module<'ra>, item_name: Symbol| {
            for resolution in r.resolutions(m).borrow().values() {
                let Some(did) =
                    resolution.borrow().best_decl().and_then(|binding| binding.res().opt_def_id())
                else {
                    continue;
                };
                if did.is_local() {
                    // We don't record the doc alias name in the local crate
                    // because the people who write doc alias are usually not
                    // confused by them.
                    continue;
                }
                if let Some(d) = hir::find_attr!(r.tcx, did, Doc(d) => d)
                    && d.aliases.contains_key(&item_name)
                {
                    return Some(did);
                }
            }
            None
        };

        if path.len() == 1 {
            for rib in self.ribs[ns].iter().rev() {
                let item = path[0].ident;
                if let RibKind::Module(module) | RibKind::Block(Some(module)) = rib.kind
                    && let Some(did) = find_doc_alias_name(self.r, module, item.name)
                {
                    return Some((did, item));
                }
            }
        } else {
            // Finds to the last resolved module item in the path
            // and searches doc aliases within that module.
            //
            // Example: For the path `a::b::last_resolved::not_exist::c::d`,
            // we will try to find any item has doc aliases named `not_exist`
            // in `last_resolved` module.
            //
            // - Use `skip(1)` because the final segment must remain unresolved.
            for (idx, seg) in path.iter().enumerate().rev().skip(1) {
                let Some(id) = seg.id else {
                    continue;
                };
                let Some(res) = self.r.partial_res_map.get(&id) else {
                    continue;
                };
                if let Res::Def(DefKind::Mod, module) = res.expect_full_res()
                    && let module = self.r.expect_module(module)
                    && let item = path[idx + 1].ident
                    && let Some(did) = find_doc_alias_name(self.r, module, item.name)
                {
                    return Some((did, item));
                }
                break;
            }
        }
        None
    }

    fn suggest_trait_and_bounds(
        &self,
        err: &mut Diag<'_>,
        source: PathSource<'_, '_, '_>,
        res: Option<Res>,
        span: Span,
        base_error: &BaseError,
    ) -> bool {
        let is_macro =
            base_error.span.from_expansion() && base_error.span.desugaring_kind().is_none();
        let mut fallback = false;

        if let (
            PathSource::Trait(AliasPossibility::Maybe),
            Some(Res::Def(DefKind::Struct | DefKind::Enum | DefKind::Union, _)),
            false,
        ) = (source, res, is_macro)
            && let Some(bounds @ [first_bound, .., last_bound]) =
                self.diag_metadata.current_trait_object
        {
            fallback = true;
            let spans: Vec<Span> = bounds
                .iter()
                .map(|bound| bound.span())
                .filter(|&sp| sp != base_error.span)
                .collect();

            let start_span = first_bound.span();
            // `end_span` is the end of the poly trait ref (Foo + 'baz + Bar><)
            let end_span = last_bound.span();
            // `last_bound_span` is the last bound of the poly trait ref (Foo + >'baz< + Bar)
            let last_bound_span = spans.last().cloned().expect("invariant: value is present");
            let mut multi_span: MultiSpan = spans.clone().into();
            for sp in spans {
                let msg = if sp == last_bound_span {
                    format!(
                        "...because of {these} bound{s}",
                        these = pluralize!("this", bounds.len() - 1),
                        s = pluralize!(bounds.len() - 1),
                    )
                } else {
                    String::new()
                };
                multi_span.push_span_label(sp, msg);
            }
            multi_span.push_span_label(base_error.span, "expected this type to be a trait...");
            err.span_help(
                multi_span,
                "`+` is used to constrain a \"trait object\" type with lifetimes or \
                        auto-traits; structs and enums can't be bound in that way",
            );
            if bounds.iter().all(|bound| match bound {
                ast::GenericBound::Outlives(_) | ast::GenericBound::Use(..) => true,
                ast::GenericBound::Trait(tr) => tr.span == base_error.span,
            }) {
                let mut sugg = vec![];
                if base_error.span != start_span {
                    sugg.push((start_span.until(base_error.span), String::new()));
                }
                if base_error.span != end_span {
                    sugg.push((base_error.span.shrink_to_hi().to(end_span), String::new()));
                }

                err.multipart_suggestion(
                    "if you meant to use a type and not a trait here, remove the bounds",
                    sugg,
                    Applicability::MaybeIncorrect,
                );
            }
        }

        fallback |= self.restrict_assoc_type_in_where_clause(span, err);
        fallback
    }

    fn suggest_typo(
        &mut self,
        err: &mut Diag<'_>,
        source: PathSource<'_, 'ast, 'ra>,
        path: &[Segment],
        following_seg: Option<&Segment>,
        span: Span,
        base_error: &BaseError,
        suggested_candidates: FxHashSet<String>,
    ) -> bool {
        let is_expected = &|res| source.is_expected(res);
        let ident_span = path.last().map_or(span, |ident| ident.ident.span);

        // Prefer suggestions based on associated types from in-scope bounds (e.g. `T::Item`)
        // over purely edit-distance-based identifier suggestions.
        // Otherwise suggestions could be verbose.
        if self.suggest_assoc_type_from_bounds(err, source, path, ident_span) {
            return false;
        }

        let typo_sugg =
            self.lookup_typo_candidate(path, following_seg, source.namespace(), is_expected);
        let mut fallback = false;
        let typo_sugg = typo_sugg
            .to_opt_suggestion()
            .filter(|sugg| !suggested_candidates.contains(sugg.candidate.as_str()));
        if !self.r.add_typo_suggestion(err, typo_sugg, ident_span) {
            fallback = true;
            match self.diag_metadata.current_let_binding {
                Some((pat_sp, Some(ty_sp), None))
                    if ty_sp.contains(base_error.span) && base_error.could_be_expr =>
                {
                    err.span_suggestion_verbose(
                        pat_sp.between(ty_sp),
                        "use `=` if you meant to assign",
                        " = ",
                        Applicability::MaybeIncorrect,
                    );
                }
                _ => {}
            }

            // If the trait has a single item (which wasn't matched by the algorithm), suggest it
            let suggestion = self.get_single_associated_item(path, &source, is_expected);
            self.r.add_typo_suggestion(err, suggestion, ident_span);
        }

        if self.let_binding_suggestion(err, ident_span) {
            fallback = false;
        }

        fallback
    }

    fn suggest_shadowed(
        &mut self,
        err: &mut Diag<'_>,
        source: PathSource<'_, '_, '_>,
        path: &[Segment],
        following_seg: Option<&Segment>,
        span: Span,
    ) -> bool {
        let is_expected = &|res| source.is_expected(res);
        let typo_sugg =
            self.lookup_typo_candidate(path, following_seg, source.namespace(), is_expected);
        let is_in_same_file = &|sp1, sp2| {
            let source_map = self.r.tcx.sess.source_map();
            let file1 = source_map.span_to_filename(sp1);
            let file2 = source_map.span_to_filename(sp2);
            file1 == file2
        };
        // print 'you might have meant' if the candidate is (1) is a shadowed name with
        // accessible definition and (2) either defined in the same crate as the typo
        // (could be in a different file) or introduced in the same file as the typo
        // (could belong to a different crate)
        if let TypoCandidate::Shadowed(res, Some(sugg_span)) = typo_sugg
            && res.opt_def_id().is_some_and(|id| id.is_local() || is_in_same_file(span, sugg_span))
        {
            err.span_label(
                sugg_span,
                format!("you might have meant to refer to this {}", res.descr()),
            );
            return true;
        }
        false
    }

    fn err_code_special_cases(
        &mut self,
        err: &mut Diag<'_>,
        source: PathSource<'_, '_, '_>,
        path: &[Segment],
        span: Span,
    ) {
        if let Some(err_code) = err.code {
            if err_code == E0425 {
                for label_rib in &self.label_ribs {
                    for (label_ident, node_id) in &label_rib.bindings {
                        let ident = path.last().expect("invariant: non-empty collection").ident;
                        if format!("'{ident}") == label_ident.to_string() {
                            err.span_label(label_ident.span, "a label with a similar name exists");
                            if let PathSource::Expr(Some(Expr {
                                kind: ExprKind::Break(None, Some(_)),
                                ..
                            })) = source
                            {
                                err.span_suggestion(
                                    span,
                                    "use the similarly named label",
                                    label_ident.name,
                                    Applicability::MaybeIncorrect,
                                );
                                // Do not lint against unused label when we suggest them.
                                self.diag_metadata.unused_labels.swap_remove(node_id);
                            }
                        }
                    }
                }

                self.suggest_ident_hidden_by_hygiene(err, path, span);
                // cannot find type in this scope
                if let Some(correct) = Self::likely_rust_type(path) {
                    err.span_suggestion(
                        span,
                        "perhaps you intended to use this type",
                        correct,
                        Applicability::MaybeIncorrect,
                    );
                }
            }
        }
    }

    fn suggest_ident_hidden_by_hygiene(&self, err: &mut Diag<'_>, path: &[Segment], span: Span) {
        let [segment] = path else { return };

        let ident = segment.ident;
        let callsite_span = span.source_callsite();
        for rib in self.ribs[ValueNS].iter().rev() {
            for (binding_ident, _) in &rib.bindings {
                // Case 1: the identifier is defined in the same scope as the macro is called
                if binding_ident.name == ident.name
                    && !binding_ident.span.eq_ctxt(span)
                    && !binding_ident.span.from_expansion()
                    && binding_ident.span.lo() < callsite_span.lo()
                {
                    err.span_help(
                        binding_ident.span,
                        "an identifier with the same name exists, but is not accessible due to macro hygiene",
                    );
                    return;
                }

                // Case 2: the identifier is defined in a macro call in the same scope
                if binding_ident.name == ident.name
                    && binding_ident.span.from_expansion()
                    && binding_ident.span.source_callsite().eq_ctxt(callsite_span)
                    && binding_ident.span.source_callsite().lo() < callsite_span.lo()
                {
                    err.span_help(
                        binding_ident.span,
                        "an identifier with the same name is defined here, but is not accessible due to macro hygiene",
                    );
                    return;
                }
            }
        }
    }

    /// Emit special messages for unresolved `Self` and `self`.
    fn suggest_self_ty(
        &self,
        err: &mut Diag<'_>,
        source: PathSource<'_, '_, '_>,
        path: &[Segment],
        span: Span,
    ) -> bool {
        if !is_self_type(path, source.namespace()) {
            return false;
        }
        err.code(E0411);
        err.span_label(span, "`Self` is only available in impls, traits, and type definitions");
        if let Some(item) = self.diag_metadata.current_item
            && let Some(ident) = item.kind.ident()
        {
            err.span_label(
                ident.span,
                format!("`Self` not allowed in {} {}", item.kind.article(), item.kind.descr()),
            );
        }
        true
    }

    fn suggest_self_value(
        &mut self,
        err: &mut Diag<'_>,
        source: PathSource<'_, '_, '_>,
        path: &[Segment],
        span: Span,
    ) -> bool {
        if !is_self_value(path, source.namespace()) {
            return false;
        }

        debug!("smart_resolve_path_fragment: E0424, source={:?}", source);
        err.code(E0424);
        err.span_label(
            span,
            match source {
                PathSource::Pat => {
                    "`self` value is a keyword and may not be bound to variables or shadowed"
                }
                _ => "`self` value is a keyword only available in methods with a `self` parameter",
            },
        );

        // using `let self` is wrong even if we're not in an associated method or if we're in a macro expansion.
        // So, we should return early if we're in a pattern, see issue #143134.
        if matches!(source, PathSource::Pat) {
            return true;
        }

        let is_assoc_fn = self.self_type_is_available();
        let self_from_macro = "a `self` parameter, but a macro invocation can only \
                               access identifiers it receives from parameters";
        if let Some((fn_kind, fn_span)) = &self.diag_metadata.current_function {
            // The current function has a `self` parameter, but we were unable to resolve
            // a reference to `self`. This can only happen if the `self` identifier we
            // are resolving came from a different hygiene context or a variable binding.
            // But variable binding error is returned early above.
            if fn_kind.decl().inputs.get(0).is_some_and(|p| p.is_self()) {
                err.span_label(*fn_span, format!("this function has {self_from_macro}"));
            } else {
                let doesnt = if is_assoc_fn {
                    let (span, sugg) = fn_kind
                        .decl()
                        .inputs
                        .get(0)
                        .map(|p| (p.span.shrink_to_lo(), "&self, "))
                        .unwrap_or_else(|| {
                            // Try to look for the "(" after the function name, if possible.
                            // This avoids placing the suggestion into the visibility specifier.
                            let span = fn_kind
                                .ident()
                                .map_or(*fn_span, |ident| fn_span.with_lo(ident.span.hi()));
                            (
                                self.r
                                    .tcx
                                    .sess
                                    .source_map()
                                    .span_through_char(span, '(')
                                    .shrink_to_hi(),
                                "&self",
                            )
                        });
                    err.span_suggestion_verbose(
                        span,
                        "add a `self` receiver parameter to make the associated `fn` a method",
                        sugg,
                        Applicability::MaybeIncorrect,
                    );
                    "doesn't"
                } else {
                    "can't"
                };
                if let Some(ident) = fn_kind.ident() {
                    err.span_label(
                        ident.span,
                        format!("this function {doesnt} have a `self` parameter"),
                    );
                }
            }
        } else if let Some(item) = self.diag_metadata.current_item {
            if matches!(item.kind, ItemKind::Delegation(..)) {
                err.span_label(item.span, format!("delegation supports {self_from_macro}"));
            } else {
                let span = if let Some(ident) = item.kind.ident() { ident.span } else { item.span };
                err.span_label(
                    span,
                    format!("`self` not allowed in {} {}", item.kind.article(), item.kind.descr()),
                );
            }
        }
        true
    }

    fn detect_missing_binding_available_from_pattern(
        &self,
        err: &mut Diag<'_>,
        path: &[Segment],
        following_seg: Option<&Segment>,
    ) {
        let [segment] = path else { return };
        let None = following_seg else { return };
        for rib in self.ribs[ValueNS].iter().rev() {
            let patterns_with_skipped_bindings = self.r.tcx.with_stable_hashing_context(|hcx| {
                rib.patterns_with_skipped_bindings.to_sorted(&hcx, true)
            });
            for (def_id, spans) in patterns_with_skipped_bindings {
                if let DefKind::Struct | DefKind::Variant = self.r.tcx.def_kind(*def_id)
                    && let Some(fields) = self.r.field_idents(*def_id)
                {
                    for field in fields {
                        if field.name == segment.ident.name {
                            if spans.iter().all(|(_, had_error)| had_error.is_err()) {
                                // This resolution error will likely be fixed by fixing a
                                // syntax error in a pattern, so it is irrelevant to the user.
                                let multispan: MultiSpan =
                                    spans.iter().map(|(s, _)| *s).collect::<Vec<_>>().into();
                                err.span_note(
                                    multispan,
                                    "this pattern had a recovered parse error which likely lost \
                                     the expected fields",
                                );
                                err.downgrade_to_delayed_bug();
                            }
                            let ty = self.r.tcx.item_name(*def_id);
                            for (span, _) in spans {
                                err.span_label(
                                    *span,
                                    format!(
                                        "this pattern doesn't include `{field}`, which is \
                                         available in `{ty}`",
                                    ),
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    fn suggest_at_operator_in_slice_pat_with_range(&self, err: &mut Diag<'_>, path: &[Segment]) {
        let Some(pat) = self.diag_metadata.current_pat else { return };
        let (bound, side, range) = match &pat.kind {
            ast::PatKind::Range(Some(bound), None, range) => (bound, Side::Start, range),
            ast::PatKind::Range(None, Some(bound), range) => (bound, Side::End, range),
            _ => return,
        };
        if let ExprKind::Path(None, range_path) = &bound.kind
            && let [segment] = &range_path.segments[..]
            && let [s] = path
            && segment.ident == s.ident
            && segment.ident.span.eq_ctxt(range.span)
        {
            // We've encountered `[first, rest..]` (#88404) or `[first, ..rest]` (#120591)
            // where the user might have meant `[first, rest @ ..]`.
            let (span, snippet) = match side {
                Side::Start => (segment.ident.span.between(range.span), " @ ".into()),
                Side::End => (range.span.to(segment.ident.span), format!("{} @ ..", segment.ident)),
            };
            err.subdiagnostic(errors::UnexpectedResUseAtOpInSlicePatWithRangeSugg {
                span,
                ident: segment.ident,
                snippet,
            });
        }

        enum Side {
            Start,
            End,
        }
    }

    fn suggest_range_struct_destructuring(
        &mut self,
        err: &mut Diag<'_>,
        path: &[Segment],
        source: PathSource<'_, '_, '_>,
    ) {
        if !matches!(source, PathSource::Pat | PathSource::TupleStruct(..) | PathSource::Expr(..)) {
            return;
        }

        let Some(pat) = self.diag_metadata.current_pat else { return };
        let ast::PatKind::Range(start, end, end_kind) = &pat.kind else { return };

        let [segment] = path else { return };
        let failing_span = segment.ident.span;

        let in_start = start.as_ref().is_some_and(|e| e.span.contains(failing_span));
        let in_end = end.as_ref().is_some_and(|e| e.span.contains(failing_span));

        if !in_start && !in_end {
            return;
        }

        let start_snippet =
            start.as_ref().and_then(|e| self.r.tcx.sess.source_map().span_to_snippet(e.span).ok());
        let end_snippet =
            end.as_ref().and_then(|e| self.r.tcx.sess.source_map().span_to_snippet(e.span).ok());

        let field = |name: &str, val: String| {
            if val == name { val } else { format!("{name}: {val}") }
        };

        let mut resolve_short_name = |short: Symbol, full: &str| -> String {
            let ident = Ident::with_dummy_span(short);
            let path = Segment::from_path(&Path::from_ident(ident));

            match self.resolve_path(&path, Some(TypeNS), None, PathSource::Type) {
                PathResult::NonModule(..) => short.to_string(),
                _ => full.to_string(),
            }
        };
        // NOTE(new_range): also account for new range types
        let (struct_path, fields) = match (start_snippet, end_snippet, &end_kind.node) {
            (Some(start), Some(end), ast::RangeEnd::Excluded) => (
                resolve_short_name(sym::Range, "std::ops::Range"),
                vec![field("start", start), field("end", end)],
            ),
            (Some(start), Some(end), ast::RangeEnd::Included(_)) => (
                resolve_short_name(sym::RangeInclusive, "std::ops::RangeInclusive"),
                vec![field("start", start), field("end", end)],
            ),
            (Some(start), None, _) => (
                resolve_short_name(sym::RangeFrom, "std::ops::RangeFrom"),
                vec![field("start", start)],
            ),
            (None, Some(end), ast::RangeEnd::Excluded) => {
                (resolve_short_name(sym::RangeTo, "std::ops::RangeTo"), vec![field("end", end)])
            }
            (None, Some(end), ast::RangeEnd::Included(_)) => (
                resolve_short_name(sym::RangeToInclusive, "std::ops::RangeToInclusive"),
                vec![field("end", end)],
            ),
            _ => return,
        };

        err.span_suggestion_verbose(
            pat.span,
            format!("if you meant to destructure a range use a struct pattern"),
            format!("{} {{ {} }}", struct_path, fields.join(", ")),
            Applicability::MaybeIncorrect,
        );

        err.note(
            "range patterns match against the start and end of a range; \
             to bind the components, use a struct pattern",
        );
    }

    fn suggest_swapping_misplaced_self_ty_and_trait(
        &mut self,
        err: &mut Diag<'_>,
        source: PathSource<'_, 'ast, 'ra>,
        res: Option<Res>,
        span: Span,
    ) {
        if let Some((trait_ref, self_ty)) =
            self.diag_metadata.currently_processing_impl_trait.clone()
            && let TyKind::Path(_, self_ty_path) = &self_ty.kind
            && let PathResult::Module(ModuleOrUniformRoot::Module(module)) =
                self.resolve_path(&Segment::from_path(self_ty_path), Some(TypeNS), None, source)
            && let ModuleKind::Def(DefKind::Trait, ..) = module.kind
            && trait_ref.path.span == span
            && let PathSource::Trait(_) = source
            && let Some(Res::Def(DefKind::Struct | DefKind::Enum | DefKind::Union, _)) = res
            && let Ok(self_ty_str) = self.r.tcx.sess.source_map().span_to_snippet(self_ty.span)
            && let Ok(trait_ref_str) =
                self.r.tcx.sess.source_map().span_to_snippet(trait_ref.path.span)
        {
            err.multipart_suggestion(
                    "`impl` items mention the trait being implemented first and the type it is being implemented for second",
                    vec![(trait_ref.path.span, self_ty_str), (self_ty.span, trait_ref_str)],
                    Applicability::MaybeIncorrect,
                );
        }
    }

    fn explain_functions_in_pattern(
        &self,
        err: &mut Diag<'_>,
        res: Option<Res>,
        source: PathSource<'_, '_, '_>,
    ) {
        let PathSource::TupleStruct(_, _) = source else { return };
        let Some(Res::Def(DefKind::Fn, _)) = res else { return };
        err.primary_message("expected a pattern, found a function call");
        err.note("function calls are not allowed in patterns: <https://doc.rust-lang.org/book/ch19-00-patterns.html>");
    }

    fn suggest_changing_type_to_const_param(
        &self,
        err: &mut Diag<'_>,
        res: Option<Res>,
        source: PathSource<'_, '_, '_>,
        path: &[Segment],
        following_seg: Option<&Segment>,
        span: Span,
    ) {
        if let PathSource::Expr(None) = source
            && let Some(Res::Def(DefKind::TyParam, _)) = res
            && following_seg.is_none()
            && let [segment] = path
        {
            // We have something like
            // impl<T, N> From<[T; N]> for VecWrapper<T> {
            //     fn from(slice: [T; N]) -> Self {
            //         VecWrapper(slice.to_vec())
            //     }
            // }
            // where `N` is a type param but should likely have been a const param.
            let Some(item) = self.diag_metadata.current_item else { return };
            let Some(generics) = item.kind.generics() else { return };
            let Some(span) = generics.params.iter().find_map(|param| {
                // Only consider type params with no bounds.
                if param.bounds.is_empty() && param.ident.name == segment.ident.name {
                    Some(param.ident.span)
                } else {
                    None
                }
            }) else {
                return;
            };
            err.subdiagnostic(errors::UnexpectedResChangeTyParamToConstParamSugg {
                before: span.shrink_to_lo(),
                after: span.shrink_to_hi(),
            });
            return;
        }
        let PathSource::Trait(_) = source else { return };

        // We don't include `DefKind::Str` and `DefKind::AssocTy` as they can't be reached here anyway.
        let applicability = match res {
            Some(Res::PrimTy(PrimTy::Int(_) | PrimTy::Uint(_) | PrimTy::Bool | PrimTy::Char)) => {
                Applicability::MachineApplicable
            }
            // NOTE(const_generics): add `DefKind::TyParam` and `SelfTyParam` once we support generic
            // const generics. Of course, `Struct` and `Enum` may contain ty params, too, but the
            // benefits of including them here outweighs the small number of false positives.
            Some(Res::Def(DefKind::Struct | DefKind::Enum, _))
                if self.r.tcx.features().adt_const_params() =>
            {
                Applicability::MaybeIncorrect
            }
            _ => return,
        };

        let Some(item) = self.diag_metadata.current_item else { return };
        let Some(generics) = item.kind.generics() else { return };

        let param = generics.params.iter().find_map(|param| {
            // Only consider type params with exactly one trait bound.
            if let [bound] = &*param.bounds
                && let ast::GenericBound::Trait(tref) = bound
                && tref.modifiers == ast::TraitBoundModifiers::NONE
                && tref.span == span
                && param.ident.span.eq_ctxt(span)
            {
                Some(param.ident.span)
            } else {
                None
            }
        });

        if let Some(param) = param {
            err.subdiagnostic(errors::UnexpectedResChangeTyToConstParamSugg {
                span: param.shrink_to_lo(),
                applicability,
            });
        }
    }

    fn suggest_pattern_match_with_let(
        &self,
        err: &mut Diag<'_>,
        source: PathSource<'_, '_, '_>,
        span: Span,
    ) -> bool {
        if let PathSource::Expr(_) = source
            && let Some(Expr { span: expr_span, kind: ExprKind::Assign(lhs, _, _), .. }) =
                self.diag_metadata.in_if_condition
        {
            // Icky heuristic so we don't suggest:
            // `if (i + 2) = 2` => `if let (i + 2) = 2` (approximately pattern)
            // `if 2 = i` => `if let 2 = i` (lhs needs to contain error span)
            if lhs.is_approximately_pattern() && lhs.span.contains(span) {
                err.span_suggestion_verbose(
                    expr_span.shrink_to_lo(),
                    "you might have meant to use pattern matching",
                    "let ",
                    Applicability::MaybeIncorrect,
                );
                return true;
            }
        }
        false
    }

    fn get_single_associated_item(
        &mut self,
        path: &[Segment],
        source: &PathSource<'_, 'ast, 'ra>,
        filter_fn: &impl Fn(Res) -> bool,
    ) -> Option<TypoSuggestion> {
        if let crate::PathSource::TraitItem(_, _) = source {
            let mod_path = &path[..path.len() - 1];
            if let PathResult::Module(ModuleOrUniformRoot::Module(module)) =
                self.resolve_path(mod_path, None, None, *source)
            {
                let targets: Vec<_> = self
                    .r
                    .resolutions(module)
                    .borrow()
                    .iter()
                    .filter_map(|(key, resolution)| {
                        let resolution = resolution.borrow();
                        resolution.best_decl().map(|binding| binding.res()).and_then(|res| {
                            if filter_fn(res) {
                                Some((key.ident.name, resolution.orig_ident_span, res))
                            } else {
                                None
                            }
                        })
                    })
                    .collect();
                if let &[(name, orig_ident_span, res)] = targets.as_slice() {
                    return Some(TypoSuggestion::single_item(name, orig_ident_span, res));
                }
            }
        }
        None
    }

    /// Given `where <T as Bar>::Baz: String`, suggest `where T: Bar<Baz = String>`.
    fn restrict_assoc_type_in_where_clause(&self, span: Span, err: &mut Diag<'_>) -> bool {
        // Detect that we are actually in a `where` predicate.
        let Some(ast::WherePredicate {
            kind:
                ast::WherePredicateKind::BoundPredicate(ast::WhereBoundPredicate {
                    bounded_ty,
                    bound_generic_params,
                    bounds,
                }),
            span: where_span,
            ..
        }) = self.diag_metadata.current_where_predicate
        else {
            return false;
        };
        if !bound_generic_params.is_empty() {
            return false;
        }

        // Confirm that the target is an associated type.
        let ast::TyKind::Path(Some(qself), path) = &bounded_ty.kind else { return false };
        // use this to verify that ident is a type param.
        let Some(partial_res) = self.r.partial_res_map.get(&bounded_ty.id) else { return false };
        if !matches!(
            partial_res.full_res(),
            Some(hir::def::Res::Def(hir::def::DefKind::AssocTy, _))
        ) {
            return false;
        }

        let peeled_ty = qself.ty.peel_refs();
        let ast::TyKind::Path(None, type_param_path) = &peeled_ty.kind else { return false };
        // Confirm that the `SelfTy` is a type parameter.
        let Some(partial_res) = self.r.partial_res_map.get(&peeled_ty.id) else {
            return false;
        };
        if !matches!(
            partial_res.full_res(),
            Some(hir::def::Res::Def(hir::def::DefKind::TyParam, _))
        ) {
            return false;
        }
        let ([ast::PathSegment { args: None, .. }], [ast::GenericBound::Trait(poly_trait_ref)]) =
            (&type_param_path.segments[..], &bounds[..])
        else {
            return false;
        };
        let [ast::PathSegment { ident, args: None, id }] =
            &poly_trait_ref.trait_ref.path.segments[..]
        else {
            return false;
        };
        if poly_trait_ref.modifiers != ast::TraitBoundModifiers::NONE {
            return false;
        }
        if ident.span == span {
            let Some(partial_res) = self.r.partial_res_map.get(&id) else {
                return false;
            };
            if !matches!(partial_res.full_res(), Some(hir::def::Res::Def(..))) {
                return false;
            }

            let Some(new_where_bound_predicate) =
                mk_where_bound_predicate(path, poly_trait_ref, &qself.ty)
            else {
                return false;
            };
            err.span_suggestion_verbose(
                *where_span,
                format!("constrain the associated type to `{ident}`"),
                where_bound_predicate_to_string(&new_where_bound_predicate),
                Applicability::MaybeIncorrect,
            );
        }
        true
    }

    /// Check if the source is call expression and the first argument is `self`. If true,
    /// return the span of whole call and the span for all arguments expect the first one (`self`).
    fn call_has_self_arg(&self, source: PathSource<'_, '_, '_>) -> Option<(Span, Option<Span>)> {
        let mut has_self_arg = None;
        if let PathSource::Expr(Some(parent)) = source
            && let ExprKind::Call(_, args) = &parent.kind
            && !args.is_empty()
        {
            let mut expr_kind = &args[0].kind;
            loop {
                match expr_kind {
                    ExprKind::Path(_, arg_name) if arg_name.segments.len() == 1 => {
                        if arg_name.segments[0].ident.name == kw::SelfLower {
                            let call_span = parent.span;
                            let tail_args_span = if args.len() > 1 {
                                Some(Span::new(
                                    args[1].span.lo(),
                                    args.last().expect("invariant: non-empty collection").span.hi(),
                                    call_span.ctxt(),
                                    None,
                                ))
                            } else {
                                None
                            };
                            has_self_arg = Some((call_span, tail_args_span));
                        }
                        break;
                    }
                    ExprKind::AddrOf(_, _, expr) => expr_kind = &expr.kind,
                    _ => break,
                }
            }
        }
        has_self_arg
    }

    fn followed_by_brace(&self, span: Span) -> (bool, Option<Span>) {
        // tRust: known issue — (estebank) find a better way to figure out that this was a
        // parser issue where a struct literal is being used on an expression
        // where a brace being opened means a block is being started. Look
        // ahead for the next text to see if `span` is followed by a `{`.
        let sm = self.r.tcx.sess.source_map();
        if let Some(followed_brace_span) = sm.span_look_ahead(span, "{", Some(50)) {
            // In case this could be a struct literal that needs to be surrounded
            // by parentheses, find the appropriate span.
            let close_brace_span = sm.span_look_ahead(followed_brace_span, "}", Some(50));
            let closing_brace = close_brace_span.map(|sp| span.to(sp));
            (true, closing_brace)
        } else {
            (false, None)
        }
    }

    fn is_struct_with_fn_ctor(&mut self, def_id: DefId) -> bool {
        def_id
            .as_local()
            .and_then(|local_id| self.r.struct_constructors.get(&local_id))
            .map(|struct_ctor| {
                matches!(
                    struct_ctor.0,
                    def::Res::Def(DefKind::Ctor(CtorOf::Struct, CtorKind::Fn), _)
                )
            })
            .unwrap_or(false)
    }

    fn update_err_for_private_tuple_struct_fields(
        &mut self,
        err: &mut Diag<'_>,
        source: &PathSource<'_, '_, '_>,
        def_id: DefId,
    ) -> Option<Vec<Span>> {
        match source {
            // e.g. `if let Enum::TupleVariant(field1, field2) = _`
            PathSource::TupleStruct(_, pattern_spans) => {
                err.primary_message(
                    "cannot match against a tuple struct which contains private fields",
                );

                // Use spans of the tuple struct pattern.
                Some(Vec::from(*pattern_spans))
            }
            // e.g. `let _ = Enum::TupleVariant(field1, field2);`
            PathSource::Expr(Some(Expr {
                kind: ExprKind::Call(path, args),
                span: call_span,
                ..
            })) => {
                err.primary_message(
                    "cannot initialize a tuple struct which contains private fields",
                );
                self.suggest_alternative_construction_methods(
                    def_id,
                    err,
                    path.span,
                    *call_span,
                    &args[..],
                );

                self.r
                    .field_idents(def_id)
                    .map(|fields| fields.iter().map(|f| f.span).collect::<Vec<_>>())
            }
            _ => None,
        }
    }

    /// Provides context-dependent help for errors reported by the `smart_resolve_path_fragment`
    /// function.
    /// Returns `true` if able to provide context-dependent help.
}
