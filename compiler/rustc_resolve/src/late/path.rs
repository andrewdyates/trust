// tRust: Split from late.rs -- path resolution and smart_resolve methods.
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


impl<'a, 'ast, 'ra, 'tcx> LateResolutionVisitor<'a, 'ast, 'ra, 'tcx> {
    fn resolve_impl_restriction_path(&mut self, restriction: &'ast ast::ImplRestriction) {
        match &restriction.kind {
            ast::RestrictionKind::Unrestricted => (),
            ast::RestrictionKind::Restricted { path, id, shorthand: _ } => {
                self.smart_resolve_path(*id, &None, path, PathSource::Module);
                if let Some(res) = self.r.partial_res_map[&id].full_res()
                    && let Some(def_id) = res.opt_def_id()
                {
                    if !self.r.is_accessible_from(
                        Visibility::Restricted(def_id),
                        self.parent_scope.module,
                    ) {
                        self.r.dcx().create_err(errors::RestrictionAncestorOnly(path.span)).emit();
                    }
                }
            }
        }
    }

    // High-level and context dependent path resolution routine.
    // Resolves the path and records the resolution into definition map.
    // If resolution fails tries several techniques to find likely
    // resolution candidates, suggest imports or other help, and report
    // errors in user friendly way.
    fn smart_resolve_path(
        &mut self,
        id: NodeId,
        qself: &Option<Box<QSelf>>,
        path: &Path,
        source: PathSource<'_, 'ast, 'ra>,
    ) {
        self.smart_resolve_path_fragment(
            qself,
            &Segment::from_path(path),
            source,
            Finalize::new(id, path.span),
            RecordPartialRes::Yes,
            None,
        );
    }

    fn smart_resolve_path_fragment(
        &mut self,
        qself: &Option<Box<QSelf>>,
        path: &[Segment],
        source: PathSource<'_, 'ast, 'ra>,
        finalize: Finalize,
        record_partial_res: RecordPartialRes,
        parent_qself: Option<&QSelf>,
    ) -> PartialRes {
        let ns = source.namespace();

        let Finalize { node_id, path_span, .. } = finalize;
        let report_errors = |this: &mut Self, res: Option<Res>| {
            if this.should_report_errs() {
                let (mut err, candidates) = this.smart_resolve_report_errors(
                    path,
                    None,
                    path_span,
                    source,
                    res,
                    parent_qself,
                );

                let def_id = this.parent_scope.module.nearest_parent_mod();
                let instead = res.is_some();
                let (suggestion, const_err) = if let Some((start, end)) =
                    this.diag_metadata.in_range
                    && path[0].ident.span.lo() == end.span.lo()
                    && !matches!(start.kind, ExprKind::Lit(_))
                {
                    let mut sugg = ".";
                    let mut span = start.span.between(end.span);
                    if span.lo() + BytePos(2) == span.hi() {
                        // There's no space between the start, the range op and the end, suggest
                        // removal which will look better.
                        span = span.with_lo(span.lo() + BytePos(1));
                        sugg = "";
                    }
                    (
                        Some((
                            span,
                            "you might have meant to write `.` instead of `..`",
                            sugg.to_string(),
                            Applicability::MaybeIncorrect,
                        )),
                        None,
                    )
                } else if res.is_none()
                    && let PathSource::Type
                    | PathSource::Expr(_)
                    | PathSource::PreciseCapturingArg(..) = source
                {
                    this.suggest_adding_generic_parameter(path, source)
                } else {
                    (None, None)
                };

                if let Some(const_err) = const_err {
                    err.cancel();
                    err = const_err;
                }

                let ue = UseError {
                    err,
                    candidates,
                    def_id,
                    instead,
                    suggestion,
                    path: path.into(),
                    is_call: source.is_call(),
                };

                this.r.use_injections.push(ue);
            }

            PartialRes::new(Res::Err)
        };

        // For paths originating from calls (like in `HashMap::new()`), tries
        // to enrich the plain `failed to resolve: ...` message with hints
        // about possible missing imports.
        //
        // Similar thing, for types, happens in `report_errors` above.
        let report_errors_for_call =
            |this: &mut Self, parent_err: Spanned<ResolutionError<'ra>>| {
                // Before we start looking for candidates, we have to get our hands
                // on the type user is trying to perform invocation on; basically:
                // we're transforming `HashMap::new` into just `HashMap`.
                let (following_seg, prefix_path) = match path.split_last() {
                    Some((last, path)) if !path.is_empty() => (Some(last), path),
                    _ => return Some(parent_err),
                };

                let (mut err, candidates) = this.smart_resolve_report_errors(
                    prefix_path,
                    following_seg,
                    path_span,
                    PathSource::Type,
                    None,
                    parent_qself,
                );

                // There are two different error messages user might receive at
                // this point:
                // - E0425 cannot find type `{}` in this scope
                // - E0433 failed to resolve: use of undeclared type or module `{}`
                //
                // The first one is emitted for paths in type-position, and the
                // latter one - for paths in expression-position.
                //
                // Thus (since we're in expression-position at this point), not to
                // confuse the user, we want to keep the *message* from E0433 (so
                // `parent_err`), but we want *hints* from E0425 (so `err`).
                //
                // And that's what happens below - we're just mixing both messages
                // into a single one.
                let failed_to_resolve = match parent_err.node {
                    ResolutionError::FailedToResolve { .. } => true,
                    _ => false,
                };
                let mut parent_err = this.r.into_struct_error(parent_err.span, parent_err.node);

                // overwrite all properties with the parent's error message
                err.messages = take(&mut parent_err.messages);
                err.code = take(&mut parent_err.code);
                swap(&mut err.span, &mut parent_err.span);
                if failed_to_resolve {
                    err.children = take(&mut parent_err.children);
                } else {
                    err.children.append(&mut parent_err.children);
                }
                err.sort_span = parent_err.sort_span;
                err.is_lint = parent_err.is_lint.clone();

                // merge the parent_err's suggestions with the typo (err's) suggestions
                match &mut err.suggestions {
                    Suggestions::Enabled(typo_suggestions) => match &mut parent_err.suggestions {
                        Suggestions::Enabled(parent_suggestions) => {
                            // If both suggestions are enabled, append parent_err's suggestions to err's suggestions.
                            typo_suggestions.append(parent_suggestions)
                        }
                        Suggestions::Sealed(_) | Suggestions::Disabled => {
                            // If the parent's suggestions are either sealed or disabled, it signifies that
                            // new suggestions cannot be added or removed from the diagnostic. Therefore,
                            // we assign both types of suggestions to err's suggestions and discard the
                            // existing suggestions in err.
                            err.suggestions = std::mem::take(&mut parent_err.suggestions);
                        }
                    },
                    Suggestions::Sealed(_) | Suggestions::Disabled => (),
                }

                parent_err.cancel();

                let def_id = this.parent_scope.module.nearest_parent_mod();

                if this.should_report_errs() {
                    if candidates.is_empty() {
                        if path.len() == 2
                            && let [segment] = prefix_path
                        {
                            // Delay to check whether method name is an associated function or not
                            // ```
                            // let foo = Foo {};
                            // foo::bar(); // possibly suggest to foo.bar();
                            //```
                            err.stash(segment.ident.span, rustc_errors::StashKey::CallAssocMethod);
                        } else {
                            // When there is no suggested imports, we can just emit the error
                            // and suggestions immediately. Note that we bypass the usually error
                            // reporting routine (ie via `self.r.report_error`) because we need
                            // to post-process the `ResolutionError` above.
                            err.emit();
                        }
                    } else {
                        // If there are suggested imports, the error reporting is delayed
                        this.r.use_injections.push(UseError {
                            err,
                            candidates,
                            def_id,
                            instead: false,
                            suggestion: None,
                            path: prefix_path.into(),
                            is_call: source.is_call(),
                        });
                    }
                } else {
                    err.cancel();
                }

                // We don't return `Some(parent_err)` here, because the error will
                // be already printed either immediately or as part of the `use` injections
                None
            };

        let partial_res = match self.resolve_qpath_anywhere(
            qself,
            path,
            ns,
            source.defer_to_typeck(),
            finalize,
            source,
        ) {
            Ok(Some(partial_res)) if let Some(res) = partial_res.full_res() => {
                // if we also have an associated type that matches the ident, stash a suggestion
                if let Some(items) = self.diag_metadata.current_trait_assoc_items
                    && let [Segment { ident, .. }] = path
                    && items.iter().any(|item| {
                        if let AssocItemKind::Type(alias) = &item.kind
                            && alias.ident == *ident
                        {
                            true
                        } else {
                            false
                        }
                    })
                {
                    let mut diag = self.r.tcx.dcx().struct_allow("");
                    diag.span_suggestion_verbose(
                        path_span.shrink_to_lo(),
                        "there is an associated type with the same name",
                        "Self::",
                        Applicability::MaybeIncorrect,
                    );
                    diag.stash(path_span, StashKey::AssociatedTypeSuggestion);
                }

                if source.is_expected(res) || res == Res::Err {
                    partial_res
                } else {
                    report_errors(self, Some(res))
                }
            }

            Ok(Some(partial_res)) if source.defer_to_typeck() => {
                // Not fully resolved associated item `T::A::B` or `<T as Tr>::A::B`
                // or `<T>::A::B`. If `B` should be resolved in value namespace then
                // it needs to be added to the trait map.
                if ns == ValueNS {
                    let item_name = path.last().expect("invariant: non-empty collection").ident;
                    let traits = self.traits_in_scope(item_name, ns);
                    self.r.trait_map.insert(node_id, traits);
                }

                if PrimTy::from_name(path[0].ident.name).is_some() {
                    let mut std_path = Vec::with_capacity(1 + path.len());

                    std_path.push(Segment::from_ident(Ident::with_dummy_span(sym::std)));
                    std_path.extend(path);
                    if let PathResult::Module(_) | PathResult::NonModule(_) =
                        self.resolve_path(&std_path, Some(ns), None, source)
                    {
                        // Check if we wrote `str::from_utf8` instead of `std::str::from_utf8`
                        let item_span =
                            path.iter().last().map_or(path_span, |segment| segment.ident.span);

                        self.r.confused_type_with_std_module.insert(item_span, path_span);
                        self.r.confused_type_with_std_module.insert(path_span, path_span);
                    }
                }

                partial_res
            }

            Err(err) => {
                if let Some(err) = report_errors_for_call(self, err) {
                    self.report_error(err.span, err.node);
                }

                PartialRes::new(Res::Err)
            }

            _ => report_errors(self, None),
        };

        if record_partial_res == RecordPartialRes::Yes {
            // Avoid recording definition of `A::B` in `<T as A>::B::C`.
            self.r.record_partial_res(node_id, partial_res);
            self.resolve_elided_lifetimes_in_path(partial_res, path, source, path_span);
            self.lint_unused_qualifications(path, ns, finalize);
        }

        partial_res
    }

    fn self_type_is_available(&mut self) -> bool {
        let binding = self
            .maybe_resolve_ident_in_lexical_scope(Ident::with_dummy_span(kw::SelfUpper), TypeNS);
        if let Some(LateDecl::RibDef(res)) = binding { res != Res::Err } else { false }
    }

    fn self_value_is_available(&mut self, self_span: Span) -> bool {
        let ident = Ident::new(kw::SelfLower, self_span);
        let binding = self.maybe_resolve_ident_in_lexical_scope(ident, ValueNS);
        if let Some(LateDecl::RibDef(res)) = binding { res != Res::Err } else { false }
    }

    /// A wrapper around [`Resolver::report_error`].
    ///
    /// This doesn't emit errors for function bodies if this is rustdoc.
    fn report_error(&mut self, span: Span, resolution_error: ResolutionError<'ra>) {
        if self.should_report_errs() {
            self.r.report_error(span, resolution_error);
        }
    }

    #[inline]
    /// If we're actually rustdoc then avoid giving a name resolution error for `cfg()` items or
    // an invalid `use foo::*;` was found, which can cause unbounded amounts of "item not found"
    // errors. We silence them all.
    fn should_report_errs(&self) -> bool {
        !(self.r.tcx.sess.opts.actually_rustdoc && self.in_func_body)
            && !self.r.glob_error.is_some()
    }

    // Resolve in alternative namespaces if resolution in the primary namespace fails.
    fn resolve_qpath_anywhere(
        &mut self,
        qself: &Option<Box<QSelf>>,
        path: &[Segment],
        primary_ns: Namespace,
        defer_to_typeck: bool,
        finalize: Finalize,
        source: PathSource<'_, 'ast, 'ra>,
    ) -> Result<Option<PartialRes>, Spanned<ResolutionError<'ra>>> {
        let mut fin_res = None;

        for (i, &ns) in [primary_ns, TypeNS, ValueNS].iter().enumerate() {
            if i == 0 || ns != primary_ns {
                match self.resolve_qpath(qself, path, ns, finalize, source)? {
                    Some(partial_res)
                        if partial_res.unresolved_segments() == 0 || defer_to_typeck =>
                    {
                        return Ok(Some(partial_res));
                    }
                    partial_res => {
                        if fin_res.is_none() {
                            fin_res = partial_res;
                        }
                    }
                }
            }
        }

        assert!(primary_ns != MacroNS);
        if qself.is_none()
            && let PathResult::NonModule(res) =
                self.r.cm().maybe_resolve_path(path, Some(MacroNS), &self.parent_scope, None)
        {
            return Ok(Some(res));
        }

        Ok(fin_res)
    }

    /// Handles paths that may refer to associated items.
    fn resolve_qpath(
        &mut self,
        qself: &Option<Box<QSelf>>,
        path: &[Segment],
        ns: Namespace,
        finalize: Finalize,
        source: PathSource<'_, 'ast, 'ra>,
    ) -> Result<Option<PartialRes>, Spanned<ResolutionError<'ra>>> {
        debug!(
            "resolve_qpath(qself={:?}, path={:?}, ns={:?}, finalize={:?})",
            qself, path, ns, finalize,
        );

        if let Some(qself) = qself {
            if qself.position == 0 {
                // This is a case like `<T>::B`, where there is no
                // trait to resolve. In that case, we leave the `B`
                // segment to be resolved by type-check.
                return Ok(Some(PartialRes::with_unresolved_segments(
                    Res::Def(DefKind::Mod, CRATE_DEF_ID.to_def_id()),
                    path.len(),
                )));
            }

            let num_privacy_errors = self.r.privacy_errors.len();
            // Make sure that `A` in `<T as A>::B::C` is a trait.
            let trait_res = self.smart_resolve_path_fragment(
                &None,
                &path[..qself.position],
                PathSource::Trait(AliasPossibility::No),
                Finalize::new(finalize.node_id, qself.path_span),
                RecordPartialRes::No,
                Some(&qself),
            );

            if trait_res.expect_full_res() == Res::Err {
                return Ok(Some(trait_res));
            }

            // Truncate additional privacy errors reported above,
            // because they'll be recomputed below.
            self.r.privacy_errors.truncate(num_privacy_errors);

            // Make sure `A::B` in `<T as A>::B::C` is a trait item.
            //
            // Currently, `path` names the full item (`A::B::C`, in
            // our example). so we extract the prefix of that that is
            // the trait (the slice upto and including
            // `qself.position`). And then we recursively resolve that,
            // but with `qself` set to `None`.
            let ns = if qself.position + 1 == path.len() { ns } else { TypeNS };
            let partial_res = self.smart_resolve_path_fragment(
                &None,
                &path[..=qself.position],
                PathSource::TraitItem(ns, &source),
                Finalize::with_root_span(finalize.node_id, finalize.path_span, qself.path_span),
                RecordPartialRes::No,
                Some(&qself),
            );

            // The remaining segments (the `C` in our example) will
            // have to be resolved by type-check, since that requires doing
            // trait resolution.
            return Ok(Some(PartialRes::with_unresolved_segments(
                partial_res.base_res(),
                partial_res.unresolved_segments() + path.len() - qself.position - 1,
            )));
        }

        let result = match self.resolve_path(path, Some(ns), Some(finalize), source) {
            PathResult::NonModule(path_res) => path_res,
            PathResult::Module(ModuleOrUniformRoot::Module(module)) if !module.is_normal() => {
                PartialRes::new(module.res().expect("invariant: module has resolution"))
            }
            // A part of this path references a `mod` that had a parse error. To avoid resolution
            // errors for each reference to that module, we don't emit an error for them until the
            // `mod` is fixed. this can have a significant cascade effect.
            PathResult::Failed { error_implied_by_parse_error: true, .. } => {
                PartialRes::new(Res::Err)
            }
            // In `a(::assoc_item)*` `a` cannot be a module. If `a` does resolve to a module we
            // don't report an error right away, but try to fallback to a primitive type.
            // So, we are still able to successfully resolve something like
            //
            // use std::u8; // bring module u8 in scope
            // fn f() -> u8 { // OK, resolves to primitive u8, not to std::u8
            //     u8::max_value() // OK, resolves to associated function <u8>::max_value,
            //                     // not to nonexistent std::u8::max_value
            // }
            //
            // Such behavior is required for backward compatibility.
            // The same fallback is used when `a` resolves to nothing.
            PathResult::Module(ModuleOrUniformRoot::Module(_)) | PathResult::Failed { .. }
                if (ns == TypeNS || path.len() > 1)
                    && PrimTy::from_name(path[0].ident.name).is_some() =>
            {
                let prim = PrimTy::from_name(path[0].ident.name).expect("invariant: value is present");
                let tcx = self.r.tcx();

                let gate_err_sym_msg = match prim {
                    PrimTy::Float(FloatTy::F16) if !tcx.features().f16() => {
                        Some((sym::f16, "the type `f16` is unstable"))
                    }
                    PrimTy::Float(FloatTy::F128) if !tcx.features().f128() => {
                        Some((sym::f128, "the type `f128` is unstable"))
                    }
                    _ => None,
                };

                if let Some((sym, msg)) = gate_err_sym_msg {
                    let span = path[0].ident.span;
                    if !span.allows_unstable(sym) {
                        feature_err(tcx.sess, sym, span, msg).emit();
                    }
                };

                // Fix up partial res of segment from `resolve_path` call.
                if let Some(id) = path[0].id {
                    self.r.partial_res_map.insert(id, PartialRes::new(Res::PrimTy(prim)));
                }

                PartialRes::with_unresolved_segments(Res::PrimTy(prim), path.len() - 1)
            }
            PathResult::Module(ModuleOrUniformRoot::Module(module)) => {
                PartialRes::new(module.res().expect("invariant: module has resolution"))
            }
            PathResult::Failed {
                is_error_from_last_segment: false,
                span,
                label,
                suggestion,
                module,
                segment_name,
                error_implied_by_parse_error: _,
                message,
            } => {
                return Err(respan(
                    span,
                    ResolutionError::FailedToResolve {
                        segment: segment_name,
                        label,
                        suggestion,
                        module,
                        message,
                    },
                ));
            }
            PathResult::Module(..) | PathResult::Failed { .. } => return Ok(None),
            // tRust: invariant — path resolution is always determinate by the time resolve_qpath is called
            PathResult::Indeterminate => bug!("indeterminate path result in resolve_qpath"),
        };

        Ok(Some(result))
    }


}
