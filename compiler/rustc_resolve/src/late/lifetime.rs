// tRust: Split from late.rs -- lifetime resolution methods.
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
    /// Do some `work` within a new innermost rib of the given `kind` in the given namespace (`ns`).
    fn with_rib<T>(
        &mut self,
        ns: Namespace,
        kind: RibKind<'ra>,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.ribs[ns].push(Rib::new(kind));
        let ret = work(self);
        self.ribs[ns].pop();
        ret
    }

    fn visit_generic_params(&mut self, params: &'ast [GenericParam], add_self_upper: bool) {
        // For type parameter defaults, we have to ban access
        // to following type parameters, as the GenericArgs can only
        // provide previous type parameters as they're built. We
        // put all the parameters on the ban list and then remove
        // them one by one as they are processed and become available.
        let mut forward_ty_ban_rib =
            Rib::new(RibKind::ForwardGenericParamBan(ForwardGenericParamBanReason::Default));
        let mut forward_const_ban_rib =
            Rib::new(RibKind::ForwardGenericParamBan(ForwardGenericParamBanReason::Default));
        for param in params.iter() {
            match param.kind {
                GenericParamKind::Type { .. } => {
                    forward_ty_ban_rib
                        .bindings
                        .insert(Ident::with_dummy_span(param.ident.name), Res::Err);
                }
                GenericParamKind::Const { .. } => {
                    forward_const_ban_rib
                        .bindings
                        .insert(Ident::with_dummy_span(param.ident.name), Res::Err);
                }
                GenericParamKind::Lifetime => {}
            }
        }

        // rust-lang/rust#61631: The type `Self` is essentially
        // another type parameter. For ADTs, we consider it
        // well-defined only after all of the ADT type parameters have
        // been provided. Therefore, we do not allow use of `Self`
        // anywhere in ADT type parameter defaults.
        //
        // (We however cannot ban `Self` for defaults on *all* generic
        // lists; e.g. trait generics can usefully refer to `Self`,
        // such as in the case of `trait Add<Rhs = Self>`.)
        if add_self_upper {
            // (`Some` if + only if we are in ADT's generics.)
            forward_ty_ban_rib.bindings.insert(Ident::with_dummy_span(kw::SelfUpper), Res::Err);
        }

        // NOTE: We use different ribs here not for a technical reason, but just
        // for better diagnostics.
        let mut forward_ty_ban_rib_const_param_ty = Rib {
            bindings: forward_ty_ban_rib.bindings.clone(),
            patterns_with_skipped_bindings: Default::default(),
            kind: RibKind::ForwardGenericParamBan(ForwardGenericParamBanReason::ConstParamTy),
        };
        let mut forward_const_ban_rib_const_param_ty = Rib {
            bindings: forward_const_ban_rib.bindings.clone(),
            patterns_with_skipped_bindings: Default::default(),
            kind: RibKind::ForwardGenericParamBan(ForwardGenericParamBanReason::ConstParamTy),
        };
        // We'll ban these with a `ConstParamTy` rib, so just clear these ribs for better
        // diagnostics, so we don't mention anything about const param tys having generics at all.
        if !self.r.tcx.features().generic_const_parameter_types() {
            forward_ty_ban_rib_const_param_ty.bindings.clear();
            forward_const_ban_rib_const_param_ty.bindings.clear();
        }

        self.with_lifetime_rib(LifetimeRibKind::AnonymousReportError, |this| {
            for param in params {
                match param.kind {
                    GenericParamKind::Lifetime => {
                        for bound in &param.bounds {
                            this.visit_param_bound(bound, BoundKind::Bound);
                        }
                    }
                    GenericParamKind::Type { ref default } => {
                        for bound in &param.bounds {
                            this.visit_param_bound(bound, BoundKind::Bound);
                        }

                        if let Some(ty) = default {
                            this.ribs[TypeNS].push(forward_ty_ban_rib);
                            this.ribs[ValueNS].push(forward_const_ban_rib);
                            this.visit_ty(ty);
                            forward_const_ban_rib = this.ribs[ValueNS].pop().expect("invariant: non-empty collection");
                            forward_ty_ban_rib = this.ribs[TypeNS].pop().expect("invariant: non-empty collection");
                        }

                        // Allow all following defaults to refer to this type parameter.
                        let i = &Ident::with_dummy_span(param.ident.name);
                        forward_ty_ban_rib.bindings.swap_remove(i);
                        forward_ty_ban_rib_const_param_ty.bindings.swap_remove(i);
                    }
                    GenericParamKind::Const { ref ty, span: _, ref default } => {
                        // Const parameters can't have param bounds.
                        assert!(param.bounds.is_empty());

                        this.ribs[TypeNS].push(forward_ty_ban_rib_const_param_ty);
                        this.ribs[ValueNS].push(forward_const_ban_rib_const_param_ty);
                        if this.r.tcx.features().generic_const_parameter_types() {
                            this.visit_ty(ty)
                        } else {
                            this.ribs[TypeNS].push(Rib::new(RibKind::ConstParamTy));
                            this.ribs[ValueNS].push(Rib::new(RibKind::ConstParamTy));
                            this.with_lifetime_rib(LifetimeRibKind::ConstParamTy, |this| {
                                this.visit_ty(ty)
                            });
                            this.ribs[TypeNS].pop().expect("invariant: non-empty collection");
                            this.ribs[ValueNS].pop().expect("invariant: non-empty collection");
                        }
                        forward_const_ban_rib_const_param_ty = this.ribs[ValueNS].pop().expect("invariant: non-empty collection");
                        forward_ty_ban_rib_const_param_ty = this.ribs[TypeNS].pop().expect("invariant: non-empty collection");

                        if let Some(expr) = default {
                            this.ribs[TypeNS].push(forward_ty_ban_rib);
                            this.ribs[ValueNS].push(forward_const_ban_rib);
                            this.resolve_anon_const(
                                expr,
                                AnonConstKind::ConstArg(IsRepeatExpr::No),
                            );
                            forward_const_ban_rib = this.ribs[ValueNS].pop().expect("invariant: non-empty collection");
                            forward_ty_ban_rib = this.ribs[TypeNS].pop().expect("invariant: non-empty collection");
                        }

                        // Allow all following defaults to refer to this const parameter.
                        let i = &Ident::with_dummy_span(param.ident.name);
                        forward_const_ban_rib.bindings.swap_remove(i);
                        forward_const_ban_rib_const_param_ty.bindings.swap_remove(i);
                    }
                }
            }
        })
    }

    #[instrument(level = "debug", skip(self, work))]
    fn with_lifetime_rib<T>(
        &mut self,
        kind: LifetimeRibKind,
        work: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.lifetime_ribs.push(LifetimeRib::new(kind));
        let outer_elision_candidates = self.lifetime_elision_candidates.take();
        let ret = work(self);
        self.lifetime_elision_candidates = outer_elision_candidates;
        self.lifetime_ribs.pop();
        ret
    }

    #[instrument(level = "debug", skip(self))]
    fn resolve_lifetime(&mut self, lifetime: &'ast Lifetime, use_ctxt: visit::LifetimeCtxt) {
        let ident = lifetime.ident;

        if ident.name == kw::StaticLifetime {
            self.record_lifetime_res(
                lifetime.id,
                LifetimeRes::Static,
                LifetimeElisionCandidate::Named,
            );
            return;
        }

        if ident.name == kw::UnderscoreLifetime {
            return self.resolve_anonymous_lifetime(lifetime, lifetime.id, false);
        }

        let mut lifetime_rib_iter = self.lifetime_ribs.iter().rev();
        while let Some(rib) = lifetime_rib_iter.next() {
            let normalized_ident = ident.normalize_to_macros_2_0();
            if let Some(&(_, res)) = rib.bindings.get(&normalized_ident) {
                self.record_lifetime_res(lifetime.id, res, LifetimeElisionCandidate::Named);

                if let LifetimeRes::Param { param, binder } = res {
                    match self.lifetime_uses.entry(param) {
                        Entry::Vacant(v) => {
                            debug!("First use of {:?} at {:?}", res, ident.span);
                            let use_set = self
                                .lifetime_ribs
                                .iter()
                                .rev()
                                .find_map(|rib| match rib.kind {
                                    // Do not suggest eliding a lifetime where an anonymous
                                    // lifetime would be illegal.
                                    LifetimeRibKind::Item
                                    | LifetimeRibKind::AnonymousReportError
                                    | LifetimeRibKind::StaticIfNoLifetimeInScope { .. }
                                    | LifetimeRibKind::ElisionFailure => Some(LifetimeUseSet::Many),
                                    // An anonymous lifetime is legal here, and bound to the right
                                    // place, go ahead.
                                    LifetimeRibKind::AnonymousCreateParameter {
                                        binder: anon_binder,
                                        ..
                                    } => Some(if binder == anon_binder {
                                        LifetimeUseSet::One { use_span: ident.span, use_ctxt }
                                    } else {
                                        LifetimeUseSet::Many
                                    }),
                                    // Only report if eliding the lifetime would have the same
                                    // semantics.
                                    LifetimeRibKind::Elided(r) => Some(if res == r {
                                        LifetimeUseSet::One { use_span: ident.span, use_ctxt }
                                    } else {
                                        LifetimeUseSet::Many
                                    }),
                                    LifetimeRibKind::Generics { .. }
                                    | LifetimeRibKind::ConstParamTy => None,
                                    LifetimeRibKind::ConcreteAnonConst(_) => {
                                    // tRust: invariant — ConcreteAnonConst rib always has an inner Elided(Infer) rib, so this arm is unreachable
                                        span_bug!(ident.span, "unexpected rib kind: {:?}", rib.kind)
                                    }
                                })
                                .unwrap_or(LifetimeUseSet::Many);
                            debug!(?use_ctxt, ?use_set);
                            v.insert(use_set);
                        }
                        Entry::Occupied(mut o) => {
                            debug!("Many uses of {:?} at {:?}", res, ident.span);
                            *o.get_mut() = LifetimeUseSet::Many;
                        }
                    }
                }
                return;
            }

            match rib.kind {
                LifetimeRibKind::Item => break,
                LifetimeRibKind::ConstParamTy => {
                    let guar = self.emit_non_static_lt_in_const_param_ty_error(lifetime);
                    self.record_lifetime_res(
                        lifetime.id,
                        LifetimeRes::Error(guar),
                        LifetimeElisionCandidate::Ignore,
                    );
                    return;
                }
                LifetimeRibKind::ConcreteAnonConst(cause) => {
                    let guar = self.emit_forbidden_non_static_lifetime_error(cause, lifetime);
                    self.record_lifetime_res(
                        lifetime.id,
                        LifetimeRes::Error(guar),
                        LifetimeElisionCandidate::Ignore,
                    );
                    return;
                }
                LifetimeRibKind::AnonymousCreateParameter { .. }
                | LifetimeRibKind::Elided(_)
                | LifetimeRibKind::Generics { .. }
                | LifetimeRibKind::ElisionFailure
                | LifetimeRibKind::AnonymousReportError
                | LifetimeRibKind::StaticIfNoLifetimeInScope { .. } => {}
            }
        }

        let normalized_ident = ident.normalize_to_macros_2_0();
        let outer_res = lifetime_rib_iter
            .find_map(|rib| rib.bindings.get_key_value(&normalized_ident).map(|(&outer, _)| outer));

        let guar = self.emit_undeclared_lifetime_error(lifetime, outer_res);
        self.record_lifetime_res(
            lifetime.id,
            LifetimeRes::Error(guar),
            LifetimeElisionCandidate::Named,
        );
    }

    #[instrument(level = "debug", skip(self))]
    fn resolve_anonymous_lifetime(
        &mut self,
        lifetime: &Lifetime,
        id_for_lint: NodeId,
        elided: bool,
    ) {
        debug_assert_eq!(lifetime.ident.name, kw::UnderscoreLifetime);

        let kind =
            if elided { MissingLifetimeKind::Ampersand } else { MissingLifetimeKind::Underscore };
        let missing_lifetime = MissingLifetime {
            id: lifetime.id,
            span: lifetime.ident.span,
            kind,
            count: 1,
            id_for_lint,
        };
        let elision_candidate = LifetimeElisionCandidate::Missing(missing_lifetime);
        for (i, rib) in self.lifetime_ribs.iter().enumerate().rev() {
            debug!(?rib.kind);
            match rib.kind {
                LifetimeRibKind::AnonymousCreateParameter { binder, .. } => {
                    let res = self.create_fresh_lifetime(lifetime.ident, binder, kind);
                    self.record_lifetime_res(lifetime.id, res, elision_candidate);
                    return;
                }
                LifetimeRibKind::StaticIfNoLifetimeInScope { lint_id: node_id, emit_lint } => {
                    let mut lifetimes_in_scope = vec![];
                    for rib in self.lifetime_ribs[..i].iter().rev() {
                        lifetimes_in_scope.extend(rib.bindings.iter().map(|(ident, _)| ident.span));
                        // Consider any anonymous lifetimes, too
                        if let LifetimeRibKind::AnonymousCreateParameter { binder, .. } = rib.kind
                            && let Some(extra) = self.r.extra_lifetime_params_map.get(&binder)
                        {
                            lifetimes_in_scope.extend(extra.iter().map(|(ident, _, _)| ident.span));
                        }
                        if let LifetimeRibKind::Item = rib.kind {
                            break;
                        }
                    }
                    if lifetimes_in_scope.is_empty() {
                        self.record_lifetime_res(
                            lifetime.id,
                            LifetimeRes::Static,
                            elision_candidate,
                        );
                        return;
                    } else if emit_lint {
                        let lt_span = if elided {
                            lifetime.ident.span.shrink_to_hi()
                        } else {
                            lifetime.ident.span
                        };
                        let code = if elided { "'static " } else { "'static" };

                        self.r.lint_buffer.buffer_lint(
                            lint::builtin::ELIDED_LIFETIMES_IN_ASSOCIATED_CONSTANT,
                            node_id,
                            lifetime.ident.span,
                            crate::errors::AssociatedConstElidedLifetime {
                                elided,
                                code,
                                span: lt_span,
                                lifetimes_in_scope: lifetimes_in_scope.into(),
                            },
                        );
                    }
                }
                LifetimeRibKind::AnonymousReportError => {
                    let guar = if elided {
                        let suggestion = self.lifetime_ribs[i..].iter().rev().find_map(|rib| {
                            if let LifetimeRibKind::Generics {
                                span,
                                kind: LifetimeBinderKind::PolyTrait | LifetimeBinderKind::WhereBound,
                                ..
                            } = rib.kind
                            {
                                Some(errors::ElidedAnonymousLifetimeReportErrorSuggestion {
                                    lo: span.shrink_to_lo(),
                                    hi: lifetime.ident.span.shrink_to_hi(),
                                })
                            } else {
                                None
                            }
                        });
                        // are we trying to use an anonymous lifetime
                        // on a non GAT associated trait type?
                        if !self.in_func_body
                            && let Some((module, _)) = &self.current_trait_ref
                            && let Some(ty) = &self.diag_metadata.current_self_type
                            && Some(true) == self.diag_metadata.in_non_gat_assoc_type
                            && let crate::ModuleKind::Def(DefKind::Trait, trait_id, _) = module.kind
                        {
                            if def_id_matches_path(
                                self.r.tcx,
                                trait_id,
                                &["core", "iter", "traits", "iterator", "Iterator"],
                            ) {
                                self.r.dcx().emit_err(errors::LendingIteratorReportError {
                                    lifetime: lifetime.ident.span,
                                    ty: ty.span,
                                })
                            } else {
                                let decl = if !trait_id.is_local()
                                    && let Some(assoc) = self.diag_metadata.current_impl_item
                                    && let AssocItemKind::Type(_) = assoc.kind
                                    && let assocs = self.r.tcx.associated_items(trait_id)
                                    && let Some(ident) = assoc.kind.ident()
                                    && let Some(assoc) = assocs.find_by_ident_and_kind(
                                        self.r.tcx,
                                        ident,
                                        AssocTag::Type,
                                        trait_id,
                                    ) {
                                    let mut decl: MultiSpan =
                                        self.r.tcx.def_span(assoc.def_id).into();
                                    decl.push_span_label(
                                        self.r.tcx.def_span(trait_id),
                                        String::new(),
                                    );
                                    decl
                                } else {
                                    DUMMY_SP.into()
                                };
                                let mut err = self.r.dcx().create_err(
                                    errors::AnonymousLifetimeNonGatReportError {
                                        lifetime: lifetime.ident.span,
                                        decl,
                                    },
                                );
                                self.point_at_impl_lifetimes(&mut err, i, lifetime.ident.span);
                                err.emit()
                            }
                        } else {
                            self.r.dcx().emit_err(errors::ElidedAnonymousLifetimeReportError {
                                span: lifetime.ident.span,
                                suggestion,
                            })
                        }
                    } else {
                        self.r.dcx().emit_err(errors::ExplicitAnonymousLifetimeReportError {
                            span: lifetime.ident.span,
                        })
                    };
                    self.record_lifetime_res(
                        lifetime.id,
                        LifetimeRes::Error(guar),
                        elision_candidate,
                    );
                    return;
                }
                LifetimeRibKind::Elided(res) => {
                    self.record_lifetime_res(lifetime.id, res, elision_candidate);
                    return;
                }
                LifetimeRibKind::ElisionFailure => {
                    self.diag_metadata.current_elision_failures.push((
                        missing_lifetime,
                        elision_candidate,
                        Either::Left(lifetime.id),
                    ));
                    return;
                }
                LifetimeRibKind::Item => break,
                LifetimeRibKind::Generics { .. } | LifetimeRibKind::ConstParamTy => {}
                LifetimeRibKind::ConcreteAnonConst(_) => {
                    // There is always an `Elided(LifetimeRes::Infer)` inside an `AnonConst`.
                    // tRust: invariant — ConcreteAnonConst rib always has an inner Elided(Infer) rib, so this arm is unreachable
                    span_bug!(lifetime.ident.span, "unexpected rib kind: {:?}", rib.kind)
                }
            }
        }
        let guar = self.report_missing_lifetime_specifiers([&missing_lifetime], None);
        self.record_lifetime_res(lifetime.id, LifetimeRes::Error(guar), elision_candidate);
    }

    fn point_at_impl_lifetimes(&mut self, err: &mut Diag<'_>, i: usize, lifetime: Span) {
        let Some((rib, span)) =
            self.lifetime_ribs[..i].iter().rev().find_map(|rib| match rib.kind {
                LifetimeRibKind::Generics { span, kind: LifetimeBinderKind::ImplBlock, .. } => {
                    Some((rib, span))
                }
                _ => None,
            })
        else {
            return;
        };
        if !rib.bindings.is_empty() {
            err.span_label(
                span,
                format!(
                    "there {} named lifetime{} specified on the impl block you could use",
                    if rib.bindings.len() == 1 { "is a" } else { "are" },
                    pluralize!(rib.bindings.len()),
                ),
            );
            if rib.bindings.len() == 1 {
                err.span_suggestion_verbose(
                    lifetime.shrink_to_hi(),
                    "consider using the lifetime from the impl block",
                    format!("{} ", rib.bindings.keys().next().expect("invariant: iterator is non-empty")),
                    Applicability::MaybeIncorrect,
                );
            }
        } else {
            struct AnonRefFinder;
            impl<'ast> Visitor<'ast> for AnonRefFinder {
                type Result = ControlFlow<Span>;

                fn visit_ty(&mut self, ty: &'ast ast::Ty) -> Self::Result {
                    if let ast::TyKind::Ref(None, mut_ty) = &ty.kind {
                        return ControlFlow::Break(mut_ty.ty.span.shrink_to_lo());
                    }
                    visit::walk_ty(self, ty)
                }

                fn visit_lifetime(
                    &mut self,
                    lt: &'ast ast::Lifetime,
                    _cx: visit::LifetimeCtxt,
                ) -> Self::Result {
                    if lt.ident.name == kw::UnderscoreLifetime {
                        return ControlFlow::Break(lt.ident.span);
                    }
                    visit::walk_lifetime(self, lt)
                }
            }

            if let Some(ty) = &self.diag_metadata.current_self_type
                && let ControlFlow::Break(sp) = AnonRefFinder.visit_ty(ty)
            {
                err.multipart_suggestion(
                    "add a lifetime to the impl block and use it in the self type and associated \
                     type",
                    vec![
                        (span, "<'a>".to_string()),
                        (sp, "'a ".to_string()),
                        (lifetime.shrink_to_hi(), "'a ".to_string()),
                    ],
                    Applicability::MaybeIncorrect,
                );
            } else if let Some(item) = &self.diag_metadata.current_item
                && let ItemKind::Impl(impl_) = &item.kind
                && let Some(of_trait) = &impl_.of_trait
                && let ControlFlow::Break(sp) = AnonRefFinder.visit_trait_ref(&of_trait.trait_ref)
            {
                err.multipart_suggestion(
                    "add a lifetime to the impl block and use it in the trait and associated type",
                    vec![
                        (span, "<'a>".to_string()),
                        (sp, "'a".to_string()),
                        (lifetime.shrink_to_hi(), "'a ".to_string()),
                    ],
                    Applicability::MaybeIncorrect,
                );
            } else {
                err.span_label(
                    span,
                    "you could add a lifetime on the impl block, if the trait or the self type \
                     could have one",
                );
            }
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn resolve_elided_lifetime(&mut self, anchor_id: NodeId, span: Span) {
        let id = self.r.next_node_id();
        let lt = Lifetime { id, ident: Ident::new(kw::UnderscoreLifetime, span) };

        self.record_lifetime_res(
            anchor_id,
            LifetimeRes::ElidedAnchor { start: id, end: id + 1 },
            LifetimeElisionCandidate::Ignore,
        );
        self.resolve_anonymous_lifetime(&lt, anchor_id, true);
    }

    #[instrument(level = "debug", skip(self))]
    fn create_fresh_lifetime(
        &mut self,
        ident: Ident,
        binder: NodeId,
        kind: MissingLifetimeKind,
    ) -> LifetimeRes {
        debug_assert_eq!(ident.name, kw::UnderscoreLifetime);
        debug!(?ident.span);

        // Leave the responsibility to create the `LocalDefId` to lowering.
        let param = self.r.next_node_id();
        let res = LifetimeRes::Fresh { param, binder, kind };
        self.record_lifetime_param(param, res);

        // Record the created lifetime parameter so lowering can pick it up and add it to HIR.
        self.r
            .extra_lifetime_params_map
            .entry(binder)
            .or_insert_with(Vec::new)
            .push((ident, param, res));
        res
    }

    #[instrument(level = "debug", skip(self))]
    fn resolve_elided_lifetimes_in_path(
        &mut self,
        partial_res: PartialRes,
        path: &[Segment],
        source: PathSource<'_, 'ast, 'ra>,
        path_span: Span,
    ) {
        let proj_start = path.len() - partial_res.unresolved_segments();
        for (i, segment) in path.iter().enumerate() {
            if segment.has_lifetime_args {
                continue;
            }
            let Some(segment_id) = segment.id else {
                continue;
            };

            // Figure out if this is a type/trait segment,
            // which may need lifetime elision performed.
            let type_def_id = match partial_res.base_res() {
                Res::Def(DefKind::AssocTy, def_id) if i + 2 == proj_start => {
                    self.r.tcx.parent(def_id)
                }
                Res::Def(DefKind::Variant, def_id) if i + 1 == proj_start => {
                    self.r.tcx.parent(def_id)
                }
                Res::Def(DefKind::Struct, def_id)
                | Res::Def(DefKind::Union, def_id)
                | Res::Def(DefKind::Enum, def_id)
                | Res::Def(DefKind::TyAlias, def_id)
                | Res::Def(DefKind::Trait, def_id)
                    if i + 1 == proj_start =>
                {
                    def_id
                }
                _ => continue,
            };

            let expected_lifetimes = self.r.item_generics_num_lifetimes(type_def_id);
            if expected_lifetimes == 0 {
                continue;
            }

            let node_ids = self.r.next_node_ids(expected_lifetimes);
            self.record_lifetime_res(
                segment_id,
                LifetimeRes::ElidedAnchor { start: node_ids.start, end: node_ids.end },
                LifetimeElisionCandidate::Ignore,
            );

            let inferred = match source {
                PathSource::Trait(..)
                | PathSource::TraitItem(..)
                | PathSource::Type
                | PathSource::PreciseCapturingArg(..)
                | PathSource::ReturnTypeNotation
                | PathSource::Macro
                | PathSource::Module => false,
                PathSource::Expr(..)
                | PathSource::Pat
                | PathSource::Struct(_)
                | PathSource::TupleStruct(..)
                | PathSource::DefineOpaques
                | PathSource::Delegation => true,
            };
            if inferred {
                // Do not create a parameter for patterns and expressions: type checking can infer
                // the appropriate lifetime for us.
                for id in node_ids {
                    self.record_lifetime_res(
                        id,
                        LifetimeRes::Infer,
                        LifetimeElisionCandidate::Named,
                    );
                }
                continue;
            }

            let elided_lifetime_span = if segment.has_generic_args {
                // If there are brackets, but not generic arguments, then use the opening bracket
                segment.args_span.with_hi(segment.args_span.lo() + BytePos(1))
            } else {
                // If there are no brackets, use the identifier span.
                // tRust: known issue — we use find_ancestor_inside to properly suggest elided spans in paths
                // originating from macros, since the segment's span might be from a macro arg.
                segment.ident.span.find_ancestor_inside(path_span).unwrap_or(path_span)
            };
            let ident = Ident::new(kw::UnderscoreLifetime, elided_lifetime_span);

            let kind = if segment.has_generic_args {
                MissingLifetimeKind::Comma
            } else {
                MissingLifetimeKind::Brackets
            };
            let missing_lifetime = MissingLifetime {
                id: node_ids.start,
                id_for_lint: segment_id,
                span: elided_lifetime_span,
                kind,
                count: expected_lifetimes,
            };
            let mut should_lint = true;
            for rib in self.lifetime_ribs.iter().rev() {
                match rib.kind {
                    // In create-parameter mode we error here because we don't want to support
                    // deprecated impl elision in new features like impl elision and `async fn`,
                    // both of which work using the `CreateParameter` mode:
                    //
                    //     impl Foo for std::cell::Ref<u32> // note lack of '_
                    //     async fn foo(_: std::cell::Ref<u32>) { ... }
                    LifetimeRibKind::AnonymousCreateParameter { report_in_path: true, .. }
                    | LifetimeRibKind::StaticIfNoLifetimeInScope { .. } => {
                        let sess = self.r.tcx.sess;
                        let subdiag = rustc_errors::elided_lifetime_in_path_suggestion(
                            sess.source_map(),
                            expected_lifetimes,
                            path_span,
                            !segment.has_generic_args,
                            elided_lifetime_span,
                        );
                        let guar =
                            self.r.dcx().emit_err(errors::ImplicitElidedLifetimeNotAllowedHere {
                                span: path_span,
                                subdiag,
                            });
                        should_lint = false;

                        for id in node_ids {
                            self.record_lifetime_res(
                                id,
                                LifetimeRes::Error(guar),
                                LifetimeElisionCandidate::Named,
                            );
                        }
                        break;
                    }
                    // Do not create a parameter for patterns and expressions.
                    LifetimeRibKind::AnonymousCreateParameter { binder, .. } => {
                        // Group all suggestions into the first record.
                        let mut candidate = LifetimeElisionCandidate::Missing(missing_lifetime);
                        for id in node_ids {
                            let res = self.create_fresh_lifetime(ident, binder, kind);
                            self.record_lifetime_res(
                                id,
                                res,
                                replace(&mut candidate, LifetimeElisionCandidate::Named),
                            );
                        }
                        break;
                    }
                    LifetimeRibKind::Elided(res) => {
                        let mut candidate = LifetimeElisionCandidate::Missing(missing_lifetime);
                        for id in node_ids {
                            self.record_lifetime_res(
                                id,
                                res,
                                replace(&mut candidate, LifetimeElisionCandidate::Ignore),
                            );
                        }
                        break;
                    }
                    LifetimeRibKind::ElisionFailure => {
                        self.diag_metadata.current_elision_failures.push((
                            missing_lifetime,
                            LifetimeElisionCandidate::Ignore,
                            Either::Right(node_ids),
                        ));
                        break;
                    }
                    // `LifetimeRes::Error`, which would usually be used in the case of
                    // `ReportError`, is unsuitable here, as we don't emit an error yet. Instead,
                    // we simply resolve to an implicit lifetime, which will be checked later, at
                    // which point a suitable error will be emitted.
                    LifetimeRibKind::AnonymousReportError | LifetimeRibKind::Item => {
                        let guar =
                            self.report_missing_lifetime_specifiers([&missing_lifetime], None);
                        for id in node_ids {
                            self.record_lifetime_res(
                                id,
                                LifetimeRes::Error(guar),
                                LifetimeElisionCandidate::Ignore,
                            );
                        }
                        break;
                    }
                    LifetimeRibKind::Generics { .. } | LifetimeRibKind::ConstParamTy => {}
                    LifetimeRibKind::ConcreteAnonConst(_) => {
                        // There is always an `Elided(LifetimeRes::Infer)` inside an `AnonConst`.
                        // tRust: invariant — ConcreteAnonConst rib always has an inner Elided(Infer) rib, so this arm is unreachable
                        span_bug!(elided_lifetime_span, "unexpected rib kind: {:?}", rib.kind)
                    }
                }
            }

            if should_lint {
                self.r.lint_buffer.buffer_lint(
                    lint::builtin::ELIDED_LIFETIMES_IN_PATHS,
                    segment_id,
                    elided_lifetime_span,
                    lint::BuiltinLintDiag::ElidedLifetimesInPaths(
                        expected_lifetimes,
                        path_span,
                        !segment.has_generic_args,
                        elided_lifetime_span,
                    ),
                );
            }
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn record_lifetime_res(
        &mut self,
        id: NodeId,
        res: LifetimeRes,
        candidate: LifetimeElisionCandidate,
    ) {
        if let Some(prev_res) = self.r.lifetimes_res_map.insert(id, res) {
            panic!("lifetime {id:?} resolved multiple times ({prev_res:?} before, {res:?} now)")
        }

        match res {
            LifetimeRes::Param { .. } | LifetimeRes::Fresh { .. } | LifetimeRes::Static { .. } => {
                if let Some(ref mut candidates) = self.lifetime_elision_candidates {
                    candidates.push((res, candidate));
                }
            }
            LifetimeRes::Infer | LifetimeRes::Error(..) | LifetimeRes::ElidedAnchor { .. } => {}
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn record_lifetime_param(&mut self, id: NodeId, res: LifetimeRes) {
        if let Some(prev_res) = self.r.lifetimes_res_map.insert(id, res) {
            panic!(
                "lifetime parameter {id:?} resolved multiple times ({prev_res:?} before, {res:?} now)"
            )
        }
    }

    /// Perform resolution of a function signature, accounting for lifetime elision.
    #[instrument(level = "debug", skip(self, inputs))]
    fn resolve_fn_signature(
        &mut self,
        fn_id: NodeId,
        has_self: bool,
        inputs: impl Iterator<Item = (Option<&'ast Pat>, &'ast Ty)> + Clone,
        output_ty: &'ast FnRetTy,
        report_elided_lifetimes_in_path: bool,
    ) {
        let rib = LifetimeRibKind::AnonymousCreateParameter {
            binder: fn_id,
            report_in_path: report_elided_lifetimes_in_path,
        };
        self.with_lifetime_rib(rib, |this| {
            // Add each argument to the rib.
            let elision_lifetime = this.resolve_fn_params(has_self, inputs);
            debug!(?elision_lifetime);

            let outer_failures = take(&mut this.diag_metadata.current_elision_failures);
            let output_rib = if let Ok(res) = elision_lifetime.as_ref() {
                this.r.lifetime_elision_allowed.insert(fn_id);
                LifetimeRibKind::Elided(*res)
            } else {
                LifetimeRibKind::ElisionFailure
            };
            this.with_lifetime_rib(output_rib, |this| visit::walk_fn_ret_ty(this, output_ty));
            let elision_failures =
                replace(&mut this.diag_metadata.current_elision_failures, outer_failures);
            if !elision_failures.is_empty() {
                // tRust: invariant — if elision_failures is non-empty, elision_lifetime must be Err
                let Err(failure_info) = elision_lifetime else { bug!() };
                let guar = this.report_missing_lifetime_specifiers(
                    elision_failures.iter().map(|(missing_lifetime, ..)| missing_lifetime),
                    Some(failure_info),
                );
                let mut record_res = |lifetime, candidate| {
                    this.record_lifetime_res(lifetime, LifetimeRes::Error(guar), candidate)
                };
                for (_, candidate, nodes) in elision_failures {
                    match nodes {
                        Either::Left(node_id) => record_res(node_id, candidate),
                        Either::Right(node_ids) => {
                            for lifetime in node_ids {
                                record_res(lifetime, candidate)
                            }
                        }
                    }
                }
            }
        });
    }

    /// Resolve inside function parameters and parameter types.
    /// Returns the lifetime for elision in fn return type,
    /// or diagnostic information in case of elision failure.
    fn resolve_fn_params(
        &mut self,
        has_self: bool,
        inputs: impl Iterator<Item = (Option<&'ast Pat>, &'ast Ty)> + Clone,
    ) -> Result<LifetimeRes, (Vec<MissingLifetime>, Vec<ElisionFnParameter>)> {
        enum Elision {
            /// We have not found any candidate.
            None,
            /// We have a candidate bound to `self`.
            Self_(LifetimeRes),
            /// We have a candidate bound to a parameter.
            Param(LifetimeRes),
            /// We failed elision.
            Err,
        }

        // Save elision state to reinstate it later.
        let outer_candidates = self.lifetime_elision_candidates.take();

        // Result of elision.
        let mut elision_lifetime = Elision::None;
        // Information for diagnostics.
        let mut parameter_info = Vec::new();
        let mut all_candidates = Vec::new();

        // Resolve and apply bindings first so diagnostics can see if they're used in types.
        let mut bindings = smallvec![(PatBoundCtx::Product, Default::default())];
        for (pat, _) in inputs.clone() {
            debug!("resolving bindings in pat = {pat:?}");
            self.with_lifetime_rib(LifetimeRibKind::Elided(LifetimeRes::Infer), |this| {
                if let Some(pat) = pat {
                    this.resolve_pattern(pat, PatternSource::FnParam, &mut bindings);
                }
            });
        }
        self.apply_pattern_bindings(bindings);

        for (index, (pat, ty)) in inputs.enumerate() {
            debug!("resolving type for pat = {pat:?}, ty = {ty:?}");
            // Record elision candidates only for this parameter.
            debug_assert_matches!(self.lifetime_elision_candidates, None);
            self.lifetime_elision_candidates = Some(Default::default());
            self.visit_ty(ty);
            let local_candidates = self.lifetime_elision_candidates.take();

            if let Some(candidates) = local_candidates {
                let distinct: UnordSet<_> = candidates.iter().map(|(res, _)| *res).collect();
                let lifetime_count = distinct.len();
                if lifetime_count != 0 {
                    parameter_info.push(ElisionFnParameter {
                        index,
                        ident: if let Some(pat) = pat
                            && let PatKind::Ident(_, ident, _) = pat.kind
                        {
                            Some(ident)
                        } else {
                            None
                        },
                        lifetime_count,
                        span: ty.span,
                    });
                    all_candidates.extend(candidates.into_iter().filter_map(|(_, candidate)| {
                        match candidate {
                            LifetimeElisionCandidate::Ignore | LifetimeElisionCandidate::Named => {
                                None
                            }
                            LifetimeElisionCandidate::Missing(missing) => Some(missing),
                        }
                    }));
                }
                if !distinct.is_empty() {
                    match elision_lifetime {
                        // We are the first parameter to bind lifetimes.
                        Elision::None => {
                            if let Some(res) = distinct.get_only() {
                                // We have a single lifetime => success.
                                elision_lifetime = Elision::Param(*res)
                            } else {
                                // We have multiple lifetimes => error.
                                elision_lifetime = Elision::Err;
                            }
                        }
                        // We have 2 parameters that bind lifetimes => error.
                        Elision::Param(_) => elision_lifetime = Elision::Err,
                        // `self` elision takes precedence over everything else.
                        Elision::Self_(_) | Elision::Err => {}
                    }
                }
            }

            // Handle `self` specially.
            if index == 0 && has_self {
                let self_lifetime = self.find_lifetime_for_self(ty);
                elision_lifetime = match self_lifetime {
                    // We found `self` elision.
                    Set1::One(lifetime) => Elision::Self_(lifetime),
                    // `self` itself had ambiguous lifetimes, e.g.
                    // &Box<&Self>. In this case we won't consider
                    // taking an alternative parameter lifetime; just avoid elision
                    // entirely.
                    Set1::Many => Elision::Err,
                    // We do not have `self` elision: disregard the `Elision::Param` that we may
                    // have found.
                    Set1::Empty => Elision::None,
                }
            }
            debug!("(resolving function / closure) recorded parameter");
        }

        // Reinstate elision state.
        debug_assert_matches!(self.lifetime_elision_candidates, None);
        self.lifetime_elision_candidates = outer_candidates;

        if let Elision::Param(res) | Elision::Self_(res) = elision_lifetime {
            return Ok(res);
        }

        // We do not have a candidate.
        Err((all_candidates, parameter_info))
    }

    /// List all the lifetimes that appear in the provided type.
    fn find_lifetime_for_self(&self, ty: &'ast Ty) -> Set1<LifetimeRes> {
        /// Visits a type to find all the &references, and determines the
        /// set of lifetimes for all of those references where the referent
        /// contains Self.
        struct FindReferenceVisitor<'a, 'ra, 'tcx> {
            r: &'a Resolver<'ra, 'tcx>,
            impl_self: Option<Res>,
            lifetime: Set1<LifetimeRes>,
        }

        impl<'ra> Visitor<'ra> for FindReferenceVisitor<'_, '_, '_> {
            fn visit_ty(&mut self, ty: &'ra Ty) {
                trace!("FindReferenceVisitor considering ty={:?}", ty);
                if let TyKind::Ref(lt, _) | TyKind::PinnedRef(lt, _) = ty.kind {
                    // See if anything inside the &thing contains Self
                    let mut visitor =
                        SelfVisitor { r: self.r, impl_self: self.impl_self, self_found: false };
                    visitor.visit_ty(ty);
                    trace!("FindReferenceVisitor: SelfVisitor self_found={:?}", visitor.self_found);
                    if visitor.self_found {
                        let lt_id = if let Some(lt) = lt {
                            lt.id
                        } else {
                            let res = self.r.lifetimes_res_map[&ty.id];
                            // tRust: invariant — lifetime res for a type with self reference must be ElidedAnchor
                            let LifetimeRes::ElidedAnchor { start, .. } = res else { bug!() };
                            start
                        };
                        let lt_res = self.r.lifetimes_res_map[&lt_id];
                        trace!("FindReferenceVisitor inserting res={:?}", lt_res);
                        self.lifetime.insert(lt_res);
                    }
                }
                visit::walk_ty(self, ty)
            }

            // A type may have an expression as a const generic argument.
            // We do not want to recurse into those.
            fn visit_expr(&mut self, _: &'ra Expr) {}
        }

        /// Visitor which checks the referent of a &Thing to see if the
        /// Thing contains Self
        struct SelfVisitor<'a, 'ra, 'tcx> {
            r: &'a Resolver<'ra, 'tcx>,
            impl_self: Option<Res>,
            self_found: bool,
        }

        impl SelfVisitor<'_, '_, '_> {
            // Look for `self: &'a Self` - also desugared from `&'a self`
            fn is_self_ty(&self, ty: &Ty) -> bool {
                match ty.kind {
                    TyKind::ImplicitSelf => true,
                    TyKind::Path(None, _) => {
                        let path_res = self.r.partial_res_map[&ty.id].full_res();
                        if let Some(Res::SelfTyParam { .. } | Res::SelfTyAlias { .. }) = path_res {
                            return true;
                        }
                        self.impl_self.is_some() && path_res == self.impl_self
                    }
                    _ => false,
                }
            }
        }

        impl<'ra> Visitor<'ra> for SelfVisitor<'_, '_, '_> {
            fn visit_ty(&mut self, ty: &'ra Ty) {
                trace!("SelfVisitor considering ty={:?}", ty);
                if self.is_self_ty(ty) {
                    trace!("SelfVisitor found Self");
                    self.self_found = true;
                }
                visit::walk_ty(self, ty)
            }

            // A type may have an expression as a const generic argument.
            // We do not want to recurse into those.
            fn visit_expr(&mut self, _: &'ra Expr) {}
        }

        let impl_self = self
            .diag_metadata
            .current_self_type
            .as_ref()
            .and_then(|ty| {
                if let TyKind::Path(None, _) = ty.kind {
                    self.r.partial_res_map.get(&ty.id)
                } else {
                    None
                }
            })
            .and_then(|res| res.full_res())
            .filter(|res| {
                // Permit the types that unambiguously always
                // result in the same type constructor being used
                // (it can't differ between `Self` and `self`).
                matches!(
                    res,
                    Res::Def(DefKind::Struct | DefKind::Union | DefKind::Enum, _,) | Res::PrimTy(_)
                )
            });
        let mut visitor = FindReferenceVisitor { r: self.r, impl_self, lifetime: Set1::Empty };
        visitor.visit_ty(ty);
        trace!("FindReferenceVisitor found={:?}", visitor.lifetime);
        visitor.lifetime
    }

    /// Searches the current set of local scopes for labels. Returns the `NodeId` of the resolved
    /// label and reports an error if the label is not found or is unreachable.

}
