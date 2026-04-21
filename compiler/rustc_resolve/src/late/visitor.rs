// tRust: Split from late.rs -- Visitor trait implementation for LateResolutionVisitor.
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


/// Walks the whole crate in DFS order, visiting each item, resolving names as it goes.
impl<'ast, 'ra, 'tcx> Visitor<'ast> for LateResolutionVisitor<'_, 'ast, 'ra, 'tcx> {
    fn visit_attribute(&mut self, _: &'ast Attribute) {
        // We do not want to resolve expressions that appear in attributes,
        // as they do not correspond to actual code.
    }
    fn visit_item(&mut self, item: &'ast Item) {
        let prev = replace(&mut self.diag_metadata.current_item, Some(item));
        // Always report errors in items we just entered.
        let old_ignore = replace(&mut self.in_func_body, false);
        self.with_lifetime_rib(LifetimeRibKind::Item, |this| this.resolve_item(item));
        self.in_func_body = old_ignore;
        self.diag_metadata.current_item = prev;
    }
    fn visit_arm(&mut self, arm: &'ast Arm) {
        self.resolve_arm(arm);
    }
    fn visit_block(&mut self, block: &'ast Block) {
        let old_macro_rules = self.parent_scope.macro_rules;
        self.resolve_block(block);
        self.parent_scope.macro_rules = old_macro_rules;
    }
    fn visit_anon_const(&mut self, constant: &'ast AnonConst) {
        // tRust: invariant — anonymous constants must be visited via resolve_anon_const, never through the general visitor
        bug!("encountered anon const without a manual call to `resolve_anon_const`: {constant:#?}");
    }
    fn visit_expr(&mut self, expr: &'ast Expr) {
        self.resolve_expr(expr, None);
    }
    fn visit_pat(&mut self, p: &'ast Pat) {
        let prev = self.diag_metadata.current_pat;
        self.diag_metadata.current_pat = Some(p);

        if let PatKind::Guard(subpat, _) = &p.kind {
            // We walk the guard expression in `resolve_pattern_inner`. Don't resolve it twice.
            self.visit_pat(subpat);
        } else {
            visit::walk_pat(self, p);
        }

        self.diag_metadata.current_pat = prev;
    }
    fn visit_local(&mut self, local: &'ast Local) {
        let local_spans = match local.pat.kind {
            // We check for this to avoid tuple struct fields.
            PatKind::Wild => None,
            _ => Some((
                local.pat.span,
                local.ty.as_ref().map(|ty| ty.span),
                local.kind.init().map(|init| init.span),
            )),
        };
        let original = replace(&mut self.diag_metadata.current_let_binding, local_spans);
        self.resolve_local(local);
        self.diag_metadata.current_let_binding = original;
    }
    fn visit_ty(&mut self, ty: &'ast Ty) {
        let prev = self.diag_metadata.current_trait_object;
        let prev_ty = self.diag_metadata.current_type_path;
        match &ty.kind {
            TyKind::Ref(None, _) | TyKind::PinnedRef(None, _) => {
                // Elided lifetime in reference: we resolve as if there was some lifetime `'_` with
                // NodeId `ty.id`.
                // This span will be used in case of elision failure.
                let span = self.r.tcx.sess.source_map().start_point(ty.span);
                self.resolve_elided_lifetime(ty.id, span);
                visit::walk_ty(self, ty);
            }
            TyKind::Path(qself, path) => {
                self.diag_metadata.current_type_path = Some(ty);

                // If we have a path that ends with `(..)`, then it must be
                // return type notation. Resolve that path in the *value*
                // namespace.
                let source = if let Some(seg) = path.segments.last()
                    && let Some(args) = &seg.args
                    && matches!(**args, GenericArgs::ParenthesizedElided(..))
                {
                    PathSource::ReturnTypeNotation
                } else {
                    PathSource::Type
                };

                self.smart_resolve_path(ty.id, qself, path, source);

                // Check whether we should interpret this as a bare trait object.
                if qself.is_none()
                    && let Some(partial_res) = self.r.partial_res_map.get(&ty.id)
                    && let Some(Res::Def(DefKind::Trait | DefKind::TraitAlias, _)) =
                        partial_res.full_res()
                {
                    // This path is actually a bare trait object. In case of a bare `Fn`-trait
                    // object with anonymous lifetimes, we need this rib to correctly place the
                    // synthetic lifetimes.
                    let span = ty.span.shrink_to_lo().to(path.span.shrink_to_lo());
                    self.with_generic_param_rib(
                        &[],
                        RibKind::Normal,
                        ty.id,
                        LifetimeBinderKind::PolyTrait,
                        span,
                        |this| this.visit_path(path),
                    );
                } else {
                    visit::walk_ty(self, ty)
                }
            }
            TyKind::ImplicitSelf => {
                let self_ty = Ident::with_dummy_span(kw::SelfUpper);
                let res = self
                    .resolve_ident_in_lexical_scope(
                        self_ty,
                        TypeNS,
                        Some(Finalize::new(ty.id, ty.span)),
                        None,
                    )
                    .map_or(Res::Err, |d| d.res());
                self.r.record_partial_res(ty.id, PartialRes::new(res));
                visit::walk_ty(self, ty)
            }
            TyKind::ImplTrait(..) => {
                let candidates = self.lifetime_elision_candidates.take();
                visit::walk_ty(self, ty);
                self.lifetime_elision_candidates = candidates;
            }
            TyKind::TraitObject(bounds, ..) => {
                self.diag_metadata.current_trait_object = Some(&bounds[..]);
                visit::walk_ty(self, ty)
            }
            TyKind::FnPtr(fn_ptr) => {
                let span = ty.span.shrink_to_lo().to(fn_ptr.decl_span.shrink_to_lo());
                self.with_generic_param_rib(
                    &fn_ptr.generic_params,
                    RibKind::Normal,
                    ty.id,
                    LifetimeBinderKind::FnPtrType,
                    span,
                    |this| {
                        this.visit_generic_params(&fn_ptr.generic_params, false);
                        this.resolve_fn_signature(
                            ty.id,
                            false,
                            // We don't need to deal with patterns in parameters, because
                            // they are not possible for foreign or bodiless functions.
                            fn_ptr.decl.inputs.iter().map(|Param { ty, .. }| (None, &**ty)),
                            &fn_ptr.decl.output,
                            false,
                        )
                    },
                )
            }
            TyKind::UnsafeBinder(unsafe_binder) => {
                let span = ty.span.shrink_to_lo().to(unsafe_binder.inner_ty.span.shrink_to_lo());
                self.with_generic_param_rib(
                    &unsafe_binder.generic_params,
                    RibKind::Normal,
                    ty.id,
                    LifetimeBinderKind::FnPtrType,
                    span,
                    |this| {
                        this.visit_generic_params(&unsafe_binder.generic_params, false);
                        this.with_lifetime_rib(
                            // We don't allow anonymous `unsafe &'_ ()` binders,
                            // although I guess we could.
                            LifetimeRibKind::AnonymousReportError,
                            |this| this.visit_ty(&unsafe_binder.inner_ty),
                        );
                    },
                )
            }
            TyKind::Array(element_ty, length) => {
                self.visit_ty(element_ty);
                self.resolve_anon_const(length, AnonConstKind::ConstArg(IsRepeatExpr::No));
            }
            _ => visit::walk_ty(self, ty),
        }
        self.diag_metadata.current_trait_object = prev;
        self.diag_metadata.current_type_path = prev_ty;
    }

    fn visit_ty_pat(&mut self, t: &'ast TyPat) -> Self::Result {
        match &t.kind {
            TyPatKind::Range(start, end, _) => {
                if let Some(start) = start {
                    self.resolve_anon_const(start, AnonConstKind::ConstArg(IsRepeatExpr::No));
                }
                if let Some(end) = end {
                    self.resolve_anon_const(end, AnonConstKind::ConstArg(IsRepeatExpr::No));
                }
            }
            TyPatKind::Or(patterns) => {
                for pat in patterns {
                    self.visit_ty_pat(pat)
                }
            }
            TyPatKind::NotNull | TyPatKind::Err(_) => {}
        }
    }

    fn visit_poly_trait_ref(&mut self, tref: &'ast PolyTraitRef) {
        let span = tref.span.shrink_to_lo().to(tref.trait_ref.path.span.shrink_to_lo());
        self.with_generic_param_rib(
            &tref.bound_generic_params,
            RibKind::Normal,
            tref.trait_ref.ref_id,
            LifetimeBinderKind::PolyTrait,
            span,
            |this| {
                this.visit_generic_params(&tref.bound_generic_params, false);
                this.smart_resolve_path(
                    tref.trait_ref.ref_id,
                    &None,
                    &tref.trait_ref.path,
                    PathSource::Trait(AliasPossibility::Maybe),
                );
                this.visit_trait_ref(&tref.trait_ref);
            },
        );
    }
    fn visit_foreign_item(&mut self, foreign_item: &'ast ForeignItem) {
        self.resolve_doc_links(&foreign_item.attrs, MaybeExported::Ok(foreign_item.id));
        let def_kind = self.r.local_def_kind(foreign_item.id);
        match foreign_item.kind {
            ForeignItemKind::TyAlias(box TyAlias { ref generics, .. }) => {
                self.with_generic_param_rib(
                    &generics.params,
                    RibKind::Item(HasGenericParams::Yes(generics.span), def_kind),
                    foreign_item.id,
                    LifetimeBinderKind::Item,
                    generics.span,
                    |this| visit::walk_item(this, foreign_item),
                );
            }
            ForeignItemKind::Fn(box Fn { ref generics, .. }) => {
                self.with_generic_param_rib(
                    &generics.params,
                    RibKind::Item(HasGenericParams::Yes(generics.span), def_kind),
                    foreign_item.id,
                    LifetimeBinderKind::Function,
                    generics.span,
                    |this| visit::walk_item(this, foreign_item),
                );
            }
            ForeignItemKind::Static(..) => {
                self.with_static_rib(def_kind, |this| visit::walk_item(this, foreign_item))
            }
            ForeignItemKind::MacCall(..) => {
                panic!("unexpanded macro in resolve!")
            }
        }
    }
    fn visit_fn(&mut self, fn_kind: FnKind<'ast>, _: &AttrVec, sp: Span, fn_id: NodeId) {
        let previous_value = self.diag_metadata.current_function;
        match fn_kind {
            // Bail if the function is foreign, and thus cannot validly have
            // a body, or if there's no body for some other reason.
            FnKind::Fn(FnCtxt::Foreign, _, Fn { sig, ident, generics, .. })
            | FnKind::Fn(_, _, Fn { sig, ident, generics, body: None, .. }) => {
                self.visit_fn_header(&sig.header);
                self.visit_ident(ident);
                self.visit_generics(generics);
                self.resolve_fn_signature(
                    fn_id,
                    sig.decl.has_self(),
                    sig.decl.inputs.iter().map(|Param { ty, .. }| (None, &**ty)),
                    &sig.decl.output,
                    false,
                );
                return;
            }
            FnKind::Fn(..) => {
                self.diag_metadata.current_function = Some((fn_kind, sp));
            }
            // Do not update `current_function` for closures: it suggests `self` parameters.
            FnKind::Closure(..) => {}
        };
        debug!("(resolving function) entering function");

        if let FnKind::Fn(_, _, f) = fn_kind {
            for EiiImpl { node_id, eii_macro_path, known_eii_macro_resolution, .. } in &f.eii_impls
            {
                // See docs on the `known_eii_macro_resolution` field:
                // if we already know the resolution statically, don't bother resolving it.
                if let Some(target) = known_eii_macro_resolution {
                    self.smart_resolve_path(
                        *node_id,
                        &None,
                        &target.foreign_item,
                        PathSource::Expr(None),
                    );
                } else {
                    self.smart_resolve_path(*node_id, &None, &eii_macro_path, PathSource::Macro);
                }
            }
        }

        // Create a value rib for the function.
        self.with_rib(ValueNS, RibKind::FnOrCoroutine, |this| {
            // Create a label rib for the function.
            this.with_label_rib(RibKind::FnOrCoroutine, |this| {
                match fn_kind {
                    FnKind::Fn(_, _, Fn { sig, generics, contract, body, .. }) => {
                        this.visit_generics(generics);

                        let declaration = &sig.decl;
                        let coro_node_id = sig
                            .header
                            .coroutine_kind
                            .map(|coroutine_kind| coroutine_kind.return_id());

                        this.resolve_fn_signature(
                            fn_id,
                            declaration.has_self(),
                            declaration
                                .inputs
                                .iter()
                                .map(|Param { pat, ty, .. }| (Some(&**pat), &**ty)),
                            &declaration.output,
                            coro_node_id.is_some(),
                        );

                        if let Some(contract) = contract {
                            this.visit_contract(contract);
                        }

                        if let Some(body) = body {
                            // Ignore errors in function bodies if this is rustdoc
                            // Be sure not to set this until the function signature has been resolved.
                            let previous_state = replace(&mut this.in_func_body, true);
                            // We only care block in the same function
                            this.last_block_rib = None;
                            // Resolve the function body, potentially inside the body of an async closure
                            this.with_lifetime_rib(
                                LifetimeRibKind::Elided(LifetimeRes::Infer),
                                |this| this.visit_block(body),
                            );

                            debug!("(resolving function) leaving function");
                            this.in_func_body = previous_state;
                        }
                    }
                    FnKind::Closure(binder, _, declaration, body) => {
                        this.visit_closure_binder(binder);

                        this.with_lifetime_rib(
                            match binder {
                                // We do not have any explicit generic lifetime parameter.
                                ClosureBinder::NotPresent => {
                                    LifetimeRibKind::AnonymousCreateParameter {
                                        binder: fn_id,
                                        report_in_path: false,
                                    }
                                }
                                ClosureBinder::For { .. } => LifetimeRibKind::AnonymousReportError,
                            },
                            // Add each argument to the rib.
                            |this| this.resolve_params(&declaration.inputs),
                        );
                        this.with_lifetime_rib(
                            match binder {
                                ClosureBinder::NotPresent => {
                                    LifetimeRibKind::Elided(LifetimeRes::Infer)
                                }
                                ClosureBinder::For { .. } => LifetimeRibKind::AnonymousReportError,
                            },
                            |this| visit::walk_fn_ret_ty(this, &declaration.output),
                        );

                        // Ignore errors in function bodies if this is rustdoc
                        // Be sure not to set this until the function signature has been resolved.
                        let previous_state = replace(&mut this.in_func_body, true);
                        // Resolve the function body, potentially inside the body of an async closure
                        this.with_lifetime_rib(
                            LifetimeRibKind::Elided(LifetimeRes::Infer),
                            |this| this.visit_expr(body),
                        );

                        debug!("(resolving function) leaving function");
                        this.in_func_body = previous_state;
                    }
                }
            })
        });
        self.diag_metadata.current_function = previous_value;
    }

    fn visit_lifetime(&mut self, lifetime: &'ast Lifetime, use_ctxt: visit::LifetimeCtxt) {
        self.resolve_lifetime(lifetime, use_ctxt)
    }

    fn visit_precise_capturing_arg(&mut self, arg: &'ast PreciseCapturingArg) {
        match arg {
            // Lower the lifetime regularly; we'll resolve the lifetime and check
            // it's a parameter later on in HIR lowering.
            PreciseCapturingArg::Lifetime(_) => {}

            PreciseCapturingArg::Arg(path, id) => {
                // we want `impl use<C>` to try to resolve `C` as both a type parameter or
                // a const parameter. Since the resolver specifically doesn't allow having
                // two generic params with the same name, even if they're a different namespace,
                // it doesn't really matter which we try resolving first, but just like
                // `Ty::Param` we just fall back to the value namespace only if it's missing
                // from the type namespace.
                let mut check_ns = |ns| {
                    self.maybe_resolve_ident_in_lexical_scope(path.segments[0].ident, ns).is_some()
                };
                // Like `Ty::Param`, we try resolving this as both a const and a type.
                if !check_ns(TypeNS) && check_ns(ValueNS) {
                    self.smart_resolve_path(
                        *id,
                        &None,
                        path,
                        PathSource::PreciseCapturingArg(ValueNS),
                    );
                } else {
                    self.smart_resolve_path(
                        *id,
                        &None,
                        path,
                        PathSource::PreciseCapturingArg(TypeNS),
                    );
                }
            }
        }

        visit::walk_precise_capturing_arg(self, arg)
    }

    fn visit_generics(&mut self, generics: &'ast Generics) {
        self.visit_generic_params(&generics.params, self.diag_metadata.current_self_item.is_some());
        for p in &generics.where_clause.predicates {
            self.visit_where_predicate(p);
        }
    }

    fn visit_closure_binder(&mut self, b: &'ast ClosureBinder) {
        match b {
            ClosureBinder::NotPresent => {}
            ClosureBinder::For { generic_params, .. } => {
                self.visit_generic_params(
                    generic_params,
                    self.diag_metadata.current_self_item.is_some(),
                );
            }
        }
    }

    fn visit_generic_arg(&mut self, arg: &'ast GenericArg) {
        debug!("visit_generic_arg({:?})", arg);
        let prev = replace(&mut self.diag_metadata.currently_processing_generic_args, true);
        match arg {
            GenericArg::Type(ty) => {
                // We parse const arguments as path types as we cannot distinguish them during
                // parsing. We try to resolve that ambiguity by attempting resolution the type
                // namespace first, and if that fails we try again in the value namespace. If
                // resolution in the value namespace succeeds, we have an generic const argument on
                // our hands.
                if let TyKind::Path(None, ref path) = ty.kind
                    // We cannot disambiguate multi-segment paths right now as that requires type
                    // checking.
                    && path.is_potential_trivial_const_arg()
                {
                    let mut check_ns = |ns| {
                        self.maybe_resolve_ident_in_lexical_scope(path.segments[0].ident, ns)
                            .is_some()
                    };
                    if !check_ns(TypeNS) && check_ns(ValueNS) {
                        self.resolve_anon_const_manual(
                            true,
                            AnonConstKind::ConstArg(IsRepeatExpr::No),
                            |this| {
                                this.smart_resolve_path(ty.id, &None, path, PathSource::Expr(None));
                                this.visit_path(path);
                            },
                        );

                        self.diag_metadata.currently_processing_generic_args = prev;
                        return;
                    }
                }

                self.visit_ty(ty);
            }
            GenericArg::Lifetime(lt) => self.visit_lifetime(lt, visit::LifetimeCtxt::GenericArg),
            GenericArg::Const(ct) => {
                self.resolve_anon_const(ct, AnonConstKind::ConstArg(IsRepeatExpr::No))
            }
        }
        self.diag_metadata.currently_processing_generic_args = prev;
    }

    fn visit_assoc_item_constraint(&mut self, constraint: &'ast AssocItemConstraint) {
        self.visit_ident(&constraint.ident);
        if let Some(ref gen_args) = constraint.gen_args {
            // Forbid anonymous lifetimes in GAT parameters until proper semantics are decided.
            self.with_lifetime_rib(LifetimeRibKind::AnonymousReportError, |this| {
                this.visit_generic_args(gen_args)
            });
        }
        match constraint.kind {
            AssocItemConstraintKind::Equality { ref term } => match term {
                Term::Ty(ty) => self.visit_ty(ty),
                Term::Const(c) => {
                    self.resolve_anon_const(c, AnonConstKind::ConstArg(IsRepeatExpr::No))
                }
            },
            AssocItemConstraintKind::Bound { ref bounds } => {
                walk_list!(self, visit_param_bound, bounds, BoundKind::Bound);
            }
        }
    }

    fn visit_path_segment(&mut self, path_segment: &'ast PathSegment) {
        let Some(ref args) = path_segment.args else {
            return;
        };

        match &**args {
            GenericArgs::AngleBracketed(..) => visit::walk_generic_args(self, args),
            GenericArgs::Parenthesized(p_args) => {
                // Probe the lifetime ribs to know how to behave.
                for rib in self.lifetime_ribs.iter().rev() {
                    match rib.kind {
                        // We are inside a `PolyTraitRef`. The lifetimes are
                        // to be introduced in that (maybe implicit) `for<>` binder.
                        LifetimeRibKind::Generics {
                            binder,
                            kind: LifetimeBinderKind::PolyTrait,
                            ..
                        } => {
                            self.resolve_fn_signature(
                                binder,
                                false,
                                p_args.inputs.iter().map(|ty| (None, &**ty)),
                                &p_args.output,
                                false,
                            );
                            break;
                        }
                        // We have nowhere to introduce generics. Code is malformed,
                        // so use regular lifetime resolution to avoid spurious errors.
                        LifetimeRibKind::Item | LifetimeRibKind::Generics { .. } => {
                            visit::walk_generic_args(self, args);
                            break;
                        }
                        LifetimeRibKind::AnonymousCreateParameter { .. }
                        | LifetimeRibKind::AnonymousReportError
                        | LifetimeRibKind::StaticIfNoLifetimeInScope { .. }
                        | LifetimeRibKind::Elided(_)
                        | LifetimeRibKind::ElisionFailure
                        | LifetimeRibKind::ConcreteAnonConst(_)
                        | LifetimeRibKind::ConstParamTy => {}
                    }
                }
            }
            GenericArgs::ParenthesizedElided(_) => {}
        }
    }

    fn visit_where_predicate(&mut self, p: &'ast WherePredicate) {
        debug!("visit_where_predicate {:?}", p);
        let previous_value = replace(&mut self.diag_metadata.current_where_predicate, Some(p));
        self.with_lifetime_rib(LifetimeRibKind::AnonymousReportError, |this| {
            if let WherePredicateKind::BoundPredicate(WhereBoundPredicate {
                bounded_ty,
                bounds,
                bound_generic_params,
                ..
            }) = &p.kind
            {
                let span = p.span.shrink_to_lo().to(bounded_ty.span.shrink_to_lo());
                this.with_generic_param_rib(
                    bound_generic_params,
                    RibKind::Normal,
                    bounded_ty.id,
                    LifetimeBinderKind::WhereBound,
                    span,
                    |this| {
                        this.visit_generic_params(bound_generic_params, false);
                        this.visit_ty(bounded_ty);
                        for bound in bounds {
                            this.visit_param_bound(bound, BoundKind::Bound)
                        }
                    },
                );
            } else {
                visit::walk_where_predicate(this, p);
            }
        });
        self.diag_metadata.current_where_predicate = previous_value;
    }

    fn visit_inline_asm(&mut self, asm: &'ast InlineAsm) {
        for (op, _) in &asm.operands {
            match op {
                InlineAsmOperand::In { expr, .. }
                | InlineAsmOperand::Out { expr: Some(expr), .. }
                | InlineAsmOperand::InOut { expr, .. } => self.visit_expr(expr),
                InlineAsmOperand::Out { expr: None, .. } => {}
                InlineAsmOperand::SplitInOut { in_expr, out_expr, .. } => {
                    self.visit_expr(in_expr);
                    if let Some(out_expr) = out_expr {
                        self.visit_expr(out_expr);
                    }
                }
                InlineAsmOperand::Const { anon_const, .. } => {
                    // Although this is `DefKind::AnonConst`, it is allowed to reference outer
                    // generic parameters like an inline const.
                    self.resolve_anon_const(anon_const, AnonConstKind::InlineConst);
                }
                InlineAsmOperand::Sym { sym } => self.visit_inline_asm_sym(sym),
                InlineAsmOperand::Label { block } => self.visit_block(block),
            }
        }
    }

    fn visit_inline_asm_sym(&mut self, sym: &'ast InlineAsmSym) {
        // This is similar to the code for AnonConst.
        self.with_rib(ValueNS, RibKind::InlineAsmSym, |this| {
            this.with_rib(TypeNS, RibKind::InlineAsmSym, |this| {
                this.with_label_rib(RibKind::InlineAsmSym, |this| {
                    this.smart_resolve_path(sym.id, &sym.qself, &sym.path, PathSource::Expr(None));
                    visit::walk_inline_asm_sym(this, sym);
                });
            })
        });
    }

    fn visit_variant(&mut self, v: &'ast Variant) {
        self.resolve_doc_links(&v.attrs, MaybeExported::Ok(v.id));
        self.visit_id(v.id);
        walk_list!(self, visit_attribute, &v.attrs);
        self.visit_vis(&v.vis);
        self.visit_ident(&v.ident);
        self.visit_variant_data(&v.data);
        if let Some(discr) = &v.disr_expr {
            self.resolve_anon_const(discr, AnonConstKind::EnumDiscriminant);
        }
    }

    fn visit_field_def(&mut self, f: &'ast FieldDef) {
        self.resolve_doc_links(&f.attrs, MaybeExported::Ok(f.id));
        let FieldDef {
            attrs,
            id: _,
            span: _,
            vis,
            ident,
            ty,
            is_placeholder: _,
            default,
            safety: _,
        } = f;
        walk_list!(self, visit_attribute, attrs);
        try_visit!(self.visit_vis(vis));
        visit_opt!(self, visit_ident, ident);
        try_visit!(self.visit_ty(ty));
        if let Some(v) = &default {
            self.resolve_anon_const(v, AnonConstKind::FieldDefaultValue);
        }
    }
}
