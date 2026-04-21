// tRust: Split from late.rs -- item resolution methods.
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
    fn resolve_label(&self, mut label: Ident) -> Result<(NodeId, Span), ResolutionError<'ra>> {
        let mut suggestion = None;

        for i in (0..self.label_ribs.len()).rev() {
            let rib = &self.label_ribs[i];

            if let RibKind::MacroDefinition(def) = rib.kind
                // If an invocation of this macro created `ident`, give up on `ident`
                // and switch to `ident`'s source from the macro definition.
                && def == self.r.macro_def(label.span.ctxt())
            {
                label.span.remove_mark();
            }

            let ident = label.normalize_to_macro_rules();
            if let Some((ident, id)) = rib.bindings.get_key_value(&ident) {
                let definition_span = ident.span;
                return if self.is_label_valid_from_rib(i) {
                    Ok((*id, definition_span))
                } else {
                    Err(ResolutionError::UnreachableLabel {
                        name: label.name,
                        definition_span,
                        suggestion,
                    })
                };
            }

            // Diagnostics: Check if this rib contains a label with a similar name, keep track of
            // the first such label that is encountered.
            suggestion = suggestion.or_else(|| self.suggestion_for_label_in_rib(i, label));
        }

        Err(ResolutionError::UndeclaredLabel { name: label.name, suggestion })
    }

    /// Determine whether or not a label from the `rib_index`th label rib is reachable.
    fn is_label_valid_from_rib(&self, rib_index: usize) -> bool {
        let ribs = &self.label_ribs[rib_index + 1..];
        ribs.iter().all(|rib| !rib.kind.is_label_barrier())
    }

    fn resolve_adt(&mut self, item: &'ast Item, generics: &'ast Generics) {
        debug!("resolve_adt");
        let kind = self.r.local_def_kind(item.id);
        self.with_current_self_item(item, |this| {
            this.with_generic_param_rib(
                &generics.params,
                RibKind::Item(HasGenericParams::Yes(generics.span), kind),
                item.id,
                LifetimeBinderKind::Item,
                generics.span,
                |this| {
                    let item_def_id = this.r.local_def_id(item.id).to_def_id();
                    this.with_self_rib(
                        Res::SelfTyAlias { alias_to: item_def_id, is_trait_impl: false },
                        |this| {
                            visit::walk_item(this, item);
                        },
                    );
                },
            );
        });
    }

    fn future_proof_import(&mut self, use_tree: &UseTree) {
        if let [segment, rest @ ..] = use_tree.prefix.segments.as_slice() {
            let ident = segment.ident;
            if ident.is_path_segment_keyword() || ident.span.is_rust_2015() {
                return;
            }

            let nss = match use_tree.kind {
                UseTreeKind::Simple(..) if rest.is_empty() => &[TypeNS, ValueNS][..],
                _ => &[TypeNS],
            };
            let report_error = |this: &Self, ns| {
                if this.should_report_errs() {
                    let what = if ns == TypeNS { "type parameters" } else { "local variables" };
                    this.r.dcx().emit_err(errors::ImportsCannotReferTo { span: ident.span, what });
                }
            };

            for &ns in nss {
                match self.maybe_resolve_ident_in_lexical_scope(ident, ns) {
                    Some(LateDecl::RibDef(..)) => {
                        report_error(self, ns);
                    }
                    Some(LateDecl::Decl(binding)) => {
                        if let Some(LateDecl::RibDef(..)) =
                            self.resolve_ident_in_lexical_scope(ident, ns, None, Some(binding))
                        {
                            report_error(self, ns);
                        }
                    }
                    None => {}
                }
            }
        } else if let UseTreeKind::Nested { items, .. } = &use_tree.kind {
            for (use_tree, _) in items {
                self.future_proof_import(use_tree);
            }
        }
    }

    fn resolve_item(&mut self, item: &'ast Item) {
        let mod_inner_docs =
            matches!(item.kind, ItemKind::Mod(..)) && rustdoc::inner_docs(&item.attrs);
        if !mod_inner_docs && !matches!(item.kind, ItemKind::Impl(..) | ItemKind::Use(..)) {
            self.resolve_doc_links(&item.attrs, MaybeExported::Ok(item.id));
        }

        debug!("(resolving item) resolving {:?} ({:?})", item.kind.ident(), item.kind);

        let def_kind = self.r.local_def_kind(item.id);
        match &item.kind {
            ItemKind::TyAlias(box TyAlias { generics, .. }) => {
                self.with_generic_param_rib(
                    &generics.params,
                    RibKind::Item(HasGenericParams::Yes(generics.span), def_kind),
                    item.id,
                    LifetimeBinderKind::Item,
                    generics.span,
                    |this| visit::walk_item(this, item),
                );
            }

            ItemKind::Fn(box Fn { generics, define_opaque, .. }) => {
                self.with_generic_param_rib(
                    &generics.params,
                    RibKind::Item(HasGenericParams::Yes(generics.span), def_kind),
                    item.id,
                    LifetimeBinderKind::Function,
                    generics.span,
                    |this| visit::walk_item(this, item),
                );
                self.resolve_define_opaques(define_opaque);
            }

            ItemKind::Enum(_, generics, _)
            | ItemKind::Struct(_, generics, _)
            | ItemKind::Union(_, generics, _) => {
                self.resolve_adt(item, generics);
            }

            ItemKind::Impl(Impl { generics, of_trait, self_ty, items: impl_items, .. }) => {
                self.diag_metadata.current_impl_items = Some(impl_items);
                self.resolve_implementation(
                    &item.attrs,
                    generics,
                    of_trait.as_deref(),
                    self_ty,
                    item.id,
                    impl_items,
                );
                self.diag_metadata.current_impl_items = None;
            }

            ItemKind::Trait(box Trait { generics, bounds, items, impl_restriction, .. }) => {
                // resolve paths for `impl` restrictions
                self.resolve_impl_restriction_path(impl_restriction);

                // Create a new rib for the trait-wide type parameters.
                self.with_generic_param_rib(
                    &generics.params,
                    RibKind::Item(HasGenericParams::Yes(generics.span), def_kind),
                    item.id,
                    LifetimeBinderKind::Item,
                    generics.span,
                    |this| {
                        let local_def_id = this.r.local_def_id(item.id).to_def_id();
                        this.with_self_rib(Res::SelfTyParam { trait_: local_def_id }, |this| {
                            this.visit_generics(generics);
                            walk_list!(this, visit_param_bound, bounds, BoundKind::SuperTraits);
                            this.resolve_trait_items(items);
                        });
                    },
                );
            }

            ItemKind::TraitAlias(box TraitAlias { generics, bounds, .. }) => {
                // Create a new rib for the trait-wide type parameters.
                self.with_generic_param_rib(
                    &generics.params,
                    RibKind::Item(HasGenericParams::Yes(generics.span), def_kind),
                    item.id,
                    LifetimeBinderKind::Item,
                    generics.span,
                    |this| {
                        let local_def_id = this.r.local_def_id(item.id).to_def_id();
                        this.with_self_rib(Res::SelfTyParam { trait_: local_def_id }, |this| {
                            this.visit_generics(generics);
                            walk_list!(this, visit_param_bound, bounds, BoundKind::Bound);
                        });
                    },
                );
            }

            ItemKind::Mod(..) => {
                let module = self.r.expect_module(self.r.local_def_id(item.id).to_def_id());
                let orig_module = replace(&mut self.parent_scope.module, module);
                self.with_rib(ValueNS, RibKind::Module(module), |this| {
                    this.with_rib(TypeNS, RibKind::Module(module), |this| {
                        if mod_inner_docs {
                            this.resolve_doc_links(&item.attrs, MaybeExported::Ok(item.id));
                        }
                        let old_macro_rules = this.parent_scope.macro_rules;
                        visit::walk_item(this, item);
                        // Maintain macro_rules scopes in the same way as during early resolution
                        // for diagnostics and doc links.
                        if item.attrs.iter().all(|attr| {
                            !attr.has_name(sym::macro_use) && !attr.has_name(sym::macro_escape)
                        }) {
                            this.parent_scope.macro_rules = old_macro_rules;
                        }
                    })
                });
                self.parent_scope.module = orig_module;
            }

            ItemKind::Static(box ast::StaticItem { ident, ty, expr, define_opaque, .. }) => {
                self.with_static_rib(def_kind, |this| {
                    this.with_lifetime_rib(LifetimeRibKind::Elided(LifetimeRes::Static), |this| {
                        this.visit_ty(ty);
                    });
                    if let Some(expr) = expr {
                        // We already forbid generic params because of the above item rib,
                        // so it doesn't matter whether this is a trivial constant.
                        this.resolve_static_body(expr, Some((*ident, ConstantItemKind::Static)));
                    }
                });
                self.resolve_define_opaques(define_opaque);
            }

            ItemKind::Const(box ast::ConstItem {
                ident,
                generics,
                ty,
                rhs_kind,
                define_opaque,
                defaultness: _,
            }) => {
                self.with_generic_param_rib(
                    &generics.params,
                    RibKind::Item(
                        if self.r.tcx.features().generic_const_items() {
                            HasGenericParams::Yes(generics.span)
                        } else {
                            HasGenericParams::No
                        },
                        def_kind,
                    ),
                    item.id,
                    LifetimeBinderKind::ConstItem,
                    generics.span,
                    |this| {
                        this.visit_generics(generics);

                        this.with_lifetime_rib(
                            LifetimeRibKind::Elided(LifetimeRes::Static),
                            |this| {
                                if rhs_kind.is_type_const()
                                    && !this.r.tcx.features().generic_const_parameter_types()
                                {
                                    this.with_rib(TypeNS, RibKind::ConstParamTy, |this| {
                                        this.with_rib(ValueNS, RibKind::ConstParamTy, |this| {
                                            this.with_lifetime_rib(
                                                LifetimeRibKind::ConstParamTy,
                                                |this| this.visit_ty(ty),
                                            )
                                        })
                                    });
                                } else {
                                    this.visit_ty(ty);
                                }
                            },
                        );

                        this.resolve_const_item_rhs(
                            rhs_kind,
                            Some((*ident, ConstantItemKind::Const)),
                        );
                    },
                );
                self.resolve_define_opaques(define_opaque);
            }
            ItemKind::ConstBlock(ConstBlockItem { id: _, span: _, block }) => self
                .with_generic_param_rib(
                    &[],
                    RibKind::Item(HasGenericParams::No, def_kind),
                    item.id,
                    LifetimeBinderKind::ConstItem,
                    DUMMY_SP,
                    |this| {
                        this.with_lifetime_rib(
                            LifetimeRibKind::Elided(LifetimeRes::Infer),
                            |this| {
                                this.with_constant_rib(
                                    IsRepeatExpr::No,
                                    ConstantHasGenerics::Yes,
                                    Some((ConstBlockItem::IDENT, ConstantItemKind::Const)),
                                    |this| this.resolve_labeled_block(None, block.id, block),
                                )
                            },
                        );
                    },
                ),

            ItemKind::Use(use_tree) => {
                let maybe_exported = match use_tree.kind {
                    UseTreeKind::Simple(_) | UseTreeKind::Glob => MaybeExported::Ok(item.id),
                    UseTreeKind::Nested { .. } => MaybeExported::NestedUse(&item.vis),
                };
                self.resolve_doc_links(&item.attrs, maybe_exported);

                self.future_proof_import(use_tree);
            }

            ItemKind::MacroDef(_, macro_def) => {
                // Maintain macro_rules scopes in the same way as during early resolution
                // for diagnostics and doc links.
                if macro_def.macro_rules {
                    let def_id = self.r.local_def_id(item.id);
                    self.parent_scope.macro_rules = self.r.macro_rules_scopes[&def_id];
                }

                if let Some(EiiDecl { foreign_item: extern_item_path, impl_unsafe: _ }) =
                    &macro_def.eii_declaration
                {
                    self.smart_resolve_path(
                        item.id,
                        &None,
                        extern_item_path,
                        PathSource::Expr(None),
                    );
                }
            }

            ItemKind::ForeignMod(_) | ItemKind::GlobalAsm(_) => {
                visit::walk_item(self, item);
            }

            ItemKind::Delegation(delegation) => {
                let span = delegation.path.segments.last().expect("invariant: non-empty collection").ident.span;
                self.with_generic_param_rib(
                    &[],
                    RibKind::Item(HasGenericParams::Yes(span), def_kind),
                    item.id,
                    LifetimeBinderKind::Function,
                    span,
                    |this| this.resolve_delegation(delegation, item.id, false),
                );
            }

            ItemKind::ExternCrate(..) => {}

            ItemKind::MacCall(_) | ItemKind::DelegationMac(..) => {
                panic!("unexpanded macro in resolve!")
            }
        }
    }

    fn with_generic_param_rib<F>(
        &mut self,
        params: &[GenericParam],
        kind: RibKind<'ra>,
        binder: NodeId,
        generics_kind: LifetimeBinderKind,
        generics_span: Span,
        f: F,
    ) where
        F: FnOnce(&mut Self),
    {
        debug!("with_generic_param_rib");
        let lifetime_kind =
            LifetimeRibKind::Generics { binder, span: generics_span, kind: generics_kind };

        let mut function_type_rib = Rib::new(kind);
        let mut function_value_rib = Rib::new(kind);
        let mut function_lifetime_rib = LifetimeRib::new(lifetime_kind);

        // Only check for shadowed bindings if we're declaring new params.
        if !params.is_empty() {
            let mut seen_bindings = FxHashMap::default();
            // Store all seen lifetimes names from outer scopes.
            let mut seen_lifetimes = FxHashSet::default();

            // We also can't shadow bindings from associated parent items.
            for ns in [ValueNS, TypeNS] {
                for parent_rib in self.ribs[ns].iter().rev() {
                    // Break at module or block level, to account for nested items which are
                    // allowed to shadow generic param names.
                    if matches!(parent_rib.kind, RibKind::Module(..) | RibKind::Block(..)) {
                        break;
                    }

                    seen_bindings
                        .extend(parent_rib.bindings.keys().map(|ident| (*ident, ident.span)));
                }
            }

            // Forbid shadowing lifetime bindings
            for rib in self.lifetime_ribs.iter().rev() {
                seen_lifetimes.extend(rib.bindings.iter().map(|(ident, _)| *ident));
                if let LifetimeRibKind::Item = rib.kind {
                    break;
                }
            }

            for param in params {
                let ident = param.ident.normalize_to_macros_2_0();
                debug!("with_generic_param_rib: {}", param.id);

                if let GenericParamKind::Lifetime = param.kind
                    && let Some(&original) = seen_lifetimes.get(&ident)
                {
                    let guar = diagnostics::signal_lifetime_shadowing(
                        self.r.tcx.sess,
                        original,
                        param.ident,
                    );
                    // Record lifetime res, so lowering knows there is something fishy.
                    self.record_lifetime_param(param.id, LifetimeRes::Error(guar));
                    continue;
                }

                match seen_bindings.entry(ident) {
                    Entry::Occupied(entry) => {
                        let span = *entry.get();
                        let err = ResolutionError::NameAlreadyUsedInParameterList(ident, span);
                        let guar = self.r.report_error(param.ident.span, err);
                        let rib = match param.kind {
                            GenericParamKind::Lifetime => {
                                // Record lifetime res, so lowering knows there is something fishy.
                                self.record_lifetime_param(param.id, LifetimeRes::Error(guar));
                                continue;
                            }
                            GenericParamKind::Type { .. } => &mut function_type_rib,
                            GenericParamKind::Const { .. } => &mut function_value_rib,
                        };

                        // Taint the resolution in case of errors to prevent follow up errors in typeck
                        self.r.record_partial_res(param.id, PartialRes::new(Res::Err));
                        rib.bindings.insert(ident, Res::Err);
                        continue;
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(param.ident.span);
                    }
                }

                if param.ident.name == kw::UnderscoreLifetime {
                    // To avoid emitting two similar errors,
                    // we need to check if the span is a raw underscore lifetime, see issue #143152
                    let is_raw_underscore_lifetime = self
                        .r
                        .tcx
                        .sess
                        .psess
                        .raw_identifier_spans
                        .iter()
                        .any(|span| span == param.span());

                    let guar = self
                        .r
                        .dcx()
                        .create_err(errors::UnderscoreLifetimeIsReserved { span: param.ident.span })
                        .emit_unless_delay(is_raw_underscore_lifetime);
                    // Record lifetime res, so lowering knows there is something fishy.
                    self.record_lifetime_param(param.id, LifetimeRes::Error(guar));
                    continue;
                }

                if param.ident.name == kw::StaticLifetime {
                    let guar = self.r.dcx().emit_err(errors::StaticLifetimeIsReserved {
                        span: param.ident.span,
                        lifetime: param.ident,
                    });
                    // Record lifetime res, so lowering knows there is something fishy.
                    self.record_lifetime_param(param.id, LifetimeRes::Error(guar));
                    continue;
                }

                let def_id = self.r.local_def_id(param.id);

                // Plain insert (no renaming).
                let (rib, def_kind) = match param.kind {
                    GenericParamKind::Type { .. } => (&mut function_type_rib, DefKind::TyParam),
                    GenericParamKind::Const { .. } => {
                        (&mut function_value_rib, DefKind::ConstParam)
                    }
                    GenericParamKind::Lifetime => {
                        let res = LifetimeRes::Param { param: def_id, binder };
                        self.record_lifetime_param(param.id, res);
                        function_lifetime_rib.bindings.insert(ident, (param.id, res));
                        continue;
                    }
                };

                let res = match kind {
                    RibKind::Item(..) | RibKind::AssocItem => {
                        Res::Def(def_kind, def_id.to_def_id())
                    }
                    RibKind::Normal => {
                        // NOTE(non_lifetime_binders): Stop special-casing
                        // const params to error out here.
                        if self.r.tcx.features().non_lifetime_binders()
                            && matches!(param.kind, GenericParamKind::Type { .. })
                        {
                            Res::Def(def_kind, def_id.to_def_id())
                        } else {
                            Res::Err
                        }
                    }
                    // tRust: invariant — all valid rib kinds for generic params handled above
                    _ => span_bug!(param.ident.span, "Unexpected rib kind {:?}", kind),
                };
                self.r.record_partial_res(param.id, PartialRes::new(res));
                rib.bindings.insert(ident, res);
            }
        }

        self.lifetime_ribs.push(function_lifetime_rib);
        self.ribs[ValueNS].push(function_value_rib);
        self.ribs[TypeNS].push(function_type_rib);

        f(self);

        self.ribs[TypeNS].pop();
        self.ribs[ValueNS].pop();
        let function_lifetime_rib = self.lifetime_ribs.pop().expect("invariant: non-empty collection");

        // Do not account for the parameters we just bound for function lifetime elision.
        if let Some(ref mut candidates) = self.lifetime_elision_candidates {
            for (_, res) in function_lifetime_rib.bindings.values() {
                candidates.retain(|(r, _)| r != res);
            }
        }

        if let LifetimeBinderKind::FnPtrType
        | LifetimeBinderKind::WhereBound
        | LifetimeBinderKind::Function
        | LifetimeBinderKind::ImplBlock = generics_kind
        {
            self.maybe_report_lifetime_uses(generics_span, params)
        }
    }

    fn with_label_rib(&mut self, kind: RibKind<'ra>, f: impl FnOnce(&mut Self)) {
        self.label_ribs.push(Rib::new(kind));
        f(self);
        self.label_ribs.pop();
    }

    fn with_static_rib(&mut self, def_kind: DefKind, f: impl FnOnce(&mut Self)) {
        let kind = RibKind::Item(HasGenericParams::No, def_kind);
        self.with_rib(ValueNS, kind, |this| this.with_rib(TypeNS, kind, f))
    }

    // tRust: known issue — (min_const_generics, generic_const_exprs) We
    // want to keep allowing `[0; size_of::<*mut T>()]`
    // with a future compat lint for now. We do this by adding an
    // additional special case for repeat expressions.
    //
    // Note that we intentionally still forbid `[0; N + 1]` during
    // name resolution so that we don't extend the future
    // compat lint to new cases.
    #[instrument(level = "debug", skip(self, f))]
    fn with_constant_rib(
        &mut self,
        is_repeat: IsRepeatExpr,
        may_use_generics: ConstantHasGenerics,
        item: Option<(Ident, ConstantItemKind)>,
        f: impl FnOnce(&mut Self),
    ) {
        let f = |this: &mut Self| {
            this.with_rib(ValueNS, RibKind::ConstantItem(may_use_generics, item), |this| {
                this.with_rib(
                    TypeNS,
                    RibKind::ConstantItem(
                        may_use_generics.force_yes_if(is_repeat == IsRepeatExpr::Yes),
                        item,
                    ),
                    |this| {
                        this.with_label_rib(RibKind::ConstantItem(may_use_generics, item), f);
                    },
                )
            })
        };

        if let ConstantHasGenerics::No(cause) = may_use_generics {
            self.with_lifetime_rib(LifetimeRibKind::ConcreteAnonConst(cause), f)
        } else {
            f(self)
        }
    }

    fn with_current_self_type<T>(&mut self, self_type: &Ty, f: impl FnOnce(&mut Self) -> T) -> T {
        // Handle nested impls (inside fn bodies)
        let previous_value =
            replace(&mut self.diag_metadata.current_self_type, Some(self_type.clone()));
        let result = f(self);
        self.diag_metadata.current_self_type = previous_value;
        result
    }

    fn with_current_self_item<T>(&mut self, self_item: &Item, f: impl FnOnce(&mut Self) -> T) -> T {
        let previous_value = replace(&mut self.diag_metadata.current_self_item, Some(self_item.id));
        let result = f(self);
        self.diag_metadata.current_self_item = previous_value;
        result
    }

    /// When evaluating a `trait` use its associated types' idents for suggestions in E0425.
    fn resolve_trait_items(&mut self, trait_items: &'ast [Box<AssocItem>]) {
        let trait_assoc_items =
            replace(&mut self.diag_metadata.current_trait_assoc_items, Some(trait_items));

        let walk_assoc_item =
            |this: &mut Self, generics: &Generics, kind, item: &'ast AssocItem| {
                this.with_generic_param_rib(
                    &generics.params,
                    RibKind::AssocItem,
                    item.id,
                    kind,
                    generics.span,
                    |this| visit::walk_assoc_item(this, item, AssocCtxt::Trait),
                );
            };

        for item in trait_items {
            self.resolve_doc_links(&item.attrs, MaybeExported::Ok(item.id));
            match &item.kind {
                AssocItemKind::Const(box ast::ConstItem {
                    generics,
                    ty,
                    rhs_kind,
                    define_opaque,
                    ..
                }) => {
                    self.with_generic_param_rib(
                        &generics.params,
                        RibKind::AssocItem,
                        item.id,
                        LifetimeBinderKind::ConstItem,
                        generics.span,
                        |this| {
                            this.with_lifetime_rib(
                                LifetimeRibKind::StaticIfNoLifetimeInScope {
                                    lint_id: item.id,
                                    emit_lint: false,
                                },
                                |this| {
                                    this.visit_generics(generics);
                                    if rhs_kind.is_type_const()
                                        && !this.r.tcx.features().generic_const_parameter_types()
                                    {
                                        this.with_rib(TypeNS, RibKind::ConstParamTy, |this| {
                                            this.with_rib(ValueNS, RibKind::ConstParamTy, |this| {
                                                this.with_lifetime_rib(
                                                    LifetimeRibKind::ConstParamTy,
                                                    |this| this.visit_ty(ty),
                                                )
                                            })
                                        });
                                    } else {
                                        this.visit_ty(ty);
                                    }

                                    // Only impose the restrictions of `ConstRibKind` for an
                                    // actual constant expression in a provided default.
                                    //
                                    // We allow arbitrary const expressions inside of associated consts,
                                    // even if they are potentially not const evaluatable.
                                    //
                                    // Type parameters can already be used and as associated consts are
                                    // not used as part of the type system, this is far less surprising.
                                    this.resolve_const_item_rhs(rhs_kind, None);
                                },
                            )
                        },
                    );

                    self.resolve_define_opaques(define_opaque);
                }
                AssocItemKind::Fn(box Fn { generics, define_opaque, .. }) => {
                    walk_assoc_item(self, generics, LifetimeBinderKind::Function, item);

                    self.resolve_define_opaques(define_opaque);
                }
                AssocItemKind::Delegation(delegation) => {
                    self.with_generic_param_rib(
                        &[],
                        RibKind::AssocItem,
                        item.id,
                        LifetimeBinderKind::Function,
                        delegation.path.segments.last().expect("invariant: non-empty collection").ident.span,
                        |this| this.resolve_delegation(delegation, item.id, false),
                    );
                }
                AssocItemKind::Type(box TyAlias { generics, .. }) => self
                    .with_lifetime_rib(LifetimeRibKind::AnonymousReportError, |this| {
                        walk_assoc_item(this, generics, LifetimeBinderKind::Item, item)
                    }),
                AssocItemKind::MacCall(_) | AssocItemKind::DelegationMac(..) => {
                    panic!("unexpanded macro in resolve!")
                }
            };
        }

        self.diag_metadata.current_trait_assoc_items = trait_assoc_items;
    }

    /// This is called to resolve a trait reference from an `impl` (i.e., `impl Trait for Foo`).
    fn with_optional_trait_ref<T>(
        &mut self,
        opt_trait_ref: Option<&TraitRef>,
        self_type: &'ast Ty,
        f: impl FnOnce(&mut Self, Option<DefId>) -> T,
    ) -> T {
        let mut new_val = None;
        let mut new_id = None;
        if let Some(trait_ref) = opt_trait_ref {
            let path: Vec<_> = Segment::from_path(&trait_ref.path);
            self.diag_metadata.currently_processing_impl_trait =
                Some((trait_ref.clone(), self_type.clone()));
            let res = self.smart_resolve_path_fragment(
                &None,
                &path,
                PathSource::Trait(AliasPossibility::No),
                Finalize::new(trait_ref.ref_id, trait_ref.path.span),
                RecordPartialRes::Yes,
                None,
            );
            self.diag_metadata.currently_processing_impl_trait = None;
            if let Some(def_id) = res.expect_full_res().opt_def_id() {
                new_id = Some(def_id);
                new_val = Some((self.r.expect_module(def_id), trait_ref.clone()));
            }
        }
        let original_trait_ref = replace(&mut self.current_trait_ref, new_val);
        let result = f(self, new_id);
        self.current_trait_ref = original_trait_ref;
        result
    }

    fn with_self_rib_ns(&mut self, ns: Namespace, self_res: Res, f: impl FnOnce(&mut Self)) {
        let mut self_type_rib = Rib::new(RibKind::Normal);

        // Plain insert (no renaming, since types are not currently hygienic)
        self_type_rib.bindings.insert(Ident::with_dummy_span(kw::SelfUpper), self_res);
        self.ribs[ns].push(self_type_rib);
        f(self);
        self.ribs[ns].pop();
    }

    fn with_self_rib(&mut self, self_res: Res, f: impl FnOnce(&mut Self)) {
        self.with_self_rib_ns(TypeNS, self_res, f)
    }

    fn resolve_implementation(
        &mut self,
        attrs: &[ast::Attribute],
        generics: &'ast Generics,
        of_trait: Option<&'ast ast::TraitImplHeader>,
        self_type: &'ast Ty,
        item_id: NodeId,
        impl_items: &'ast [Box<AssocItem>],
    ) {
        debug!("resolve_implementation");
        // If applicable, create a rib for the type parameters.
        self.with_generic_param_rib(
            &generics.params,
            RibKind::Item(HasGenericParams::Yes(generics.span), self.r.local_def_kind(item_id)),
            item_id,
            LifetimeBinderKind::ImplBlock,
            generics.span,
            |this| {
                // Dummy self type for better errors if `Self` is used in the trait path.
                this.with_self_rib(Res::SelfTyParam { trait_: LOCAL_CRATE.as_def_id() }, |this| {
                    this.with_lifetime_rib(
                        LifetimeRibKind::AnonymousCreateParameter {
                            binder: item_id,
                            report_in_path: true
                        },
                        |this| {
                            // Resolve the trait reference, if necessary.
                            this.with_optional_trait_ref(
                                of_trait.map(|t| &t.trait_ref),
                                self_type,
                                |this, trait_id| {
                                    this.resolve_doc_links(attrs, MaybeExported::Impl(trait_id));

                                    let item_def_id = this.r.local_def_id(item_id);

                                    // Register the trait definitions from here.
                                    if let Some(trait_id) = trait_id {
                                        this.r
                                            .trait_impls
                                            .entry(trait_id)
                                            .or_default()
                                            .push(item_def_id);
                                    }

                                    let item_def_id = item_def_id.to_def_id();
                                    let res = Res::SelfTyAlias {
                                        alias_to: item_def_id,
                                        is_trait_impl: trait_id.is_some(),
                                    };
                                    this.with_self_rib(res, |this| {
                                        if let Some(of_trait) = of_trait {
                                            // Resolve type arguments in the trait path.
                                            visit::walk_trait_ref(this, &of_trait.trait_ref);
                                        }
                                        // Resolve the self type.
                                        this.visit_ty(self_type);
                                        // Resolve the generic parameters.
                                        this.visit_generics(generics);

                                        // Resolve the items within the impl.
                                        this.with_current_self_type(self_type, |this| {
                                            this.with_self_rib_ns(ValueNS, Res::SelfCtor(item_def_id), |this| {
                                                debug!("resolve_implementation with_self_rib_ns(ValueNS, ...)");
                                                let mut seen_trait_items = Default::default();
                                                for item in impl_items {
                                                    this.resolve_impl_item(&**item, &mut seen_trait_items, trait_id, of_trait.is_some());
                                                }
                                            });
                                        });
                                    });
                                },
                            )
                        },
                    );
                });
            },
        );
    }

    fn resolve_impl_item(
        &mut self,
        item: &'ast AssocItem,
        seen_trait_items: &mut FxHashMap<DefId, Span>,
        trait_id: Option<DefId>,
        is_in_trait_impl: bool,
    ) {
        use crate::ResolutionError::*;
        self.resolve_doc_links(&item.attrs, MaybeExported::ImplItem(trait_id.ok_or(&item.vis)));
        let prev = self.diag_metadata.current_impl_item.take();
        self.diag_metadata.current_impl_item = Some(&item);
        match &item.kind {
            AssocItemKind::Const(box ast::ConstItem {
                ident,
                generics,
                ty,
                rhs_kind,
                define_opaque,
                ..
            }) => {
                debug!("resolve_implementation AssocItemKind::Const");
                self.with_generic_param_rib(
                    &generics.params,
                    RibKind::AssocItem,
                    item.id,
                    LifetimeBinderKind::ConstItem,
                    generics.span,
                    |this| {
                        this.with_lifetime_rib(
                            // Until these are a hard error, we need to create them within the
                            // correct binder, Otherwise the lifetimes of this assoc const think
                            // they are lifetimes of the trait.
                            LifetimeRibKind::AnonymousCreateParameter {
                                binder: item.id,
                                report_in_path: true,
                            },
                            |this| {
                                this.with_lifetime_rib(
                                    LifetimeRibKind::StaticIfNoLifetimeInScope {
                                        lint_id: item.id,
                                        // In impls, it's not a hard error yet due to backcompat.
                                        emit_lint: true,
                                    },
                                    |this| {
                                        // If this is a trait impl, ensure the const
                                        // exists in trait
                                        this.check_trait_item(
                                            item.id,
                                            *ident,
                                            &item.kind,
                                            ValueNS,
                                            item.span,
                                            seen_trait_items,
                                            |i, s, c| ConstNotMemberOfTrait(i, s, c),
                                        );

                                        this.visit_generics(generics);
                                        if rhs_kind.is_type_const()
                                            && !this
                                                .r
                                                .tcx
                                                .features()
                                                .generic_const_parameter_types()
                                        {
                                            this.with_rib(TypeNS, RibKind::ConstParamTy, |this| {
                                                this.with_rib(
                                                    ValueNS,
                                                    RibKind::ConstParamTy,
                                                    |this| {
                                                        this.with_lifetime_rib(
                                                            LifetimeRibKind::ConstParamTy,
                                                            |this| this.visit_ty(ty),
                                                        )
                                                    },
                                                )
                                            });
                                        } else {
                                            this.visit_ty(ty);
                                        }
                                        // We allow arbitrary const expressions inside of associated consts,
                                        // even if they are potentially not const evaluatable.
                                        //
                                        // Type parameters can already be used and as associated consts are
                                        // not used as part of the type system, this is far less surprising.
                                        this.resolve_const_item_rhs(rhs_kind, None);
                                    },
                                )
                            },
                        );
                    },
                );
                self.resolve_define_opaques(define_opaque);
            }
            AssocItemKind::Fn(box Fn { ident, generics, define_opaque, .. }) => {
                debug!("resolve_implementation AssocItemKind::Fn");
                // We also need a new scope for the impl item type parameters.
                self.with_generic_param_rib(
                    &generics.params,
                    RibKind::AssocItem,
                    item.id,
                    LifetimeBinderKind::Function,
                    generics.span,
                    |this| {
                        // If this is a trait impl, ensure the method
                        // exists in trait
                        this.check_trait_item(
                            item.id,
                            *ident,
                            &item.kind,
                            ValueNS,
                            item.span,
                            seen_trait_items,
                            |i, s, c| MethodNotMemberOfTrait(i, s, c),
                        );

                        visit::walk_assoc_item(this, item, AssocCtxt::Impl { of_trait: true })
                    },
                );

                self.resolve_define_opaques(define_opaque);
            }
            AssocItemKind::Type(box TyAlias { ident, generics, .. }) => {
                self.diag_metadata.in_non_gat_assoc_type = Some(generics.params.is_empty());
                debug!("resolve_implementation AssocItemKind::Type");
                // We also need a new scope for the impl item type parameters.
                self.with_generic_param_rib(
                    &generics.params,
                    RibKind::AssocItem,
                    item.id,
                    LifetimeBinderKind::ImplAssocType,
                    generics.span,
                    |this| {
                        this.with_lifetime_rib(LifetimeRibKind::AnonymousReportError, |this| {
                            // If this is a trait impl, ensure the type
                            // exists in trait
                            this.check_trait_item(
                                item.id,
                                *ident,
                                &item.kind,
                                TypeNS,
                                item.span,
                                seen_trait_items,
                                |i, s, c| TypeNotMemberOfTrait(i, s, c),
                            );

                            visit::walk_assoc_item(this, item, AssocCtxt::Impl { of_trait: true })
                        });
                    },
                );
                self.diag_metadata.in_non_gat_assoc_type = None;
            }
            AssocItemKind::Delegation(box delegation) => {
                debug!("resolve_implementation AssocItemKind::Delegation");
                self.with_generic_param_rib(
                    &[],
                    RibKind::AssocItem,
                    item.id,
                    LifetimeBinderKind::Function,
                    delegation.path.segments.last().expect("invariant: non-empty collection").ident.span,
                    |this| {
                        this.check_trait_item(
                            item.id,
                            delegation.ident,
                            &item.kind,
                            ValueNS,
                            item.span,
                            seen_trait_items,
                            |i, s, c| MethodNotMemberOfTrait(i, s, c),
                        );

                        // Here we don't use `trait_id`, as we can process unresolved trait, however
                        // in this case we are still in a trait impl, https://github.com/rust-lang/rust/issues/150152
                        this.resolve_delegation(delegation, item.id, is_in_trait_impl);
                    },
                );
            }
            AssocItemKind::MacCall(_) | AssocItemKind::DelegationMac(..) => {
                panic!("unexpanded macro in resolve!")
            }
        }
        self.diag_metadata.current_impl_item = prev;
    }

    fn check_trait_item<F>(
        &mut self,
        id: NodeId,
        mut ident: Ident,
        kind: &AssocItemKind,
        ns: Namespace,
        span: Span,
        seen_trait_items: &mut FxHashMap<DefId, Span>,
        err: F,
    ) where
        F: FnOnce(Ident, String, Option<Symbol>) -> ResolutionError<'ra>,
    {
        // If there is a TraitRef in scope for an impl, then the method must be in the trait.
        let Some((module, _)) = self.current_trait_ref else {
            return;
        };
        ident.span.normalize_to_macros_2_0_and_adjust(module.expansion);
        let key = BindingKey::new(IdentKey::new(ident), ns);
        let mut decl = self.r.resolution(module, key).and_then(|r| r.best_decl());
        debug!(?decl);
        if decl.is_none() {
            // We could not find the trait item in the correct namespace.
            // Check the other namespace to report an error.
            let ns = match ns {
                ValueNS => TypeNS,
                TypeNS => ValueNS,
                _ => ns,
            };
            let key = BindingKey::new(IdentKey::new(ident), ns);
            decl = self.r.resolution(module, key).and_then(|r| r.best_decl());
            debug!(?decl);
        }

        let feed_visibility = |this: &mut Self, def_id| {
            let vis = this.r.tcx.visibility(def_id);
            let vis = if vis.is_visible_locally() {
                vis.expect_local()
            } else {
                this.r.dcx().span_delayed_bug(
                    span,
                    "error should be emitted when an unexpected trait item is used",
                );
                Visibility::Public
            };
            this.r.feed_visibility(this.r.feed(id), vis);
        };

        let Some(decl) = decl else {
            // We could not find the method: report an error.
            let candidate = self.find_similarly_named_assoc_item(ident.name, kind);
            let path = &self.current_trait_ref.as_ref().expect("invariant: value is present").1.path;
            let path_names = path_names_to_string(path);
            self.report_error(span, err(ident, path_names, candidate));
            feed_visibility(self, module.def_id());
            return;
        };

        let res = decl.res();
        // tRust: invariant — trait item declarations always resolve to Def, not local or other Res variants
        let Res::Def(def_kind, id_in_trait) = res else { bug!() };
        feed_visibility(self, id_in_trait);

        match seen_trait_items.entry(id_in_trait) {
            Entry::Occupied(entry) => {
                self.report_error(
                    span,
                    ResolutionError::TraitImplDuplicate {
                        name: ident,
                        old_span: *entry.get(),
                        trait_item_span: decl.span,
                    },
                );
                return;
            }
            Entry::Vacant(entry) => {
                entry.insert(span);
            }
        };

        match (def_kind, kind) {
            (DefKind::AssocTy, AssocItemKind::Type(..))
            | (DefKind::AssocFn, AssocItemKind::Fn(..))
            | (DefKind::AssocConst { .. }, AssocItemKind::Const(..))
            | (DefKind::AssocFn, AssocItemKind::Delegation(..)) => {
                self.r.record_partial_res(id, PartialRes::new(res));
                return;
            }
            _ => {}
        }

        // The method kind does not correspond to what appeared in the trait, report.
        let path = &self.current_trait_ref.as_ref().expect("invariant: value is present").1.path;
        let (code, kind) = match kind {
            AssocItemKind::Const(..) => (E0323, "const"),
            AssocItemKind::Fn(..) => (E0324, "method"),
            AssocItemKind::Type(..) => (E0325, "type"),
            AssocItemKind::Delegation(..) => (E0324, "method"),
            AssocItemKind::MacCall(..) | AssocItemKind::DelegationMac(..) => {
                // tRust: invariant — macro calls in trait impls must be expanded before name resolution
                span_bug!(span, "unexpanded macro")
            }
        };
        let trait_path = path_names_to_string(path);
        self.report_error(
            span,
            ResolutionError::TraitImplMismatch {
                name: ident,
                kind,
                code,
                trait_path,
                trait_item_span: decl.span,
            },
        );
    }

    fn resolve_static_body(&mut self, expr: &'ast Expr, item: Option<(Ident, ConstantItemKind)>) {
        self.with_lifetime_rib(LifetimeRibKind::Elided(LifetimeRes::Infer), |this| {
            this.with_constant_rib(IsRepeatExpr::No, ConstantHasGenerics::Yes, item, |this| {
                this.visit_expr(expr)
            });
        })
    }

    fn resolve_const_item_rhs(
        &mut self,
        rhs_kind: &'ast ConstItemRhsKind,
        item: Option<(Ident, ConstantItemKind)>,
    ) {
        self.with_lifetime_rib(LifetimeRibKind::Elided(LifetimeRes::Infer), |this| match rhs_kind {
            ConstItemRhsKind::TypeConst { rhs: Some(anon_const) } => {
                this.resolve_anon_const(anon_const, AnonConstKind::ConstArg(IsRepeatExpr::No));
            }
            ConstItemRhsKind::Body { rhs: Some(expr) } => {
                this.with_constant_rib(IsRepeatExpr::No, ConstantHasGenerics::Yes, item, |this| {
                    this.visit_expr(expr)
                });
            }
            _ => (),
        })
    }

    fn resolve_delegation(
        &mut self,
        delegation: &'ast Delegation,
        item_id: NodeId,
        is_in_trait_impl: bool,
    ) {
        self.smart_resolve_path(
            delegation.id,
            &delegation.qself,
            &delegation.path,
            PathSource::Delegation,
        );

        if let Some(qself) = &delegation.qself {
            self.visit_ty(&qself.ty);
        }

        self.visit_path(&delegation.path);

        self.r.delegation_infos.insert(
            self.r.local_def_id(item_id),
            DelegationInfo {
                resolution_node: if is_in_trait_impl { item_id } else { delegation.id },
            },
        );

        let Some(body) = &delegation.body else { return };
        self.with_rib(ValueNS, RibKind::FnOrCoroutine, |this| {
            let span = delegation.path.segments.last().expect("invariant: non-empty collection").ident.span;
            let ident = Ident::new(kw::SelfLower, span.normalize_to_macro_rules());
            let res = Res::Local(delegation.id);
            this.innermost_rib_bindings(ValueNS).insert(ident, res);

            //As we lower target_expr_template body to a body of a function we need a label rib (#148889)
            this.with_label_rib(RibKind::FnOrCoroutine, |this| {
                this.visit_block(body);
            });
        });
    }


}
