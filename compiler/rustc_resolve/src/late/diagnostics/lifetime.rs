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
    pub(crate) fn detect_and_suggest_const_parameter_error(
        &mut self,
        path: &[Segment],
        source: PathSource<'_, 'ast, 'ra>,
    ) -> Option<Diag<'tcx>> {
        let Some(item) = self.diag_metadata.current_item else { return None };
        let ItemKind::Impl(impl_) = &item.kind else { return None };
        let self_ty = &impl_.self_ty;

        // Represents parameter to the struct whether `A`, `X` or `P`
        let [current_parameter] = path else {
            return None;
        };

        let target_ident = current_parameter.ident;

        // Find the parent segment i.e `C` in `C<A, X, C>`
        let visitor = ParentPathVisitor::new(self_ty, target_ident);

        let Some(parent_segment) = visitor.parent else {
            return None;
        };

        let Some(args) = parent_segment.args.as_ref() else {
            return None;
        };

        let GenericArgs::AngleBracketed(angle) = args.as_ref() else {
            return None;
        };

        // Build map: NodeId of each usage in C<A, X, C> -> its position
        // e.g NodeId(A) -> 0, NodeId(X) -> 1, NodeId(C) -> 2
        let usage_to_pos: FxHashMap<NodeId, usize> = angle
            .args
            .iter()
            .enumerate()
            .filter_map(|(pos, arg)| {
                if let AngleBracketedArg::Arg(GenericArg::Type(ty)) = arg
                    && let TyKind::Path(_, path) = &ty.kind
                    && let [segment] = path.segments.as_slice()
                {
                    Some((segment.id, pos))
                } else {
                    None
                }
            })
            .collect();

        // Get the position of the missing param in C<A, X, C>
        // e.g for missing `B` in `C<A, B, C>` this gives idx=1
        let Some(idx) = current_parameter.id.and_then(|id| usage_to_pos.get(&id).copied()) else {
            return None;
        };

        // Now resolve the parent struct `C` to get its definition
        let ns = source.namespace();
        let segment = Segment::from(parent_segment);
        let segments = [segment];
        let finalize = Finalize::new(parent_segment.id, parent_segment.ident.span);

        if let Ok(Some(resolve)) = self.resolve_qpath_anywhere(
            &None,
            &segments,
            ns,
            source.defer_to_typeck(),
            finalize,
            source,
        ) && let Some(resolve) = resolve.full_res()
            && let Res::Def(_, def_id) = resolve
            && def_id.is_local()
            && let Some(local_def_id) = def_id.as_local()
            && let Some(struct_generics) = self.r.struct_generics.get(&local_def_id)
            && let Some(target_param) = &struct_generics.params.get(idx)
            && let GenericParamKind::Const { ty, .. } = &target_param.kind
            && let TyKind::Path(_, path) = &ty.kind
        {
            let full_type = path
                .segments
                .iter()
                .map(|seg| seg.ident.to_string())
                .collect::<Vec<_>>()
                .join("::");

            // Find the first impl param whose position in C<A, X, C>
            // is strictly greater than our missing param's index
            // e.g missing B(idx=1), impl has A(pos=0) and C(pos=2)
            // C has pos=2 > 1 so insert before C
            let next_impl_param = impl_.generics.params.iter().find(|impl_param| {
                angle
                    .args
                    .iter()
                    .find_map(|arg| {
                        if let AngleBracketedArg::Arg(GenericArg::Type(ty)) = arg
                            && let TyKind::Path(_, path) = &ty.kind
                            && let [segment] = path.segments.as_slice()
                            && segment.ident == impl_param.ident
                        {
                            usage_to_pos.get(&segment.id).copied()
                        } else {
                            None
                        }
                    })
                    .map_or(false, |pos| pos > idx)
            });

            let (insert_span, snippet) = match next_impl_param {
                Some(next_param) => {
                    // Insert in the middle before next_param
                    // e.g impl<A, C> -> impl<A, const B: u8, C>
                    (
                        next_param.span().shrink_to_lo(),
                        format!("const {}: {}, ", target_ident, full_type),
                    )
                }
                None => match impl_.generics.params.last() {
                    Some(last) => {
                        // Append after last existing param
                        // e.g impl<A, B> -> impl<A, B, const C: u8>
                        (
                            last.span().shrink_to_hi(),
                            format!(", const {}: {}", target_ident, full_type),
                        )
                    }
                    None => {
                        // No generics at all on impl
                        // e.g impl Foo for C<A> -> impl<const A: u8> Foo for C<A>
                        (
                            impl_.generics.span.shrink_to_hi(),
                            format!("<const {}: {}>", target_ident, full_type),
                        )
                    }
                },
            };

            let mut err = self.r.dcx().struct_span_err(
                target_ident.span,
                format!("cannot find const `{}` in this scope", target_ident),
            );

            err.code(E0425);

            err.span_label(target_ident.span, "not found in this scope");

            err.span_label(
                target_param.span(),
                format!("corresponding const parameter on the type defined here",),
            );

            err.subdiagnostic(errors::UnexpectedMissingConstParameter {
                span: insert_span,
                snippet,
                item_name: format!("{}", target_ident),
                item_location: String::from("impl"),
            });

            return Some(err);
        }

        None
    }

    pub(crate) fn suggest_adding_generic_parameter(
        &mut self,
        path: &[Segment],
        source: PathSource<'_, 'ast, 'ra>,
    ) -> (Option<(Span, &'static str, String, Applicability)>, Option<Diag<'tcx>>) {
        let (ident, span) = match path {
            [segment]
                if !segment.has_generic_args
                    && segment.ident.name != kw::SelfUpper
                    && segment.ident.name != kw::Dyn =>
            {
                (segment.ident.to_string(), segment.ident.span)
            }
            _ => return (None, None),
        };
        let mut iter = ident.chars().map(|c| c.is_uppercase());
        let single_uppercase_char =
            matches!(iter.next(), Some(true)) && matches!(iter.next(), None);
        if !self.diag_metadata.currently_processing_generic_args && !single_uppercase_char {
            return (None, None);
        }
        match (self.diag_metadata.current_item, single_uppercase_char, self.diag_metadata.currently_processing_generic_args) {
            (Some(Item { kind: ItemKind::Fn(fn_), .. }), _, _) if fn_.ident.name == sym::main => {
                // Ignore `fn main()` as we don't want to suggest `fn main<T>()`
            }
            (
                Some(Item {
                    kind:
                        kind @ ItemKind::Fn(..)
                        | kind @ ItemKind::Enum(..)
                        | kind @ ItemKind::Struct(..)
                        | kind @ ItemKind::Union(..),
                    ..
                }),
                true, _
            )
            // Without the 2nd `true`, we'd suggest `impl <T>` for `impl T` when a type `T` isn't found
            | (Some(Item { kind: kind @ ItemKind::Impl(..), .. }), true, true)
            | (Some(Item { kind, .. }), false, _) => {
                if let Some(generics) = kind.generics() {
                    if span.overlaps(generics.span) {
                        // Avoid the following:
                        // error[E0405]: cannot find trait `A` in this scope
                        //  --> $DIR/typo-suggestion-named-underscore.rs:CC:LL
                        //   |
                        // L | fn foo<T: A>(x: T) {} // Shouldn't suggest underscore
                        //   |           ^- help: you might be missing a type parameter: `, A`
                        //   |           |
                        //   |           not found in this scope
                        return (None, None);
                    }

                    let (msg, sugg) = match source {
                        PathSource::Type | PathSource::PreciseCapturingArg(TypeNS) => {
                            if let Some(err) = self.detect_and_suggest_const_parameter_error(path, source) {
                                return (None, Some(err));
                            }
                            ("you might be missing a type parameter", ident)
                        }
                        PathSource::Expr(_) | PathSource::PreciseCapturingArg(ValueNS) => (
                            "you might be missing a const parameter",
                            format!("const {ident}: /* Type */"),
                        ),
                        _ => return (None, None),
                    };
                    let (span, sugg) = if let [.., param] = &generics.params[..] {
                        let span = if let [.., bound] = &param.bounds[..] {
                            bound.span()
                        } else if let GenericParam {
                            kind: GenericParamKind::Const { ty, span: _, default  }, ..
                        } = param {
                            default.as_ref().map(|def| def.value.span).unwrap_or(ty.span)
                        } else {
                            param.ident.span
                        };
                        (span, format!(", {sugg}"))
                    } else {
                        (generics.span, format!("<{sugg}>"))
                    };
                    // Do not suggest if this is coming from macro expansion.
                    if span.can_be_used_for_suggestions() {
                        return (Some((
                            span.shrink_to_hi(),
                            msg,
                            sugg,
                            Applicability::MaybeIncorrect,
                        )), None);
                    }
                }
            }
            _ => {}
        }
        (None, None)
    }

    /// Given the target `label`, search the `rib_index`th label rib for similarly named labels,
    /// optionally returning the closest match and whether it is reachable.
    pub(crate) fn suggestion_for_label_in_rib(
        &self,
        rib_index: usize,
        label: Ident,
    ) -> Option<LabelSuggestion> {
        // Are ribs from this `rib_index` within scope?
        let within_scope = self.is_label_valid_from_rib(rib_index);

        let rib = &self.label_ribs[rib_index];
        let names = rib
            .bindings
            .iter()
            .filter(|(id, _)| id.span.eq_ctxt(label.span))
            .map(|(id, _)| id.name)
            .collect::<Vec<Symbol>>();

        find_best_match_for_name(&names, label.name, None).map(|symbol| {
            // Upon finding a similar name, get the ident that it was from - the span
            // contained within helps make a useful diagnostic. In addition, determine
            // whether this candidate is within scope.
            let (ident, _) = rib.bindings.iter().find(|(ident, _)| ident.name == symbol).expect("invariant: element exists in collection");
            (*ident, within_scope)
        })
    }

    pub(crate) fn maybe_report_lifetime_uses(
        &mut self,
        generics_span: Span,
        params: &[ast::GenericParam],
    ) {
        for (param_index, param) in params.iter().enumerate() {
            let GenericParamKind::Lifetime = param.kind else { continue };

            let def_id = self.r.local_def_id(param.id);

            let use_set = self.lifetime_uses.remove(&def_id);
            debug!(
                "Use set for {:?}({:?} at {:?}) is {:?}",
                def_id, param.ident, param.ident.span, use_set
            );

            let deletion_span = || {
                if params.len() == 1 {
                    // if sole lifetime, remove the entire `<>` brackets
                    Some(generics_span)
                } else if param_index == 0 {
                    // if removing within `<>` brackets, we also want to
                    // delete a leading or trailing comma as appropriate
                    match (
                        param.span().find_ancestor_inside(generics_span),
                        params[param_index + 1].span().find_ancestor_inside(generics_span),
                    ) {
                        (Some(param_span), Some(next_param_span)) => {
                            Some(param_span.to(next_param_span.shrink_to_lo()))
                        }
                        _ => None,
                    }
                } else {
                    // if removing within `<>` brackets, we also want to
                    // delete a leading or trailing comma as appropriate
                    match (
                        param.span().find_ancestor_inside(generics_span),
                        params[param_index - 1].span().find_ancestor_inside(generics_span),
                    ) {
                        (Some(param_span), Some(prev_param_span)) => {
                            Some(prev_param_span.shrink_to_hi().to(param_span))
                        }
                        _ => None,
                    }
                }
            };
            match use_set {
                Some(LifetimeUseSet::Many) => {}
                Some(LifetimeUseSet::One { use_span, use_ctxt }) => {
                    debug!(?param.ident, ?param.ident.span, ?use_span);

                    let elidable = matches!(use_ctxt, LifetimeCtxt::Ref);
                    let deletion_span =
                        if param.bounds.is_empty() { deletion_span() } else { None };

                    self.r.lint_buffer.buffer_lint(
                        lint::builtin::SINGLE_USE_LIFETIMES,
                        param.id,
                        param.ident.span,
                        lint::BuiltinLintDiag::SingleUseLifetime {
                            param_span: param.ident.span,
                            use_span,
                            elidable,
                            deletion_span,
                            ident: param.ident,
                        },
                    );
                }
                None => {
                    debug!(?param.ident, ?param.ident.span);
                    let deletion_span = deletion_span();

                    // if the lifetime originates from expanded code, we won't be able to remove it #104432
                    if deletion_span.is_some_and(|sp| !sp.in_derive_expansion()) {
                        self.r.lint_buffer.buffer_lint(
                            lint::builtin::UNUSED_LIFETIMES,
                            param.id,
                            param.ident.span,
                            errors::UnusedLifetime { deletion_span, ident: param.ident },
                        );
                    }
                }
            }
        }
    }

    pub(crate) fn emit_undeclared_lifetime_error(
        &self,
        lifetime_ref: &ast::Lifetime,
        outer_lifetime_ref: Option<Ident>,
    ) -> ErrorGuaranteed {
        debug_assert_ne!(lifetime_ref.ident.name, kw::UnderscoreLifetime);
        let mut err = if let Some(outer) = outer_lifetime_ref {
            struct_span_code_err!(
                self.r.dcx(),
                lifetime_ref.ident.span,
                E0401,
                "can't use generic parameters from outer item",
            )
            .with_span_label(lifetime_ref.ident.span, "use of generic parameter from outer item")
            .with_span_label(outer.span, "lifetime parameter from outer item")
        } else {
            struct_span_code_err!(
                self.r.dcx(),
                lifetime_ref.ident.span,
                E0261,
                "use of undeclared lifetime name `{}`",
                lifetime_ref.ident
            )
            .with_span_label(lifetime_ref.ident.span, "undeclared lifetime")
        };

        // Check if this is a typo of `'static`.
        if edit_distance(lifetime_ref.ident.name.as_str(), "'static", 2).is_some() {
            err.span_suggestion_verbose(
                lifetime_ref.ident.span,
                "you may have misspelled the `'static` lifetime",
                "'static",
                Applicability::MachineApplicable,
            );
        } else {
            self.suggest_introducing_lifetime(
                &mut err,
                Some(lifetime_ref.ident),
                |err, _, span, message, suggestion, span_suggs| {
                    err.multipart_suggestion(
                        message,
                        std::iter::once((span, suggestion)).chain(span_suggs).collect(),
                        Applicability::MaybeIncorrect,
                    );
                    true
                },
            );
        }

        err.emit()
    }

    fn suggest_introducing_lifetime(
        &self,
        err: &mut Diag<'_>,
        name: Option<Ident>,
        suggest: impl Fn(
            &mut Diag<'_>,
            bool,
            Span,
            Cow<'static, str>,
            String,
            Vec<(Span, String)>,
        ) -> bool,
    ) {
        let mut suggest_note = true;
        for rib in self.lifetime_ribs.iter().rev() {
            let mut should_continue = true;
            match rib.kind {
                LifetimeRibKind::Generics { binder, span, kind } => {
                    // Avoid suggesting placing lifetime parameters on constant items unless the relevant
                    // feature is enabled. Suggest the parent item as a possible location if applicable.
                    if let LifetimeBinderKind::ConstItem = kind
                        && !self.r.tcx().features().generic_const_items()
                    {
                        continue;
                    }
                    if let LifetimeBinderKind::ImplAssocType = kind {
                        continue;
                    }

                    if !span.can_be_used_for_suggestions()
                        && suggest_note
                        && let Some(name) = name
                    {
                        suggest_note = false; // Avoid displaying the same help multiple times.
                        err.span_label(
                            span,
                            format!(
                                "lifetime `{name}` is missing in item created through this procedural macro",
                            ),
                        );
                        continue;
                    }

                    let higher_ranked = matches!(
                        kind,
                        LifetimeBinderKind::FnPtrType
                            | LifetimeBinderKind::PolyTrait
                            | LifetimeBinderKind::WhereBound
                    );

                    let mut rm_inner_binders: FxIndexSet<Span> = Default::default();
                    let (span, sugg) = if span.is_empty() {
                        let mut binder_idents: FxIndexSet<Ident> = Default::default();
                        binder_idents.insert(name.unwrap_or(Ident::from_str("'a")));

                        // We need to special case binders in the following situation:
                        // Change `T: for<'a> Trait<T> + 'b` to `for<'a, 'b> T: Trait<T> + 'b`
                        // T: for<'a> Trait<T> + 'b
                        //    ^^^^^^^  remove existing inner binder `for<'a>`
                        // for<'a, 'b> T: Trait<T> + 'b
                        // ^^^^^^^^^^^  suggest outer binder `for<'a, 'b>`
                        if let LifetimeBinderKind::WhereBound = kind
                            && let Some(predicate) = self.diag_metadata.current_where_predicate
                            && let ast::WherePredicateKind::BoundPredicate(
                                ast::WhereBoundPredicate { bounded_ty, bounds, .. },
                            ) = &predicate.kind
                            && bounded_ty.id == binder
                        {
                            for bound in bounds {
                                if let ast::GenericBound::Trait(poly_trait_ref) = bound
                                    && let span = poly_trait_ref
                                        .span
                                        .with_hi(poly_trait_ref.trait_ref.path.span.lo())
                                    && !span.is_empty()
                                {
                                    rm_inner_binders.insert(span);
                                    poly_trait_ref.bound_generic_params.iter().for_each(|v| {
                                        binder_idents.insert(v.ident);
                                    });
                                }
                            }
                        }

                        let binders_sugg: String = binder_idents
                            .into_iter()
                            .map(|ident| ident.to_string())
                            .intersperse(", ".to_owned())
                            .collect();
                        let sugg = format!(
                            "{}<{}>{}",
                            if higher_ranked { "for" } else { "" },
                            binders_sugg,
                            if higher_ranked { " " } else { "" },
                        );
                        (span, sugg)
                    } else {
                        let span = self
                            .r
                            .tcx
                            .sess
                            .source_map()
                            .span_through_char(span, '<')
                            .shrink_to_hi();
                        let sugg =
                            format!("{}, ", name.map(|i| i.to_string()).as_deref().unwrap_or("'a"));
                        (span, sugg)
                    };

                    if higher_ranked {
                        let message = Cow::from(format!(
                            "consider making the {} lifetime-generic with a new `{}` lifetime",
                            kind.descr(),
                            name.map(|i| i.to_string()).as_deref().unwrap_or("'a"),
                        ));
                        should_continue = suggest(
                            err,
                            true,
                            span,
                            message,
                            sugg,
                            if !rm_inner_binders.is_empty() {
                                rm_inner_binders
                                    .into_iter()
                                    .map(|v| (v, "".to_string()))
                                    .collect::<Vec<_>>()
                            } else {
                                vec![]
                            },
                        );
                        err.note_once(
                            "for more information on higher-ranked polymorphism, visit \
                             https://doc.rust-lang.org/nomicon/hrtb.html",
                        );
                    } else if let Some(name) = name {
                        let message =
                            Cow::from(format!("consider introducing lifetime `{name}` here"));
                        should_continue = suggest(err, false, span, message, sugg, vec![]);
                    } else {
                        let message = Cow::from("consider introducing a named lifetime parameter");
                        should_continue = suggest(err, false, span, message, sugg, vec![]);
                    }
                }
                LifetimeRibKind::Item | LifetimeRibKind::ConstParamTy => break,
                _ => {}
            }
            if !should_continue {
                break;
            }
        }
    }

    pub(crate) fn emit_non_static_lt_in_const_param_ty_error(
        &self,
        lifetime_ref: &ast::Lifetime,
    ) -> ErrorGuaranteed {
        self.r
            .dcx()
            .create_err(errors::ParamInTyOfConstParam {
                span: lifetime_ref.ident.span,
                name: lifetime_ref.ident.name,
            })
            .emit()
    }

    /// Non-static lifetimes are prohibited in anonymous constants under `min_const_generics`.
    /// This function will emit an error if `generic_const_exprs` is not enabled, the body identified by
    /// `body_id` is an anonymous constant and `lifetime_ref` is non-static.
    pub(crate) fn emit_forbidden_non_static_lifetime_error(
        &self,
        cause: NoConstantGenericsReason,
        lifetime_ref: &ast::Lifetime,
    ) -> ErrorGuaranteed {
        match cause {
            NoConstantGenericsReason::IsEnumDiscriminant => self
                .r
                .dcx()
                .create_err(errors::ParamInEnumDiscriminant {
                    span: lifetime_ref.ident.span,
                    name: lifetime_ref.ident.name,
                    param_kind: errors::ParamKindInEnumDiscriminant::Lifetime,
                })
                .emit(),
            NoConstantGenericsReason::NonTrivialConstArg => {
                assert!(!self.r.tcx.features().generic_const_exprs());
                self.r
                    .dcx()
                    .create_err(errors::ParamInNonTrivialAnonConst {
                        span: lifetime_ref.ident.span,
                        name: lifetime_ref.ident.name,
                        param_kind: errors::ParamKindInNonTrivialAnonConst::Lifetime,
                        help: self.r.tcx.sess.is_nightly_build(),
                        is_ogca: self.r.tcx.features().opaque_generic_const_args(),
                        help_ogca: self.r.tcx.features().opaque_generic_const_args(),
                    })
                    .emit()
            }
        }
    }

    pub(crate) fn report_missing_lifetime_specifiers<'a>(
        &mut self,
        lifetime_refs: impl Clone + IntoIterator<Item = &'a MissingLifetime>,
        function_param_lifetimes: Option<(Vec<MissingLifetime>, Vec<ElisionFnParameter>)>,
    ) -> ErrorGuaranteed {
        let num_lifetimes: usize = lifetime_refs.clone().into_iter().map(|lt| lt.count).sum();
        let spans: Vec<_> = lifetime_refs.clone().into_iter().map(|lt| lt.span).collect();

        let mut err = struct_span_code_err!(
            self.r.dcx(),
            spans,
            E0106,
            "missing lifetime specifier{}",
            pluralize!(num_lifetimes)
        );
        self.add_missing_lifetime_specifiers_label(
            &mut err,
            lifetime_refs,
            function_param_lifetimes,
        );
        err.emit()
    }

    fn add_missing_lifetime_specifiers_label<'a>(
        &mut self,
        err: &mut Diag<'_>,
        lifetime_refs: impl Clone + IntoIterator<Item = &'a MissingLifetime>,
        function_param_lifetimes: Option<(Vec<MissingLifetime>, Vec<ElisionFnParameter>)>,
    ) {
        for &lt in lifetime_refs.clone() {
            err.span_label(
                lt.span,
                format!(
                    "expected {} lifetime parameter{}",
                    if lt.count == 1 { "named".to_string() } else { lt.count.to_string() },
                    pluralize!(lt.count),
                ),
            );
        }

        let mut in_scope_lifetimes: Vec<_> = self
            .lifetime_ribs
            .iter()
            .rev()
            .take_while(|rib| {
                !matches!(rib.kind, LifetimeRibKind::Item | LifetimeRibKind::ConstParamTy)
            })
            .flat_map(|rib| rib.bindings.iter())
            .map(|(&ident, &res)| (ident, res))
            .filter(|(ident, _)| ident.name != kw::UnderscoreLifetime)
            .collect();
        debug!(?in_scope_lifetimes);

        let mut maybe_static = false;
        debug!(?function_param_lifetimes);
        if let Some((param_lifetimes, params)) = &function_param_lifetimes {
            let elided_len = param_lifetimes.len();
            let num_params = params.len();

            let mut m = String::new();

            for (i, info) in params.iter().enumerate() {
                let ElisionFnParameter { ident, index, lifetime_count, span } = *info;
                debug_assert_ne!(lifetime_count, 0);

                err.span_label(span, "");

                if i != 0 {
                    if i + 1 < num_params {
                        m.push_str(", ");
                    } else if num_params == 2 {
                        m.push_str(" or ");
                    } else {
                        m.push_str(", or ");
                    }
                }

                let help_name = if let Some(ident) = ident {
                    format!("`{ident}`")
                } else {
                    format!("argument {}", index + 1)
                };

                if lifetime_count == 1 {
                    m.push_str(&help_name[..])
                } else {
                    m.push_str(&format!("one of {help_name}'s {lifetime_count} lifetimes")[..])
                }
            }

            if num_params == 0 {
                err.help(
                    "this function's return type contains a borrowed value, but there is no value \
                     for it to be borrowed from",
                );
                if in_scope_lifetimes.is_empty() {
                    maybe_static = true;
                    in_scope_lifetimes = vec![(
                        Ident::with_dummy_span(kw::StaticLifetime),
                        (DUMMY_NODE_ID, LifetimeRes::Static),
                    )];
                }
            } else if elided_len == 0 {
                err.help(
                    "this function's return type contains a borrowed value with an elided \
                     lifetime, but the lifetime cannot be derived from the arguments",
                );
                if in_scope_lifetimes.is_empty() {
                    maybe_static = true;
                    in_scope_lifetimes = vec![(
                        Ident::with_dummy_span(kw::StaticLifetime),
                        (DUMMY_NODE_ID, LifetimeRes::Static),
                    )];
                }
            } else if num_params == 1 {
                err.help(format!(
                    "this function's return type contains a borrowed value, but the signature does \
                     not say which {m} it is borrowed from",
                ));
            } else {
                err.help(format!(
                    "this function's return type contains a borrowed value, but the signature does \
                     not say whether it is borrowed from {m}",
                ));
            }
        }

        #[allow(rustc::symbol_intern_string_literal)]
        let existing_name = match &in_scope_lifetimes[..] {
            [] => Symbol::intern("'a"),
            [(existing, _)] => existing.name,
            _ => Symbol::intern("'lifetime"),
        };

        let mut spans_suggs: Vec<_> = Vec::new();
        let build_sugg = |lt: MissingLifetime| match lt.kind {
            MissingLifetimeKind::Underscore => {
                debug_assert_eq!(lt.count, 1);
                (lt.span, existing_name.to_string())
            }
            MissingLifetimeKind::Ampersand => {
                debug_assert_eq!(lt.count, 1);
                (lt.span.shrink_to_hi(), format!("{existing_name} "))
            }
            MissingLifetimeKind::Comma => {
                let sugg: String = std::iter::repeat_n([existing_name.as_str(), ", "], lt.count)
                    .flatten()
                    .collect();
                (lt.span.shrink_to_hi(), sugg)
            }
            MissingLifetimeKind::Brackets => {
                let sugg: String = std::iter::once("<")
                    .chain(std::iter::repeat_n(existing_name.as_str(), lt.count).intersperse(", "))
                    .chain([">"])
                    .collect();
                (lt.span.shrink_to_hi(), sugg)
            }
        };
        for &lt in lifetime_refs.clone() {
            spans_suggs.push(build_sugg(lt));
        }
        debug!(?spans_suggs);
        match in_scope_lifetimes.len() {
            0 => {
                if let Some((param_lifetimes, _)) = function_param_lifetimes {
                    for lt in param_lifetimes {
                        spans_suggs.push(build_sugg(lt))
                    }
                }
                self.suggest_introducing_lifetime(
                    err,
                    None,
                    |err, higher_ranked, span, message, intro_sugg, _| {
                        err.multipart_suggestion(
                            message,
                            std::iter::once((span, intro_sugg))
                                .chain(spans_suggs.clone())
                                .collect(),
                            Applicability::MaybeIncorrect,
                        );
                        higher_ranked
                    },
                );
            }
            1 => {
                let post = if maybe_static {
                    let mut lifetime_refs = lifetime_refs.clone().into_iter();
                    let owned = if let Some(lt) = lifetime_refs.next()
                        && lifetime_refs.next().is_none()
                        && lt.kind != MissingLifetimeKind::Ampersand
                    {
                        ", or if you will only have owned values"
                    } else {
                        ""
                    };
                    format!(
                        ", but this is uncommon unless you're returning a borrowed value from a \
                         `const` or a `static`{owned}",
                    )
                } else {
                    String::new()
                };
                err.multipart_suggestion(
                    format!("consider using the `{existing_name}` lifetime{post}"),
                    spans_suggs,
                    Applicability::MaybeIncorrect,
                );
                if maybe_static {
                    // NOTE: what follows are general suggestions, but we'd want to perform some
                    // minimal flow analysis to provide more accurate suggestions. For example, if
                    // we identified that the return expression references only one argument, we
                    // would suggest borrowing only that argument, and we'd skip the prior
                    // "use `'static`" suggestion entirely.
                    let mut lifetime_refs = lifetime_refs.clone().into_iter();
                    if let Some(lt) = lifetime_refs.next()
                        && lifetime_refs.next().is_none()
                        && (lt.kind == MissingLifetimeKind::Ampersand
                            || lt.kind == MissingLifetimeKind::Underscore)
                    {
                        let pre = if let Some((kind, _span)) = self.diag_metadata.current_function
                            && let FnKind::Fn(_, _, ast::Fn { sig, .. }) = kind
                            && !sig.decl.inputs.is_empty()
                            && let sugg = sig
                                .decl
                                .inputs
                                .iter()
                                .filter_map(|param| {
                                    if param.ty.span.contains(lt.span) {
                                        // We don't want to suggest `fn elision(_: &fn() -> &i32)`
                                        // when we have `fn elision(_: fn() -> &i32)`
                                        None
                                    } else if let TyKind::CVarArgs = param.ty.kind {
                                        // Don't suggest `&...` for ffi fn with varargs
                                        None
                                    } else if let TyKind::ImplTrait(..) = &param.ty.kind {
                                        // We handle these in the next `else if` branch.
                                        None
                                    } else {
                                        Some((param.ty.span.shrink_to_lo(), "&".to_string()))
                                    }
                                })
                                .collect::<Vec<_>>()
                            && !sugg.is_empty()
                        {
                            let (the, s) = if sig.decl.inputs.len() == 1 {
                                ("the", "")
                            } else {
                                ("one of the", "s")
                            };
                            let dotdotdot =
                                if lt.kind == MissingLifetimeKind::Ampersand { "..." } else { "" };
                            err.multipart_suggestion(
                                format!(
                                    "instead, you are more likely to want to change {the} \
                                     argument{s} to be borrowed{dotdotdot}",
                                ),
                                sugg,
                                Applicability::MaybeIncorrect,
                            );
                            "...or alternatively, you might want"
                        } else if (lt.kind == MissingLifetimeKind::Ampersand
                            || lt.kind == MissingLifetimeKind::Underscore)
                            && let Some((kind, _span)) = self.diag_metadata.current_function
                            && let FnKind::Fn(_, _, ast::Fn { sig, .. }) = kind
                            && let ast::FnRetTy::Ty(ret_ty) = &sig.decl.output
                            && !sig.decl.inputs.is_empty()
                            && let arg_refs = sig
                                .decl
                                .inputs
                                .iter()
                                .filter_map(|param| match &param.ty.kind {
                                    TyKind::ImplTrait(_, bounds) => Some(bounds),
                                    _ => None,
                                })
                                .flat_map(|bounds| bounds.into_iter())
                                .collect::<Vec<_>>()
                            && !arg_refs.is_empty()
                        {
                            // We have a situation like
                            // fn g(mut x: impl Iterator<Item = &()>) -> Option<&()>
                            // So we look at every ref in the trait bound. If there's any, we
                            // suggest
                            // fn g<'a>(mut x: impl Iterator<Item = &'a ()>) -> Option<&'a ()>
                            let mut lt_finder =
                                LifetimeFinder { lifetime: lt.span, found: None, seen: vec![] };
                            for bound in arg_refs {
                                if let ast::GenericBound::Trait(trait_ref) = bound {
                                    lt_finder.visit_trait_ref(&trait_ref.trait_ref);
                                }
                            }
                            lt_finder.visit_ty(ret_ty);
                            let spans_suggs: Vec<_> = lt_finder
                                .seen
                                .iter()
                                .filter_map(|ty| match &ty.kind {
                                    TyKind::Ref(_, mut_ty) => {
                                        let span = ty.span.with_hi(mut_ty.ty.span.lo());
                                        Some((span, "&'a ".to_string()))
                                    }
                                    _ => None,
                                })
                                .collect();
                            self.suggest_introducing_lifetime(
                                err,
                                None,
                                |err, higher_ranked, span, message, intro_sugg, _| {
                                    err.multipart_suggestion(
                                        message,
                                        std::iter::once((span, intro_sugg))
                                            .chain(spans_suggs.clone())
                                            .collect(),
                                        Applicability::MaybeIncorrect,
                                    );
                                    higher_ranked
                                },
                            );
                            "alternatively, you might want"
                        } else {
                            "instead, you are more likely to want"
                        };
                        let mut owned_sugg = lt.kind == MissingLifetimeKind::Ampersand;
                        let mut sugg_is_str_to_string = false;
                        let mut sugg = vec![(lt.span, String::new())];
                        if let Some((kind, _span)) = self.diag_metadata.current_function
                            && let FnKind::Fn(_, _, ast::Fn { sig, .. }) = kind
                        {
                            let mut lt_finder =
                                LifetimeFinder { lifetime: lt.span, found: None, seen: vec![] };
                            for param in &sig.decl.inputs {
                                lt_finder.visit_ty(&param.ty);
                            }
                            if let ast::FnRetTy::Ty(ret_ty) = &sig.decl.output {
                                lt_finder.visit_ty(ret_ty);
                                let mut ret_lt_finder =
                                    LifetimeFinder { lifetime: lt.span, found: None, seen: vec![] };
                                ret_lt_finder.visit_ty(ret_ty);
                                if let [Ty { span, kind: TyKind::Ref(_, mut_ty), .. }] =
                                    &ret_lt_finder.seen[..]
                                {
                                    // We might have a situation like
                                    // fn g(mut x: impl Iterator<Item = &'_ ()>) -> Option<&'_ ()>
                                    // but `lt.span` only points at `'_`, so to suggest `-> Option<()>`
                                    // we need to find a more accurate span to end up with
                                    // fn g<'a>(mut x: impl Iterator<Item = &'_ ()>) -> Option<()>
                                    sugg = vec![(span.with_hi(mut_ty.ty.span.lo()), String::new())];
                                    owned_sugg = true;
                                }
                            }
                            if let Some(ty) = lt_finder.found {
                                if let TyKind::Path(None, path) = &ty.kind {
                                    // Check if the path being borrowed is likely to be owned.
                                    let path: Vec<_> = Segment::from_path(path);
                                    match self.resolve_path(
                                        &path,
                                        Some(TypeNS),
                                        None,
                                        PathSource::Type,
                                    ) {
                                        PathResult::Module(ModuleOrUniformRoot::Module(module)) => {
                                            match module.res() {
                                                Some(Res::PrimTy(PrimTy::Str)) => {
                                                    // Don't suggest `-> str`, suggest `-> String`.
                                                    sugg = vec![(
                                                        lt.span.with_hi(ty.span.hi()),
                                                        "String".to_string(),
                                                    )];
                                                    sugg_is_str_to_string = true;
                                                }
                                                Some(Res::PrimTy(..)) => {}
                                                Some(Res::Def(
                                                    DefKind::Struct
                                                    | DefKind::Union
                                                    | DefKind::Enum
                                                    | DefKind::ForeignTy
                                                    | DefKind::AssocTy
                                                    | DefKind::OpaqueTy
                                                    | DefKind::TyParam,
                                                    _,
                                                )) => {}
                                                _ => {
                                                    // Do not suggest in all other cases.
                                                    owned_sugg = false;
                                                }
                                            }
                                        }
                                        PathResult::NonModule(res) => {
                                            match res.base_res() {
                                                Res::PrimTy(PrimTy::Str) => {
                                                    // Don't suggest `-> str`, suggest `-> String`.
                                                    sugg = vec![(
                                                        lt.span.with_hi(ty.span.hi()),
                                                        "String".to_string(),
                                                    )];
                                                    sugg_is_str_to_string = true;
                                                }
                                                Res::PrimTy(..) => {}
                                                Res::Def(
                                                    DefKind::Struct
                                                    | DefKind::Union
                                                    | DefKind::Enum
                                                    | DefKind::ForeignTy
                                                    | DefKind::AssocTy
                                                    | DefKind::OpaqueTy
                                                    | DefKind::TyParam,
                                                    _,
                                                ) => {}
                                                _ => {
                                                    // Do not suggest in all other cases.
                                                    owned_sugg = false;
                                                }
                                            }
                                        }
                                        _ => {
                                            // Do not suggest in all other cases.
                                            owned_sugg = false;
                                        }
                                    }
                                }
                                if let TyKind::Slice(inner_ty) = &ty.kind {
                                    // Don't suggest `-> [T]`, suggest `-> Vec<T>`.
                                    sugg = vec![
                                        (lt.span.with_hi(inner_ty.span.lo()), "Vec<".to_string()),
                                        (ty.span.with_lo(inner_ty.span.hi()), ">".to_string()),
                                    ];
                                }
                            }
                        }
                        if owned_sugg {
                            if let Some(span) =
                                self.find_ref_prefix_span_for_owned_suggestion(lt.span)
                                && !sugg_is_str_to_string
                            {
                                sugg = vec![(span, String::new())];
                            }
                            err.multipart_suggestion(
                                format!("{pre} to return an owned value"),
                                sugg,
                                Applicability::MaybeIncorrect,
                            );
                        }
                    }
                }
            }
            _ => {
                let lifetime_spans: Vec<_> =
                    in_scope_lifetimes.iter().map(|(ident, _)| ident.span).collect();
                err.span_note(lifetime_spans, "these named lifetimes are available to use");

                if spans_suggs.len() > 0 {
                    // This happens when we have `Foo<T>` where we point at the space before `T`,
                    // but this can be confusing so we give a suggestion with placeholders.
                    err.multipart_suggestion(
                        "consider using one of the available lifetimes here",
                        spans_suggs,
                        Applicability::HasPlaceholders,
                    );
                }
            }
        }
    }

    fn find_ref_prefix_span_for_owned_suggestion(&self, lifetime: Span) -> Option<Span> {
        let mut finder = RefPrefixSpanFinder { lifetime, span: None };
        if let Some(item) = self.diag_metadata.current_item {
            finder.visit_item(item);
        } else if let Some((kind, _span)) = self.diag_metadata.current_function
            && let FnKind::Fn(_, _, ast::Fn { sig, .. }) = kind
        {
            for param in &sig.decl.inputs {
                finder.visit_ty(&param.ty);
            }
            if let ast::FnRetTy::Ty(ret_ty) = &sig.decl.output {
                finder.visit_ty(ret_ty);
            }
        }
        finder.span
    }
}

fn mk_where_bound_predicate(
    path: &Path,
    poly_trait_ref: &ast::PolyTraitRef,
    ty: &Ty,
) -> Option<ast::WhereBoundPredicate> {
    let modified_segments = {
        let mut segments = path.segments.clone();
        let [preceding @ .., second_last, last] = segments.as_mut_slice() else {
            return None;
        };
        let mut segments = ThinVec::from(preceding);

        let added_constraint = ast::AngleBracketedArg::Constraint(ast::AssocItemConstraint {
            id: DUMMY_NODE_ID,
            ident: last.ident,
            gen_args: None,
            kind: ast::AssocItemConstraintKind::Equality {
                term: ast::Term::Ty(Box::new(ast::Ty {
                    kind: ast::TyKind::Path(None, poly_trait_ref.trait_ref.path.clone()),
                    id: DUMMY_NODE_ID,
                    span: DUMMY_SP,
                    tokens: None,
                })),
            },
            span: DUMMY_SP,
        });

        match second_last.args.as_deref_mut() {
            Some(ast::GenericArgs::AngleBracketed(ast::AngleBracketedArgs { args, .. })) => {
                args.push(added_constraint);
            }
            Some(_) => return None,
            None => {
                second_last.args =
                    Some(Box::new(ast::GenericArgs::AngleBracketed(ast::AngleBracketedArgs {
                        args: ThinVec::from([added_constraint]),
                        span: DUMMY_SP,
                    })));
            }
        }

        segments.push(second_last.clone());
        segments
    };

    let new_where_bound_predicate = ast::WhereBoundPredicate {
        bound_generic_params: ThinVec::new(),
        bounded_ty: Box::new(ty.clone()),
        bounds: vec![ast::GenericBound::Trait(ast::PolyTraitRef {
            bound_generic_params: ThinVec::new(),
            modifiers: ast::TraitBoundModifiers::NONE,
            trait_ref: ast::TraitRef {
                path: ast::Path { segments: modified_segments, span: DUMMY_SP, tokens: None },
                ref_id: DUMMY_NODE_ID,
            },
            span: DUMMY_SP,
            parens: ast::Parens::No,
        })],
    };

    Some(new_where_bound_predicate)
}

/// Report lifetime/lifetime shadowing as an error.
pub(super) fn signal_lifetime_shadowing(
    sess: &Session,
    orig: Ident,
    shadower: Ident,
) -> ErrorGuaranteed {
    struct_span_code_err!(
        sess.dcx(),
        shadower.span,
        E0496,
        "lifetime name `{}` shadows a lifetime name that is already in scope",
        orig.name,
    )
    .with_span_label(orig.span, "first declared here")
    .with_span_label(shadower.span, format!("lifetime `{}` already in scope", orig.name))
    .emit()
}

struct LifetimeFinder<'ast> {
    lifetime: Span,
    found: Option<&'ast Ty>,
    seen: Vec<&'ast Ty>,
}

impl<'ast> Visitor<'ast> for LifetimeFinder<'ast> {
    fn visit_ty(&mut self, t: &'ast Ty) {
        if let TyKind::Ref(_, mut_ty) | TyKind::PinnedRef(_, mut_ty) = &t.kind {
            self.seen.push(t);
            if t.span.lo() == self.lifetime.lo() {
                self.found = Some(&mut_ty.ty);
            }
        }
        walk_ty(self, t)
    }
}

struct RefPrefixSpanFinder {
    lifetime: Span,
    span: Option<Span>,
}

impl<'ast> Visitor<'ast> for RefPrefixSpanFinder {
    fn visit_ty(&mut self, t: &'ast Ty) {
        if self.span.is_some() {
            return;
        }
        if let TyKind::Ref(_, mut_ty) | TyKind::PinnedRef(_, mut_ty) = &t.kind
            && t.span.lo() == self.lifetime.lo()
        {
            self.span = Some(t.span.with_hi(mut_ty.ty.span.lo()));
            return;
        }
        walk_ty(self, t);
    }
}

/// Shadowing involving a label is only a warning for historical reasons.
// NOTE: make this a proper lint.
pub(super) fn signal_label_shadowing(sess: &Session, orig: Span, shadower: Ident) {
    let name = shadower.name;
    let shadower = shadower.span;
    sess.dcx()
        .struct_span_warn(
            shadower,
            format!("label name `{name}` shadows a label name that is already in scope"),
        )
        .with_span_label(orig, "first declared here")
        .with_span_label(shadower, format!("label `{name}` already in scope"))
        .emit();
}

struct ParentPathVisitor<'a> {
    target: Ident,
    parent: Option<&'a PathSegment>,
    stack: Vec<&'a Ty>,
}

impl<'a> ParentPathVisitor<'a> {
    fn new(self_ty: &'a Ty, target: Ident) -> Self {
        let mut v = ParentPathVisitor { target, parent: None, stack: Vec::new() };

        v.visit_ty(self_ty);
        v
    }
}

impl<'a> Visitor<'a> for ParentPathVisitor<'a> {
    fn visit_ty(&mut self, ty: &'a Ty) {
        if self.parent.is_some() {
            return;
        }

        // push current type
        self.stack.push(ty);

        if let TyKind::Path(_, path) = &ty.kind
            // is this just `N`?
            && let [segment] = path.segments.as_slice()
            && segment.ident == self.target
            // parent is previous element in stack
            && let [.., parent_ty, _ty] = self.stack.as_slice()
            && let TyKind::Path(_, parent_path) = &parent_ty.kind
        {
            self.parent = parent_path.segments.first();
        }

        walk_ty(self, ty);

        self.stack.pop();
    }
}
