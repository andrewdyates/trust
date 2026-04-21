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
    fn smart_resolve_context_dependent_help(
        &mut self,
        err: &mut Diag<'_>,
        span: Span,
        source: PathSource<'_, '_, '_>,
        path: &[Segment],
        res: Res,
        path_str: &str,
        fallback_label: &str,
    ) -> bool {
        let ns = source.namespace();
        let is_expected = &|res| source.is_expected(res);

        let path_sep = |this: &Self, err: &mut Diag<'_>, expr: &Expr, kind: DefKind| {
            const MESSAGE: &str = "use the path separator to refer to an item";

            let (lhs_span, rhs_span) = match &expr.kind {
                ExprKind::Field(base, ident) => (base.span, ident.span),
                ExprKind::MethodCall(box MethodCall { receiver, span, .. }) => {
                    (receiver.span, *span)
                }
                _ => return false,
            };

            if lhs_span.eq_ctxt(rhs_span) {
                err.span_suggestion_verbose(
                    lhs_span.between(rhs_span),
                    MESSAGE,
                    "::",
                    Applicability::MaybeIncorrect,
                );
                true
            } else if matches!(kind, DefKind::Struct | DefKind::TyAlias)
                && let Some(lhs_source_span) = lhs_span.find_ancestor_inside(expr.span)
                && let Ok(snippet) = this.r.tcx.sess.source_map().span_to_snippet(lhs_source_span)
            {
                // The LHS is a type that originates from a macro call.
                // We have to add angle brackets around it.

                err.span_suggestion_verbose(
                    lhs_source_span.until(rhs_span),
                    MESSAGE,
                    format!("<{snippet}>::"),
                    Applicability::MaybeIncorrect,
                );
                true
            } else {
                // Either we were unable to obtain the source span / the snippet or
                // the LHS originates from a macro call and it is not a type and thus
                // there is no way to replace `.` with `::` and still somehow suggest
                // valid Rust code.

                false
            }
        };

        let find_span = |source: &PathSource<'_, '_, '_>, err: &mut Diag<'_>| {
            match source {
                PathSource::Expr(Some(Expr { span, kind: ExprKind::Call(_, _), .. }))
                | PathSource::TupleStruct(span, _) => {
                    // We want the main underline to cover the suggested code as well for
                    // cleaner output.
                    err.span(*span);
                    *span
                }
                _ => span,
            }
        };

        let bad_struct_syntax_suggestion = |this: &mut Self, err: &mut Diag<'_>, def_id: DefId| {
            let (followed_by_brace, closing_brace) = this.followed_by_brace(span);

            match source {
                PathSource::Expr(Some(
                    parent @ Expr { kind: ExprKind::Field(..) | ExprKind::MethodCall(..), .. },
                )) if path_sep(this, err, parent, DefKind::Struct) => {}
                PathSource::Expr(
                    None
                    | Some(Expr {
                        kind:
                            ExprKind::Path(..)
                            | ExprKind::Binary(..)
                            | ExprKind::Unary(..)
                            | ExprKind::If(..)
                            | ExprKind::While(..)
                            | ExprKind::ForLoop { .. }
                            | ExprKind::Match(..),
                        ..
                    }),
                ) if followed_by_brace => {
                    if let Some(sp) = closing_brace {
                        err.span_label(span, fallback_label.to_string());
                        err.multipart_suggestion(
                            "surround the struct literal with parentheses",
                            vec![
                                (sp.shrink_to_lo(), "(".to_string()),
                                (sp.shrink_to_hi(), ")".to_string()),
                            ],
                            Applicability::MaybeIncorrect,
                        );
                    } else {
                        err.span_label(
                            span, // Note the parentheses surrounding the suggestion below
                            format!(
                                "you might want to surround a struct literal with parentheses: \
                                 `({path_str} {{ /* fields */ }})`?"
                            ),
                        );
                    }
                }
                PathSource::Expr(_) | PathSource::TupleStruct(..) | PathSource::Pat => {
                    let span = find_span(&source, err);
                    err.span_label(this.r.def_span(def_id), format!("`{path_str}` defined here"));

                    let (tail, descr, applicability, old_fields) = match source {
                        PathSource::Pat => ("", "pattern", Applicability::MachineApplicable, None),
                        PathSource::TupleStruct(_, args) => (
                            "",
                            "pattern",
                            Applicability::MachineApplicable,
                            Some(
                                args.iter()
                                    .map(|a| this.r.tcx.sess.source_map().span_to_snippet(*a).ok())
                                    .collect::<Vec<Option<String>>>(),
                            ),
                        ),
                        _ => (": val", "literal", Applicability::HasPlaceholders, None),
                    };

                    if !this.has_private_fields(def_id) {
                        // If the fields of the type are private, we shouldn't be suggesting using
                        // the struct literal syntax at all, as that will cause a subsequent error.
                        let fields = this.r.field_idents(def_id);
                        let has_fields = fields.as_ref().is_some_and(|f| !f.is_empty());

                        if let PathSource::Expr(Some(Expr {
                            kind: ExprKind::Call(path, args),
                            span,
                            ..
                        })) = source
                            && !args.is_empty()
                            && let Some(fields) = &fields
                            && args.len() == fields.len()
                        // Make sure we have same number of args as fields
                        {
                            let path_span = path.span;
                            let mut parts = Vec::new();

                            // Start with the opening brace
                            parts.push((
                                path_span.shrink_to_hi().until(args[0].span),
                                "{".to_owned(),
                            ));

                            for (field, arg) in fields.iter().zip(args.iter()) {
                                // Add the field name before the argument
                                parts.push((arg.span.shrink_to_lo(), format!("{}: ", field)));
                            }

                            // Add the closing brace
                            parts.push((
                                args.last().expect("invariant: non-empty collection").span.shrink_to_hi().until(span.shrink_to_hi()),
                                "}".to_owned(),
                            ));

                            err.multipart_suggestion(
                                format!("use struct {descr} syntax instead of calling"),
                                parts,
                                applicability,
                            );
                        } else {
                            let (fields, applicability) = match fields {
                                Some(fields) => {
                                    let fields = if let Some(old_fields) = old_fields {
                                        fields
                                            .iter()
                                            .enumerate()
                                            .map(|(idx, new)| (new, old_fields.get(idx)))
                                            .map(|(new, old)| {
                                                if let Some(Some(old)) = old
                                                    && new.as_str() != old
                                                {
                                                    format!("{new}: {old}")
                                                } else {
                                                    new.to_string()
                                                }
                                            })
                                            .collect::<Vec<String>>()
                                    } else {
                                        fields
                                            .iter()
                                            .map(|f| format!("{f}{tail}"))
                                            .collect::<Vec<String>>()
                                    };

                                    (fields.join(", "), applicability)
                                }
                                None => {
                                    ("/* fields */".to_string(), Applicability::HasPlaceholders)
                                }
                            };
                            let pad = if has_fields { " " } else { "" };
                            err.span_suggestion(
                                span,
                                format!("use struct {descr} syntax instead"),
                                format!("{path_str} {{{pad}{fields}{pad}}}"),
                                applicability,
                            );
                        }
                    }
                    if let PathSource::Expr(Some(Expr {
                        kind: ExprKind::Call(path, args),
                        span: call_span,
                        ..
                    })) = source
                    {
                        this.suggest_alternative_construction_methods(
                            def_id,
                            err,
                            path.span,
                            *call_span,
                            &args[..],
                        );
                    }
                }
                _ => {
                    err.span_label(span, fallback_label.to_string());
                }
            }
        };

        match (res, source) {
            (
                Res::Def(DefKind::Macro(kinds), def_id),
                PathSource::Expr(Some(Expr {
                    kind: ExprKind::Index(..) | ExprKind::Call(..), ..
                }))
                | PathSource::Struct(_),
            ) if kinds.contains(MacroKinds::BANG) => {
                // Don't suggest macro if it's unstable.
                let suggestable = def_id.is_local()
                    || self.r.tcx.lookup_stability(def_id).is_none_or(|s| s.is_stable());

                err.span_label(span, fallback_label.to_string());

                // Don't suggest `!` for a macro invocation if there are generic args
                if path
                    .last()
                    .is_some_and(|segment| !segment.has_generic_args && !segment.has_lifetime_args)
                    && suggestable
                {
                    err.span_suggestion_verbose(
                        span.shrink_to_hi(),
                        "use `!` to invoke the macro",
                        "!",
                        Applicability::MaybeIncorrect,
                    );
                }

                if path_str == "try" && span.is_rust_2015() {
                    err.note("if you want the `try` keyword, you need Rust 2018 or later");
                }
            }
            (Res::Def(DefKind::Macro(kinds), _), _) if kinds.contains(MacroKinds::BANG) => {
                err.span_label(span, fallback_label.to_string());
            }
            (Res::Def(DefKind::TyAlias, def_id), PathSource::Trait(_)) => {
                err.span_label(span, "type aliases cannot be used as traits");
                if self.r.tcx.sess.is_nightly_build() {
                    let msg = "you might have meant to use `#![feature(trait_alias)]` instead of a \
                               `type` alias";
                    let span = self.r.def_span(def_id);
                    if let Ok(snip) = self.r.tcx.sess.source_map().span_to_snippet(span) {
                        // The span contains a type alias so we should be able to
                        // replace `type` with `trait`.
                        let snip = snip.replacen("type", "trait", 1);
                        err.span_suggestion(span, msg, snip, Applicability::MaybeIncorrect);
                    } else {
                        err.span_help(span, msg);
                    }
                }
            }
            (
                Res::Def(kind @ (DefKind::Mod | DefKind::Trait | DefKind::TyAlias), _),
                PathSource::Expr(Some(parent)),
            ) if path_sep(self, err, parent, kind) => {
                return true;
            }
            (
                Res::Def(DefKind::Enum, def_id),
                PathSource::TupleStruct(..) | PathSource::Expr(..),
            ) => {
                self.suggest_using_enum_variant(err, source, def_id, span);
            }
            (Res::Def(DefKind::Struct, def_id), source) if ns == ValueNS => {
                let struct_ctor = match def_id.as_local() {
                    Some(def_id) => self.r.struct_constructors.get(&def_id).cloned(),
                    None => {
                        let ctor = self.r.cstore().ctor_untracked(self.r.tcx(), def_id);
                        ctor.map(|(ctor_kind, ctor_def_id)| {
                            let ctor_res =
                                Res::Def(DefKind::Ctor(CtorOf::Struct, ctor_kind), ctor_def_id);
                            let ctor_vis = self.r.tcx.visibility(ctor_def_id);
                            let field_visibilities = self
                                .r
                                .tcx
                                .associated_item_def_ids(def_id)
                                .iter()
                                .map(|&field_id| self.r.tcx.visibility(field_id))
                                .collect();
                            (ctor_res, ctor_vis, field_visibilities)
                        })
                    }
                };

                let (ctor_def, ctor_vis, fields) = if let Some(struct_ctor) = struct_ctor {
                    if let PathSource::Expr(Some(parent)) = source
                        && let ExprKind::Field(..) | ExprKind::MethodCall(..) = parent.kind
                    {
                        bad_struct_syntax_suggestion(self, err, def_id);
                        return true;
                    }
                    struct_ctor
                } else {
                    bad_struct_syntax_suggestion(self, err, def_id);
                    return true;
                };

                let is_accessible = self.r.is_accessible_from(ctor_vis, self.parent_scope.module);
                if let Some(use_span) = self.r.inaccessible_ctor_reexport.get(&span)
                    && is_accessible
                {
                    err.span_note(
                        *use_span,
                        "the type is accessed through this re-export, but the type's constructor \
                         is not visible in this import's scope due to private fields",
                    );
                    if is_accessible
                        && fields
                            .iter()
                            .all(|vis| self.r.is_accessible_from(*vis, self.parent_scope.module))
                    {
                        err.span_suggestion_verbose(
                            span,
                            "the type can be constructed directly, because its fields are \
                             available from the current scope",
                            // Using `tcx.def_path_str` causes the compiler to hang.
                            // We don't need to handle foreign crate types because in that case you
                            // can't access the ctor either way.
                            format!(
                                "crate{}", // The method already has leading `::`.
                                self.r.tcx.def_path(def_id).to_string_no_crate_verbose(),
                            ),
                            Applicability::MachineApplicable,
                        );
                    }
                    self.update_err_for_private_tuple_struct_fields(err, &source, def_id);
                }
                if !is_expected(ctor_def) || is_accessible {
                    return true;
                }

                let field_spans =
                    self.update_err_for_private_tuple_struct_fields(err, &source, def_id);

                if let Some(spans) =
                    field_spans.filter(|spans| spans.len() > 0 && fields.len() == spans.len())
                {
                    let non_visible_spans: Vec<Span> = iter::zip(&fields, &spans)
                        .filter(|(vis, _)| {
                            !self.r.is_accessible_from(**vis, self.parent_scope.module)
                        })
                        .map(|(_, span)| *span)
                        .collect();

                    if non_visible_spans.len() > 0 {
                        if let Some(fields) = self.r.field_visibility_spans.get(&def_id) {
                            err.multipart_suggestion(
                                format!(
                                    "consider making the field{} publicly accessible",
                                    pluralize!(fields.len())
                                ),
                                fields.iter().map(|span| (*span, "pub ".to_string())).collect(),
                                Applicability::MaybeIncorrect,
                            );
                        }

                        let mut m: MultiSpan = non_visible_spans.clone().into();
                        non_visible_spans
                            .into_iter()
                            .for_each(|s| m.push_span_label(s, "private field"));
                        err.span_note(m, "constructor is not visible here due to private fields");
                    }

                    return true;
                }

                err.span_label(span, "constructor is not visible here due to private fields");
            }
            (Res::Def(DefKind::Union | DefKind::Variant, def_id), _) if ns == ValueNS => {
                bad_struct_syntax_suggestion(self, err, def_id);
            }
            (Res::Def(DefKind::Ctor(_, CtorKind::Const), def_id), _) if ns == ValueNS => {
                match source {
                    PathSource::Expr(_) | PathSource::TupleStruct(..) | PathSource::Pat => {
                        let span = find_span(&source, err);
                        err.span_label(
                            self.r.def_span(def_id),
                            format!("`{path_str}` defined here"),
                        );
                        err.span_suggestion(
                            span,
                            "use this syntax instead",
                            path_str,
                            Applicability::MaybeIncorrect,
                        );
                    }
                    _ => return false,
                }
            }
            (Res::Def(DefKind::Ctor(_, CtorKind::Fn), ctor_def_id), _) if ns == ValueNS => {
                let def_id = self.r.tcx.parent(ctor_def_id);
                err.span_label(self.r.def_span(def_id), format!("`{path_str}` defined here"));
                let fields = self.r.field_idents(def_id).map_or_else(
                    || "/* fields */".to_string(),
                    |field_ids| vec!["_"; field_ids.len()].join(", "),
                );
                err.span_suggestion(
                    span,
                    "use the tuple variant pattern syntax instead",
                    format!("{path_str}({fields})"),
                    Applicability::HasPlaceholders,
                );
            }
            (Res::SelfTyParam { .. } | Res::SelfTyAlias { .. }, _) if ns == ValueNS => {
                err.span_label(span, fallback_label.to_string());
                err.note("can't use `Self` as a constructor, you must use the implemented struct");
            }
            (
                Res::Def(DefKind::TyAlias | DefKind::AssocTy, _),
                PathSource::TraitItem(ValueNS, PathSource::TupleStruct(whole, args)),
            ) => {
                err.note("can't use a type alias as tuple pattern");

                let mut suggestion = Vec::new();

                if let &&[first, ..] = args
                    && let &&[.., last] = args
                {
                    suggestion.extend([
                        // "0: " has to be included here so that the fix is machine applicable.
                        //
                        // If this would only add " { " and then the code below add "0: ",
                        // rustfix would crash, because end of this suggestion is the same as start
                        // of the suggestion below. Thus, we have to merge these...
                        (span.between(first), " { 0: ".to_owned()),
                        (last.between(whole.shrink_to_hi()), " }".to_owned()),
                    ]);

                    suggestion.extend(
                        args.iter()
                            .enumerate()
                            .skip(1) // See above
                            .map(|(index, &arg)| (arg.shrink_to_lo(), format!("{index}: "))),
                    )
                } else {
                    suggestion.push((span.between(whole.shrink_to_hi()), " {}".to_owned()));
                }

                err.multipart_suggestion(
                    "use struct pattern instead",
                    suggestion,
                    Applicability::MachineApplicable,
                );
            }
            (
                Res::Def(DefKind::TyAlias | DefKind::AssocTy, _),
                PathSource::TraitItem(
                    ValueNS,
                    PathSource::Expr(Some(ast::Expr {
                        span: whole,
                        kind: ast::ExprKind::Call(_, args),
                        ..
                    })),
                ),
            ) => {
                err.note("can't use a type alias as a constructor");

                let mut suggestion = Vec::new();

                if let [first, ..] = &**args
                    && let [.., last] = &**args
                {
                    suggestion.extend([
                        // "0: " has to be included here so that the fix is machine applicable.
                        //
                        // If this would only add " { " and then the code below add "0: ",
                        // rustfix would crash, because end of this suggestion is the same as start
                        // of the suggestion below. Thus, we have to merge these...
                        (span.between(first.span), " { 0: ".to_owned()),
                        (last.span.between(whole.shrink_to_hi()), " }".to_owned()),
                    ]);

                    suggestion.extend(
                        args.iter()
                            .enumerate()
                            .skip(1) // See above
                            .map(|(index, arg)| (arg.span.shrink_to_lo(), format!("{index}: "))),
                    )
                } else {
                    suggestion.push((span.between(whole.shrink_to_hi()), " {}".to_owned()));
                }

                err.multipart_suggestion(
                    "use struct expression instead",
                    suggestion,
                    Applicability::MachineApplicable,
                );
            }
            _ => return false,
        }
        true
    }

    fn suggest_alternative_construction_methods(
        &mut self,
        def_id: DefId,
        err: &mut Diag<'_>,
        path_span: Span,
        call_span: Span,
        args: &[Box<Expr>],
    ) {
        if def_id.is_local() {
            // Doing analysis on local `DefId`s would cause infinite recursion.
            return;
        }
        // Look at all the associated functions without receivers in the type's
        // inherent impls to look for builders that return `Self`
        let mut items = self
            .r
            .tcx
            .inherent_impls(def_id)
            .iter()
            .flat_map(|&i| self.r.tcx.associated_items(i).in_definition_order())
            // Only assoc fn with no receivers.
            .filter(|item| item.is_fn() && !item.is_method())
            .filter_map(|item| {
                // Only assoc fns that return `Self`
                let fn_sig = self.r.tcx.fn_sig(item.def_id).skip_binder();
                // Don't normalize the return type, because that can cause cycle errors.
                let ret_ty = fn_sig.output().skip_binder();
                let ty::Adt(def, _args) = ret_ty.kind() else {
                    return None;
                };
                let input_len = fn_sig.inputs().skip_binder().len();
                if def.did() != def_id {
                    return None;
                }
                let name = item.name();
                let order = !name.as_str().starts_with("new");
                Some((order, name, input_len))
            })
            .collect::<Vec<_>>();
        items.sort_by_key(|(order, _, _)| *order);
        let suggestion = |name, args| {
            format!("::{name}({})", std::iter::repeat_n("_", args).collect::<Vec<_>>().join(", "))
        };
        match &items[..] {
            [] => {}
            [(_, name, len)] if *len == args.len() => {
                err.span_suggestion_verbose(
                    path_span.shrink_to_hi(),
                    format!("you might have meant to use the `{name}` associated function",),
                    format!("::{name}"),
                    Applicability::MaybeIncorrect,
                );
            }
            [(_, name, len)] => {
                err.span_suggestion_verbose(
                    path_span.shrink_to_hi().with_hi(call_span.hi()),
                    format!("you might have meant to use the `{name}` associated function",),
                    suggestion(name, *len),
                    Applicability::MaybeIncorrect,
                );
            }
            _ => {
                err.span_suggestions_with_style(
                    path_span.shrink_to_hi().with_hi(call_span.hi()),
                    "you might have meant to use an associated function to build this type",
                    items.iter().map(|(_, name, len)| suggestion(name, *len)),
                    Applicability::MaybeIncorrect,
                    SuggestionStyle::ShowAlways,
                );
            }
        }
        // We'd ideally use `type_implements_trait` but don't have access to
        // the trait solver here. We can't use `get_diagnostic_item` or
        // `all_traits` in resolve either. So instead we abuse the import
        // suggestion machinery to get `std::default::Default` and perform some
        // checks to confirm that we got *only* that trait. We then see if the
        // Adt we have has a direct implementation of `Default`. If so, we
        // provide a structured suggestion.
        let default_trait = self
            .r
            .lookup_import_candidates(
                Ident::with_dummy_span(sym::Default),
                Namespace::TypeNS,
                &self.parent_scope,
                &|res: Res| matches!(res, Res::Def(DefKind::Trait, _)),
            )
            .iter()
            .filter_map(|candidate| candidate.did)
            .find(|did| find_attr!(self.r.tcx, *did, RustcDiagnosticItem(sym::Default)));
        let Some(default_trait) = default_trait else {
            return;
        };
        if self
            .r
            .extern_crate_map
            .items()
            // NOTE: this doesn't include impls like `impl Default for String`.
            .flat_map(|(_, crate_)| self.r.tcx.implementations_of_trait((*crate_, default_trait)))
            .filter_map(|(_, simplified_self_ty)| *simplified_self_ty)
            .filter_map(|simplified_self_ty| match simplified_self_ty {
                SimplifiedType::Adt(did) => Some(did),
                _ => None,
            })
            .any(|did| did == def_id)
        {
            err.multipart_suggestion(
                "consider using the `Default` trait",
                vec![
                    (path_span.shrink_to_lo(), "<".to_string()),
                    (
                        path_span.shrink_to_hi().with_hi(call_span.hi()),
                        " as std::default::Default>::default()".to_string(),
                    ),
                ],
                Applicability::MaybeIncorrect,
            );
        }
    }

    fn has_private_fields(&self, def_id: DefId) -> bool {
        let fields = match def_id.as_local() {
            Some(def_id) => self.r.struct_constructors.get(&def_id).cloned().map(|(_, _, f)| f),
            None => Some(
                self.r
                    .tcx
                    .associated_item_def_ids(def_id)
                    .iter()
                    .map(|&field_id| self.r.tcx.visibility(field_id))
                    .collect(),
            ),
        };

        fields.is_some_and(|fields| {
            fields.iter().any(|vis| !self.r.is_accessible_from(*vis, self.parent_scope.module))
        })
    }

    /// Given the target `ident` and `kind`, search for the similarly named associated item
    /// in `self.current_trait_ref`.
    pub(crate) fn find_similarly_named_assoc_item(
        &mut self,
        ident: Symbol,
        kind: &AssocItemKind,
    ) -> Option<Symbol> {
        let (module, _) = self.current_trait_ref.as_ref()?;
        if ident == kw::Underscore {
            // We do nothing for `_`.
            return None;
        }

        let targets = self
            .r
            .resolutions(*module)
            .borrow()
            .iter()
            .filter_map(|(key, res)| res.borrow().best_decl().map(|binding| (key, binding.res())))
            .filter(|(_, res)| match (kind, res) {
                (AssocItemKind::Const(..), Res::Def(DefKind::AssocConst { .. }, _)) => true,
                (AssocItemKind::Fn(_), Res::Def(DefKind::AssocFn, _)) => true,
                (AssocItemKind::Type(..), Res::Def(DefKind::AssocTy, _)) => true,
                (AssocItemKind::Delegation(_), Res::Def(DefKind::AssocFn, _)) => true,
                _ => false,
            })
            .map(|(key, _)| key.ident.name)
            .collect::<Vec<_>>();

        find_best_match_for_name(&targets, ident, None)
    }

    fn lookup_assoc_candidate<FilterFn>(
        &mut self,
        ident: Ident,
        ns: Namespace,
        filter_fn: FilterFn,
        called: bool,
    ) -> Option<AssocSuggestion>
    where
        FilterFn: Fn(Res) -> bool,
    {
        fn extract_node_id(t: &Ty) -> Option<NodeId> {
            match t.kind {
                TyKind::Path(None, _) => Some(t.id),
                TyKind::Ref(_, ref mut_ty) => extract_node_id(&mut_ty.ty),
                // This doesn't handle the remaining `Ty` variants as they are not
                // that commonly the self_type, it might be interesting to provide
                // support for those in future.
                _ => None,
            }
        }
        // Fields are generally expected in the same contexts as locals.
        if filter_fn(Res::Local(ast::DUMMY_NODE_ID)) {
            if let Some(node_id) =
                self.diag_metadata.current_self_type.as_ref().and_then(extract_node_id)
                && let Some(resolution) = self.r.partial_res_map.get(&node_id)
                && let Some(Res::Def(DefKind::Struct | DefKind::Union, did)) = resolution.full_res()
                && let Some(fields) = self.r.field_idents(did)
                && let Some(field) = fields.iter().find(|id| ident.name == id.name)
            {
                // Look for a field with the same name in the current self_type.
                return Some(AssocSuggestion::Field(field.span));
            }
        }

        if let Some(items) = self.diag_metadata.current_trait_assoc_items {
            for assoc_item in items {
                if let Some(assoc_ident) = assoc_item.kind.ident()
                    && assoc_ident == ident
                {
                    return Some(match &assoc_item.kind {
                        ast::AssocItemKind::Const(..) => AssocSuggestion::AssocConst,
                        ast::AssocItemKind::Fn(box ast::Fn { sig, .. }) if sig.decl.has_self() => {
                            AssocSuggestion::MethodWithSelf { called }
                        }
                        ast::AssocItemKind::Fn(..) => AssocSuggestion::AssocFn { called },
                        ast::AssocItemKind::Type(..) => AssocSuggestion::AssocType,
                        ast::AssocItemKind::Delegation(..)
                            if self
                                .r
                                .delegation_fn_sigs
                                .get(&self.r.local_def_id(assoc_item.id))
                                .is_some_and(|sig| sig.has_self) =>
                        {
                            AssocSuggestion::MethodWithSelf { called }
                        }
                        ast::AssocItemKind::Delegation(..) => AssocSuggestion::AssocFn { called },
                        ast::AssocItemKind::MacCall(_) | ast::AssocItemKind::DelegationMac(..) => {
                            continue;
                        }
                    });
                }
            }
        }

        // Look for associated items in the current trait.
        if let Some((module, _)) = self.current_trait_ref
            && let Ok(binding) = self.r.cm().maybe_resolve_ident_in_module(
                ModuleOrUniformRoot::Module(module),
                ident,
                ns,
                &self.parent_scope,
                None,
            )
        {
            let res = binding.res();
            if filter_fn(res) {
                match res {
                    Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) => {
                        let has_self = match def_id.as_local() {
                            Some(def_id) => self
                                .r
                                .delegation_fn_sigs
                                .get(&def_id)
                                .is_some_and(|sig| sig.has_self),
                            None => {
                                self.r.tcx.fn_arg_idents(def_id).first().is_some_and(|&ident| {
                                    matches!(ident, Some(Ident { name: kw::SelfLower, .. }))
                                })
                            }
                        };
                        if has_self {
                            return Some(AssocSuggestion::MethodWithSelf { called });
                        } else {
                            return Some(AssocSuggestion::AssocFn { called });
                        }
                    }
                    Res::Def(DefKind::AssocConst { .. }, _) => {
                        return Some(AssocSuggestion::AssocConst);
                    }
                    Res::Def(DefKind::AssocTy, _) => {
                        return Some(AssocSuggestion::AssocType);
                    }
                    _ => {}
                }
            }
        }

        None
    }

    fn lookup_typo_candidate(
        &mut self,
        path: &[Segment],
        following_seg: Option<&Segment>,
        ns: Namespace,
        filter_fn: &impl Fn(Res) -> bool,
    ) -> TypoCandidate {
        let mut names = Vec::new();
        if let [segment] = path {
            let mut ctxt = segment.ident.span.ctxt();

            // Search in lexical scope.
            // Walk backwards up the ribs in scope and collect candidates.
            for rib in self.ribs[ns].iter().rev() {
                let rib_ctxt = if rib.kind.contains_params() {
                    ctxt.normalize_to_macros_2_0()
                } else {
                    ctxt.normalize_to_macro_rules()
                };

                // Locals and type parameters
                for (ident, &res) in &rib.bindings {
                    if filter_fn(res) && ident.span.ctxt() == rib_ctxt {
                        names.push(TypoSuggestion::new(ident.name, ident.span, res));
                    }
                }

                if let RibKind::Block(Some(module)) = rib.kind {
                    self.r.add_module_candidates(module, &mut names, &filter_fn, Some(ctxt));
                } else if let RibKind::Module(module) = rib.kind {
                    // Encountered a module item, abandon ribs and look into that module and preludes.
                    let parent_scope = &ParentScope { module, ..self.parent_scope };
                    self.r.add_scope_set_candidates(
                        &mut names,
                        ScopeSet::All(ns),
                        parent_scope,
                        segment.ident.span.with_ctxt(ctxt),
                        filter_fn,
                    );
                    break;
                }

                if let RibKind::MacroDefinition(def) = rib.kind
                    && def == self.r.macro_def(ctxt)
                {
                    // If an invocation of this macro created `ident`, give up on `ident`
                    // and switch to `ident`'s source from the macro definition.
                    ctxt.remove_mark();
                }
            }
        } else {
            // Search in module.
            let mod_path = &path[..path.len() - 1];
            if let PathResult::Module(ModuleOrUniformRoot::Module(module)) =
                self.resolve_path(mod_path, Some(TypeNS), None, PathSource::Type)
            {
                self.r.add_module_candidates(module, &mut names, &filter_fn, None);
            }
        }

        // if next_seg is present, let's filter everything that does not continue the path
        if let Some(following_seg) = following_seg {
            names.retain(|suggestion| match suggestion.res {
                Res::Def(DefKind::Struct | DefKind::Enum | DefKind::Union, _) => {
                    // NOTE: this is not totally accurate, but mostly works
                    suggestion.candidate != following_seg.ident.name
                }
                Res::Def(DefKind::Mod, def_id) => {
                    let module = self.r.expect_module(def_id);
                    self.r
                        .resolutions(module)
                        .borrow()
                        .iter()
                        .any(|(key, _)| key.ident.name == following_seg.ident.name)
                }
                _ => true,
            });
        }
        let name = path[path.len() - 1].ident.name;
        // Make sure error reporting is deterministic.
        names.sort_by(|a, b| a.candidate.as_str().cmp(b.candidate.as_str()));

        match find_best_match_for_name(
            &names.iter().map(|suggestion| suggestion.candidate).collect::<Vec<Symbol>>(),
            name,
            None,
        ) {
            Some(found) => {
                let Some(sugg) = names.into_iter().find(|suggestion| suggestion.candidate == found)
                else {
                    return TypoCandidate::None;
                };
                if found == name {
                    TypoCandidate::Shadowed(sugg.res, sugg.span)
                } else {
                    TypoCandidate::Typo(sugg)
                }
            }
            _ => TypoCandidate::None,
        }
    }

    // Returns the name of the Rust type approximately corresponding to
    // a type name in another programming language.
    fn likely_rust_type(path: &[Segment]) -> Option<Symbol> {
        let name = path[path.len() - 1].ident.as_str();
        // Common Java types
        Some(match name {
            "byte" => sym::u8, // In Java, bytes are signed, but in practice one almost always wants unsigned bytes.
            "short" => sym::i16,
            "Bool" => sym::bool,
            "Boolean" => sym::bool,
            "boolean" => sym::bool,
            "int" => sym::i32,
            "long" => sym::i64,
            "float" => sym::f32,
            "double" => sym::f64,
            _ => return None,
        })
    }

    // try to give a suggestion for this pattern: `name = blah`, which is common in other languages
    // suggest `let name = blah` to introduce a new binding
    fn let_binding_suggestion(&self, err: &mut Diag<'_>, ident_span: Span) -> bool {
        if ident_span.from_expansion() {
            return false;
        }

        // only suggest when the code is a assignment without prefix code
        if let Some(Expr { kind: ExprKind::Assign(lhs, ..), .. }) = self.diag_metadata.in_assignment
            && let ast::ExprKind::Path(None, ref path) = lhs.kind
            && self.r.tcx.sess.source_map().is_line_before_span_empty(ident_span)
        {
            let (span, text) = match path.segments.first() {
                Some(seg) if let Some(name) = seg.ident.as_str().strip_prefix("let") => {
                    // a special case for #117894
                    let name = name.trim_prefix('_');
                    (ident_span, format!("let {name}"))
                }
                _ => (ident_span.shrink_to_lo(), "let ".to_string()),
            };

            err.span_suggestion_verbose(
                span,
                "you might have meant to introduce a new binding",
                text,
                Applicability::MaybeIncorrect,
            );
            return true;
        }

        // a special case for #133713
        // '=' maybe a typo of `:`, which is a type annotation instead of assignment
        if err.code == Some(E0423)
            && let Some((let_span, None, Some(val_span))) = self.diag_metadata.current_let_binding
            && val_span.contains(ident_span)
            && val_span.lo() == ident_span.lo()
        {
            err.span_suggestion_verbose(
                let_span.shrink_to_hi().to(val_span.shrink_to_lo()),
                "you might have meant to use `:` for type annotation",
                ": ",
                Applicability::MaybeIncorrect,
            );
            return true;
        }
        false
    }

    fn find_module(&self, def_id: DefId) -> Option<(Module<'ra>, ImportSuggestion)> {
        let mut result = None;
        let mut seen_modules = FxHashSet::default();
        let root_did = self.r.graph_root.def_id();
        let mut worklist = vec![(
            self.r.graph_root,
            ThinVec::new(),
            root_did.is_local() || !self.r.tcx.is_doc_hidden(root_did),
        )];

        while let Some((in_module, path_segments, doc_visible)) = worklist.pop() {
            // abort if the module is already found
            if result.is_some() {
                break;
            }

            in_module.for_each_child(self.r, |r, ident, orig_ident_span, _, name_binding| {
                // abort if the module is already found or if name_binding is private external
                if result.is_some() || !name_binding.vis().is_visible_locally() {
                    return;
                }
                if let Some(module_def_id) = name_binding.res().module_like_def_id() {
                    // form the path
                    let mut path_segments = path_segments.clone();
                    path_segments.push(ast::PathSegment::from_ident(ident.orig(orig_ident_span)));
                    let doc_visible = doc_visible
                        && (module_def_id.is_local() || !r.tcx.is_doc_hidden(module_def_id));
                    if module_def_id == def_id {
                        let path =
                            Path { span: name_binding.span, segments: path_segments, tokens: None };
                        result = Some((
                            r.expect_module(module_def_id),
                            ImportSuggestion {
                                did: Some(def_id),
                                descr: "module",
                                path,
                                accessible: true,
                                doc_visible,
                                note: None,
                                via_import: false,
                                is_stable: true,
                            },
                        ));
                    } else {
                        // add the module to the lookup
                        if seen_modules.insert(module_def_id) {
                            let module = r.expect_module(module_def_id);
                            worklist.push((module, path_segments, doc_visible));
                        }
                    }
                }
            });
        }

        result
    }

    fn collect_enum_ctors(&self, def_id: DefId) -> Option<Vec<(Path, DefId, CtorKind)>> {
        self.find_module(def_id).map(|(enum_module, enum_import_suggestion)| {
            let mut variants = Vec::new();
            enum_module.for_each_child(self.r, |_, ident, orig_ident_span, _, name_binding| {
                if let Res::Def(DefKind::Ctor(CtorOf::Variant, kind), def_id) = name_binding.res() {
                    let mut segms = enum_import_suggestion.path.segments.clone();
                    segms.push(ast::PathSegment::from_ident(ident.orig(orig_ident_span)));
                    let path = Path { span: name_binding.span, segments: segms, tokens: None };
                    variants.push((path, def_id, kind));
                }
            });
            variants
        })
    }

    /// Adds a suggestion for using an enum's variant when an enum is used instead.
    fn suggest_using_enum_variant(
        &self,
        err: &mut Diag<'_>,
        source: PathSource<'_, '_, '_>,
        def_id: DefId,
        span: Span,
    ) {
        let Some(variant_ctors) = self.collect_enum_ctors(def_id) else {
            err.note("you might have meant to use one of the enum's variants");
            return;
        };

        // If the expression is a field-access or method-call, try to find a variant with the field/method name
        // that could have been intended, and suggest replacing the `.` with `::`.
        // Otherwise, suggest adding `::VariantName` after the enum;
        // and if the expression is call-like, only suggest tuple variants.
        let (suggest_path_sep_dot_span, suggest_only_tuple_variants) = match source {
            // `Type(a, b)` in a pattern, only suggest adding a tuple variant after `Type`.
            PathSource::TupleStruct(..) => (None, true),
            PathSource::Expr(Some(expr)) => match &expr.kind {
                // `Type(a, b)`, only suggest adding a tuple variant after `Type`.
                ExprKind::Call(..) => (None, true),
                // `Type.Foo(a, b)`, suggest replacing `.` -> `::` if variant `Foo` exists and is a tuple variant,
                // otherwise suggest adding a variant after `Type`.
                ExprKind::MethodCall(box MethodCall {
                    receiver,
                    span,
                    seg: PathSegment { ident, .. },
                    ..
                }) => {
                    let dot_span = receiver.span.between(*span);
                    let found_tuple_variant = variant_ctors.iter().any(|(path, _, ctor_kind)| {
                        *ctor_kind == CtorKind::Fn
                            && path.segments.last().is_some_and(|seg| seg.ident == *ident)
                    });
                    (found_tuple_variant.then_some(dot_span), false)
                }
                // `Type.Foo`, suggest replacing `.` -> `::` if variant `Foo` exists and is a unit or tuple variant,
                // otherwise suggest adding a variant after `Type`.
                ExprKind::Field(base, ident) => {
                    let dot_span = base.span.between(ident.span);
                    let found_tuple_or_unit_variant = variant_ctors.iter().any(|(path, ..)| {
                        path.segments.last().is_some_and(|seg| seg.ident == *ident)
                    });
                    (found_tuple_or_unit_variant.then_some(dot_span), false)
                }
                _ => (None, false),
            },
            _ => (None, false),
        };

        if let Some(dot_span) = suggest_path_sep_dot_span {
            err.span_suggestion_verbose(
                dot_span,
                "use the path separator to refer to a variant",
                "::",
                Applicability::MaybeIncorrect,
            );
        } else if suggest_only_tuple_variants {
            // Suggest only tuple variants regardless of whether they have fields and do not
            // suggest path with added parentheses.
            let mut suggestable_variants = variant_ctors
                .iter()
                .filter(|(.., kind)| *kind == CtorKind::Fn)
                .map(|(variant, ..)| path_names_to_string(variant))
                .collect::<Vec<_>>();
            suggestable_variants.sort();

            let non_suggestable_variant_count = variant_ctors.len() - suggestable_variants.len();

            let source_msg = if matches!(source, PathSource::TupleStruct(..)) {
                "to match against"
            } else {
                "to construct"
            };

            if !suggestable_variants.is_empty() {
                let msg = if non_suggestable_variant_count == 0 && suggestable_variants.len() == 1 {
                    format!("try {source_msg} the enum's variant")
                } else {
                    format!("try {source_msg} one of the enum's variants")
                };

                err.span_suggestions(
                    span,
                    msg,
                    suggestable_variants,
                    Applicability::MaybeIncorrect,
                );
            }

            // If the enum has no tuple variants..
            if non_suggestable_variant_count == variant_ctors.len() {
                err.help(format!("the enum has no tuple variants {source_msg}"));
            }

            // If there are also non-tuple variants..
            if non_suggestable_variant_count == 1 {
                err.help(format!("you might have meant {source_msg} the enum's non-tuple variant"));
            } else if non_suggestable_variant_count >= 1 {
                err.help(format!(
                    "you might have meant {source_msg} one of the enum's non-tuple variants"
                ));
            }
        } else {
            let needs_placeholder = |ctor_def_id: DefId, kind: CtorKind| {
                let def_id = self.r.tcx.parent(ctor_def_id);
                match kind {
                    CtorKind::Const => false,
                    CtorKind::Fn => {
                        !self.r.field_idents(def_id).is_some_and(|field_ids| field_ids.is_empty())
                    }
                }
            };

            let mut suggestable_variants = variant_ctors
                .iter()
                .filter(|(_, def_id, kind)| !needs_placeholder(*def_id, *kind))
                .map(|(variant, _, kind)| (path_names_to_string(variant), kind))
                .map(|(variant, kind)| match kind {
                    CtorKind::Const => variant,
                    CtorKind::Fn => format!("({variant}())"),
                })
                .collect::<Vec<_>>();
            suggestable_variants.sort();
            let no_suggestable_variant = suggestable_variants.is_empty();

            if !no_suggestable_variant {
                let msg = if suggestable_variants.len() == 1 {
                    "you might have meant to use the following enum variant"
                } else {
                    "you might have meant to use one of the following enum variants"
                };

                err.span_suggestions(
                    span,
                    msg,
                    suggestable_variants,
                    Applicability::MaybeIncorrect,
                );
            }

            let mut suggestable_variants_with_placeholders = variant_ctors
                .iter()
                .filter(|(_, def_id, kind)| needs_placeholder(*def_id, *kind))
                .map(|(variant, _, kind)| (path_names_to_string(variant), kind))
                .filter_map(|(variant, kind)| match kind {
                    CtorKind::Fn => Some(format!("({variant}(/* fields */))")),
                    _ => None,
                })
                .collect::<Vec<_>>();
            suggestable_variants_with_placeholders.sort();

            if !suggestable_variants_with_placeholders.is_empty() {
                let msg =
                    match (no_suggestable_variant, suggestable_variants_with_placeholders.len()) {
                        (true, 1) => "the following enum variant is available",
                        (true, _) => "the following enum variants are available",
                        (false, 1) => "alternatively, the following enum variant is available",
                        (false, _) => {
                            "alternatively, the following enum variants are also available"
                        }
                    };

                err.span_suggestions(
                    span,
                    msg,
                    suggestable_variants_with_placeholders,
                    Applicability::HasPlaceholders,
                );
            }
        };

        if def_id.is_local() {
            err.span_note(self.r.def_span(def_id), "the enum is defined here");
        }
    }

    /// Detects missing const parameters in `impl` blocks and suggests adding them.
    ///
    /// When a const parameter is used in the self type of an `impl` but not declared
    /// in the `impl`'s own generic parameter list, this function emits a targeted
    /// diagnostic with a suggestion to add it at the correct position.
    ///
    /// Example:
    ///
    /// ```rust,ignore (suggested field is not completely correct, it should be a single suggestion)
    /// struct C<const A: u8, const X: u8, const P: u32>;
    ///
    /// impl Foo for C<A, X, P> {}
    /// //           ^ the struct `C` in `C<A, X, P>` is used as the self type
    /// //             ^ ^ ^ but A, X and P are not declared on the impl
    ///
    /// Suggested fix:
    ///
    /// impl<const A: u8, const X: u8, const P: u32> Foo for C<A, X, P> {}
    ///
    /// Current behavior (suggestions are emitted one-by-one):
    ///
    /// impl<const A: u8> Foo for C<A, X, P> {}
    /// impl<const X: u8> Foo for C<A, X, P> {}
    /// impl<const P: u32> Foo for C<A, X, P> {}
    ///
    /// Ideally the suggestion should aggregate them into a single line:
    ///
    /// impl<const A: u8, const X: u8, const P: u32> Foo for C<A, X, P> {}
    /// ```
    ///
}
