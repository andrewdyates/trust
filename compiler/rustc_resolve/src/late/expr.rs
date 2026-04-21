// tRust: Split from late.rs -- expression, block, and const resolution methods.
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
    fn with_resolved_label(&mut self, label: Option<Label>, id: NodeId, f: impl FnOnce(&mut Self)) {
        if let Some(label) = label {
            if label.ident.as_str().as_bytes()[1] != b'_' {
                self.diag_metadata.unused_labels.insert(id, label.ident.span);
            }

            if let Ok((_, orig_span)) = self.resolve_label(label.ident) {
                diagnostics::signal_label_shadowing(self.r.tcx.sess, orig_span, label.ident)
            }

            self.with_label_rib(RibKind::Normal, |this| {
                let ident = label.ident.normalize_to_macro_rules();
                this.label_ribs.last_mut().expect("invariant: value is present").bindings.insert(ident, id);
                f(this);
            });
        } else {
            f(self);
        }
    }

    fn resolve_labeled_block(&mut self, label: Option<Label>, id: NodeId, block: &'ast Block) {
        self.with_resolved_label(label, id, |this| this.visit_block(block));
    }

    fn resolve_block(&mut self, block: &'ast Block) {
        debug!("(resolving block) entering block");
        // Move down in the graph, if there's an anonymous module rooted here.
        let orig_module = self.parent_scope.module;
        let anonymous_module = self.r.block_map.get(&block.id).copied();

        let mut num_macro_definition_ribs = 0;
        if let Some(anonymous_module) = anonymous_module {
            debug!("(resolving block) found anonymous module, moving down");
            self.ribs[ValueNS].push(Rib::new(RibKind::Block(Some(anonymous_module))));
            self.ribs[TypeNS].push(Rib::new(RibKind::Block(Some(anonymous_module))));
            self.parent_scope.module = anonymous_module;
        } else {
            self.ribs[ValueNS].push(Rib::new(RibKind::Block(None)));
        }

        // Descend into the block.
        for stmt in &block.stmts {
            if let StmtKind::Item(ref item) = stmt.kind
                && let ItemKind::MacroDef(..) = item.kind
            {
                num_macro_definition_ribs += 1;
                let res = self.r.local_def_id(item.id).to_def_id();
                self.ribs[ValueNS].push(Rib::new(RibKind::MacroDefinition(res)));
                self.label_ribs.push(Rib::new(RibKind::MacroDefinition(res)));
            }

            self.visit_stmt(stmt);
        }

        // Move back up.
        self.parent_scope.module = orig_module;
        for _ in 0..num_macro_definition_ribs {
            self.ribs[ValueNS].pop();
            self.label_ribs.pop();
        }
        self.last_block_rib = self.ribs[ValueNS].pop();
        if anonymous_module.is_some() {
            self.ribs[TypeNS].pop();
        }
        debug!("(resolving block) leaving block");
    }

    fn resolve_anon_const(&mut self, constant: &'ast AnonConst, anon_const_kind: AnonConstKind) {
        debug!(
            "resolve_anon_const(constant: {:?}, anon_const_kind: {:?})",
            constant, anon_const_kind
        );

        let is_trivial_const_arg = constant.value.is_potential_trivial_const_arg();
        self.resolve_anon_const_manual(is_trivial_const_arg, anon_const_kind, |this| {
            this.resolve_expr(&constant.value, None)
        })
    }

    /// There are a few places that we need to resolve an anon const but we did not parse an
    /// anon const so cannot provide an `&'ast AnonConst`. Right now this is just unbraced
    /// const arguments that were parsed as type arguments, and `legacy_const_generics` which
    /// parse as normal function argument expressions. To avoid duplicating the code for resolving
    /// an anon const we have this function which lets the caller manually call `resolve_expr` or
    /// `smart_resolve_path`.
    fn resolve_anon_const_manual(
        &mut self,
        is_trivial_const_arg: bool,
        anon_const_kind: AnonConstKind,
        resolve_expr: impl FnOnce(&mut Self),
    ) {
        let is_repeat_expr = match anon_const_kind {
            AnonConstKind::ConstArg(is_repeat_expr) => is_repeat_expr,
            _ => IsRepeatExpr::No,
        };

        let may_use_generics = match anon_const_kind {
            AnonConstKind::EnumDiscriminant => {
                ConstantHasGenerics::No(NoConstantGenericsReason::IsEnumDiscriminant)
            }
            AnonConstKind::FieldDefaultValue => ConstantHasGenerics::Yes,
            AnonConstKind::InlineConst => ConstantHasGenerics::Yes,
            AnonConstKind::ConstArg(_) => {
                if self.r.tcx.features().generic_const_exprs()
                    || self.r.tcx.features().min_generic_const_args()
                    || is_trivial_const_arg
                {
                    ConstantHasGenerics::Yes
                } else {
                    ConstantHasGenerics::No(NoConstantGenericsReason::NonTrivialConstArg)
                }
            }
        };

        self.with_constant_rib(is_repeat_expr, may_use_generics, None, |this| {
            this.with_lifetime_rib(LifetimeRibKind::Elided(LifetimeRes::Infer), |this| {
                resolve_expr(this);
            });
        });
    }

    fn resolve_expr_field(&mut self, f: &'ast ExprField, e: &'ast Expr) {
        self.resolve_expr(&f.expr, Some(e));
        self.visit_ident(&f.ident);
        walk_list!(self, visit_attribute, f.attrs.iter());
    }

    fn resolve_expr(&mut self, expr: &'ast Expr, parent: Option<&'ast Expr>) {
        // First, record candidate traits for this expression if it could
        // result in the invocation of a method call.

        self.record_candidate_traits_for_expr_if_necessary(expr);

        // Next, resolve the node.
        match expr.kind {
            ExprKind::Path(ref qself, ref path) => {
                self.smart_resolve_path(expr.id, qself, path, PathSource::Expr(parent));
                visit::walk_expr(self, expr);
            }

            ExprKind::Struct(ref se) => {
                self.smart_resolve_path(expr.id, &se.qself, &se.path, PathSource::Struct(parent));
                // This is the same as `visit::walk_expr(self, expr);`, but we want to pass the
                // parent in for accurate suggestions when encountering `Foo { bar }` that should
                // have been `Foo { bar: self.bar }`.
                if let Some(qself) = &se.qself {
                    self.visit_ty(&qself.ty);
                }
                self.visit_path(&se.path);
                walk_list!(self, resolve_expr_field, &se.fields, expr);
                match &se.rest {
                    StructRest::Base(expr) => self.visit_expr(expr),
                    StructRest::Rest(_span) => {}
                    StructRest::None | StructRest::NoneWithError(_) => {}
                }
            }

            ExprKind::Break(Some(label), _) | ExprKind::Continue(Some(label)) => {
                match self.resolve_label(label.ident) {
                    Ok((node_id, _)) => {
                        // Since this res is a label, it is never read.
                        self.r.label_res_map.insert(expr.id, node_id);
                        self.diag_metadata.unused_labels.swap_remove(&node_id);
                    }
                    Err(error) => {
                        self.report_error(label.ident.span, error);
                    }
                }

                // visit `break` argument if any
                visit::walk_expr(self, expr);
            }

            ExprKind::Break(None, Some(ref e)) => {
                // We use this instead of `visit::walk_expr` to keep the parent expr around for
                // better diagnostics.
                self.resolve_expr(e, Some(expr));
            }

            ExprKind::Let(ref pat, ref scrutinee, _, Recovered::No) => {
                self.visit_expr(scrutinee);
                self.resolve_pattern_top(pat, PatternSource::Let);
            }

            ExprKind::Let(ref pat, ref scrutinee, _, Recovered::Yes(_)) => {
                self.visit_expr(scrutinee);
                // This is basically a tweaked, inlined `resolve_pattern_top`.
                let mut bindings = smallvec![(PatBoundCtx::Product, Default::default())];
                self.resolve_pattern(pat, PatternSource::Let, &mut bindings);
                // We still collect the bindings in this `let` expression which is in
                // an invalid position (and therefore shouldn't declare variables into
                // its parent scope). To avoid unnecessary errors though, we do just
                // reassign the resolutions to `Res::Err`.
                for (_, bindings) in &mut bindings {
                    for (_, binding) in bindings {
                        *binding = Res::Err;
                    }
                }
                self.apply_pattern_bindings(bindings);
            }

            ExprKind::If(ref cond, ref then, ref opt_else) => {
                self.with_rib(ValueNS, RibKind::Normal, |this| {
                    let old = this.diag_metadata.in_if_condition.replace(cond);
                    this.visit_expr(cond);
                    this.diag_metadata.in_if_condition = old;
                    this.visit_block(then);
                });
                if let Some(expr) = opt_else {
                    self.visit_expr(expr);
                }
            }

            ExprKind::Loop(ref block, label, _) => {
                self.resolve_labeled_block(label, expr.id, block)
            }

            ExprKind::While(ref cond, ref block, label) => {
                self.with_resolved_label(label, expr.id, |this| {
                    this.with_rib(ValueNS, RibKind::Normal, |this| {
                        let old = this.diag_metadata.in_if_condition.replace(cond);
                        this.visit_expr(cond);
                        this.diag_metadata.in_if_condition = old;
                        this.visit_block(block);
                    })
                });
            }

            ExprKind::ForLoop { ref pat, ref iter, ref body, label, kind: _ } => {
                self.visit_expr(iter);
                self.with_rib(ValueNS, RibKind::Normal, |this| {
                    this.resolve_pattern_top(pat, PatternSource::For);
                    this.resolve_labeled_block(label, expr.id, body);
                });
            }

            ExprKind::Block(ref block, label) => self.resolve_labeled_block(label, block.id, block),

            // Equivalent to `visit::walk_expr` + passing some context to children.
            ExprKind::Field(ref subexpression, _) => {
                self.resolve_expr(subexpression, Some(expr));
            }
            ExprKind::MethodCall(box MethodCall { ref seg, ref receiver, ref args, .. }) => {
                self.resolve_expr(receiver, Some(expr));
                for arg in args {
                    self.resolve_expr(arg, None);
                }
                self.visit_path_segment(seg);
            }

            ExprKind::Call(ref callee, ref arguments) => {
                self.resolve_expr(callee, Some(expr));
                let const_args = self.r.legacy_const_generic_args(callee).unwrap_or_default();
                for (idx, argument) in arguments.iter().enumerate() {
                    // Constant arguments need to be treated as AnonConst since
                    // that is how they will be later lowered to HIR.
                    if const_args.contains(&idx) {
                        // NOTE(mgca): legacy const generics doesn't support mgca but maybe
                        // that's okay.
                        let is_trivial_const_arg = argument.is_potential_trivial_const_arg();
                        self.resolve_anon_const_manual(
                            is_trivial_const_arg,
                            AnonConstKind::ConstArg(IsRepeatExpr::No),
                            |this| this.resolve_expr(argument, None),
                        );
                    } else {
                        self.resolve_expr(argument, None);
                    }
                }
            }
            ExprKind::Type(ref _type_expr, ref _ty) => {
                visit::walk_expr(self, expr);
            }
            // For closures, RibKind::FnOrCoroutine is added in visit_fn
            ExprKind::Closure(box ast::Closure {
                binder: ClosureBinder::For { ref generic_params, span },
                ..
            }) => {
                self.with_generic_param_rib(
                    generic_params,
                    RibKind::Normal,
                    expr.id,
                    LifetimeBinderKind::Closure,
                    span,
                    |this| visit::walk_expr(this, expr),
                );
            }
            ExprKind::Closure(..) => visit::walk_expr(self, expr),
            ExprKind::Gen(..) => {
                self.with_label_rib(RibKind::FnOrCoroutine, |this| visit::walk_expr(this, expr));
            }
            ExprKind::Repeat(ref elem, ref ct) => {
                self.visit_expr(elem);
                self.resolve_anon_const(ct, AnonConstKind::ConstArg(IsRepeatExpr::Yes));
            }
            ExprKind::ConstBlock(ref ct) => {
                self.resolve_anon_const(ct, AnonConstKind::InlineConst);
            }
            ExprKind::Index(ref elem, ref idx, _) => {
                self.resolve_expr(elem, Some(expr));
                self.visit_expr(idx);
            }
            ExprKind::Assign(ref lhs, ref rhs, _) => {
                if !self.diag_metadata.is_assign_rhs {
                    self.diag_metadata.in_assignment = Some(expr);
                }
                self.visit_expr(lhs);
                self.diag_metadata.is_assign_rhs = true;
                self.diag_metadata.in_assignment = None;
                self.visit_expr(rhs);
                self.diag_metadata.is_assign_rhs = false;
            }
            ExprKind::Range(Some(ref start), Some(ref end), RangeLimits::HalfOpen) => {
                self.diag_metadata.in_range = Some((start, end));
                self.resolve_expr(start, Some(expr));
                self.resolve_expr(end, Some(expr));
                self.diag_metadata.in_range = None;
            }
            _ => {
                visit::walk_expr(self, expr);
            }
        }
    }

    fn record_candidate_traits_for_expr_if_necessary(&mut self, expr: &'ast Expr) {
        match expr.kind {
            ExprKind::Field(_, ident) => {
                // #6890: Even though you can't treat a method like a field,
                // we need to add any trait methods we find that match the
                // field name so that we can do some nice error reporting
                // later on in typeck.
                let traits = self.traits_in_scope(ident, ValueNS);
                self.r.trait_map.insert(expr.id, traits);
            }
            ExprKind::MethodCall(ref call) => {
                debug!("(recording candidate traits for expr) recording traits for {}", expr.id);
                let traits = self.traits_in_scope(call.seg.ident, ValueNS);
                self.r.trait_map.insert(expr.id, traits);
            }
            _ => {
                // Nothing to do.
            }
        }
    }

    fn traits_in_scope(&mut self, ident: Ident, ns: Namespace) -> &'tcx [TraitCandidate<'tcx>] {
        self.r.traits_in_scope(
            self.current_trait_ref.as_ref().map(|(module, _)| *module),
            &self.parent_scope,
            ident.span,
            Some((ident.name, ns)),
        )
    }

    fn resolve_and_cache_rustdoc_path(&mut self, path_str: &str, ns: Namespace) -> Option<Res> {
        // NOTE: this caching may be incorrect in case of multiple `macro_rules`
        // items with the same name in the same module.
        // Also hygiene is not considered.
        let mut doc_link_resolutions = std::mem::take(&mut self.r.doc_link_resolutions);
        let res = *doc_link_resolutions
            .entry(self.parent_scope.module.nearest_parent_mod().expect_local())
            .or_default()
            .entry((Symbol::intern(path_str), ns))
            .or_insert_with_key(|(path, ns)| {
                let res = self.r.resolve_rustdoc_path(path.as_str(), *ns, self.parent_scope);
                if let Some(res) = res
                    && let Some(def_id) = res.opt_def_id()
                    && self.is_invalid_proc_macro_item_for_doc(def_id)
                {
                    // Encoding def ids in proc macro crate metadata will ICE,
                    // because it will only store proc macros for it.
                    return None;
                }
                res
            });
        self.r.doc_link_resolutions = doc_link_resolutions;
        res
    }

    fn is_invalid_proc_macro_item_for_doc(&self, did: DefId) -> bool {
        if !matches!(self.r.tcx.sess.opts.resolve_doc_links, ResolveDocLinks::ExportedMetadata)
            || !self.r.tcx.crate_types().contains(&CrateType::ProcMacro)
        {
            return false;
        }
        let Some(local_did) = did.as_local() else { return true };
        !self.r.proc_macros.contains(&local_did)
    }

    fn resolve_doc_links(&mut self, attrs: &[Attribute], maybe_exported: MaybeExported<'_>) {
        match self.r.tcx.sess.opts.resolve_doc_links {
            ResolveDocLinks::None => return,
            ResolveDocLinks::ExportedMetadata
                if !self.r.tcx.crate_types().iter().copied().any(CrateType::has_metadata)
                    || !maybe_exported.eval(self.r) =>
            {
                return;
            }
            ResolveDocLinks::Exported
                if !maybe_exported.eval(self.r)
                    && !rustdoc::has_primitive_or_keyword_or_attribute_docs(attrs) =>
            {
                return;
            }
            ResolveDocLinks::ExportedMetadata
            | ResolveDocLinks::Exported
            | ResolveDocLinks::All => {}
        }

        if !attrs.iter().any(|attr| attr.may_have_doc_links()) {
            return;
        }

        let mut need_traits_in_scope = false;
        for path_str in rustdoc::attrs_to_preprocessed_links(attrs) {
            // Resolve all namespaces due to no disambiguator or for diagnostics.
            let mut any_resolved = false;
            let mut need_assoc = false;
            for ns in [TypeNS, ValueNS, MacroNS] {
                if let Some(res) = self.resolve_and_cache_rustdoc_path(&path_str, ns) {
                    // Rustdoc ignores tool attribute resolutions and attempts
                    // to resolve their prefixes for diagnostics.
                    any_resolved = !matches!(res, Res::NonMacroAttr(NonMacroAttrKind::Tool));
                } else if ns != MacroNS {
                    need_assoc = true;
                }
            }

            // Resolve all prefixes for type-relative resolution or for diagnostics.
            if need_assoc || !any_resolved {
                let mut path = &path_str[..];
                while let Some(idx) = path.rfind("::") {
                    path = &path[..idx];
                    need_traits_in_scope = true;
                    for ns in [TypeNS, ValueNS, MacroNS] {
                        self.resolve_and_cache_rustdoc_path(path, ns);
                    }
                }
            }
        }

        if need_traits_in_scope {
            // NOTE: hygiene is not considered.
            let mut doc_link_traits_in_scope = std::mem::take(&mut self.r.doc_link_traits_in_scope);
            doc_link_traits_in_scope
                .entry(self.parent_scope.module.nearest_parent_mod().expect_local())
                .or_insert_with(|| {
                    self.r
                        .traits_in_scope(None, &self.parent_scope, DUMMY_SP, None)
                        .into_iter()
                        .filter_map(|tr| {
                            if self.is_invalid_proc_macro_item_for_doc(tr.def_id) {
                                // Encoding def ids in proc macro crate metadata will ICE.
                                // because it will only store proc macros for it.
                                return None;
                            }
                            Some(tr.def_id)
                        })
                        .collect()
                });
            self.r.doc_link_traits_in_scope = doc_link_traits_in_scope;
        }
    }

    fn lint_unused_qualifications(&mut self, path: &[Segment], ns: Namespace, finalize: Finalize) {
        // Don't lint on global paths because the user explicitly wrote out the full path.
        if let Some(seg) = path.first()
            && seg.ident.name == kw::PathRoot
        {
            return;
        }

        if finalize.path_span.from_expansion()
            || path.iter().any(|seg| seg.ident.span.from_expansion())
        {
            return;
        }

        let end_pos =
            path.iter().position(|seg| seg.has_generic_args).map_or(path.len(), |pos| pos + 1);
        let unqualified = path[..end_pos].iter().enumerate().skip(1).rev().find_map(|(i, seg)| {
            // Preserve the current namespace for the final path segment, but use the type
            // namespace for all preceding segments
            //
            // e.g. for `std::env::args` check the `ValueNS` for `args` but the `TypeNS` for
            // `std` and `env`
            //
            // If the final path segment is beyond `end_pos` all the segments to check will
            // use the type namespace
            let ns = if i + 1 == path.len() { ns } else { TypeNS };
            let res = self.r.partial_res_map.get(&seg.id?)?.full_res()?;
            let binding = self.resolve_ident_in_lexical_scope(seg.ident, ns, None, None)?;
            (res == binding.res()).then_some((seg, binding))
        });

        if let Some((seg, decl)) = unqualified {
            self.r.potentially_unnecessary_qualifications.push(UnnecessaryQualification {
                decl,
                node_id: finalize.node_id,
                path_span: finalize.path_span,
                removal_span: path[0].ident.span.until(seg.ident.span),
            });
        }
    }

    fn resolve_define_opaques(&mut self, define_opaque: &Option<ThinVec<(NodeId, Path)>>) {
        if let Some(define_opaque) = define_opaque {
            for (id, path) in define_opaque {
                self.smart_resolve_path(*id, &None, path, PathSource::DefineOpaques);
            }
        }
    }
}

}
