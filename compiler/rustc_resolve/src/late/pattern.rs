// tRust: Split from late.rs -- pattern resolution methods.
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
    fn resolve_params(&mut self, params: &'ast [Param]) {
        let mut bindings = smallvec![(PatBoundCtx::Product, Default::default())];
        self.with_lifetime_rib(LifetimeRibKind::Elided(LifetimeRes::Infer), |this| {
            for Param { pat, .. } in params {
                this.resolve_pattern(pat, PatternSource::FnParam, &mut bindings);
            }
            this.apply_pattern_bindings(bindings);
        });
        for Param { ty, .. } in params {
            self.visit_ty(ty);
        }
    }

    fn resolve_local(&mut self, local: &'ast Local) {
        debug!("resolving local ({:?})", local);
        // Resolve the type.
        visit_opt!(self, visit_ty, &local.ty);

        // Resolve the initializer.
        if let Some((init, els)) = local.kind.init_else_opt() {
            self.visit_expr(init);

            // Resolve the `else` block
            if let Some(els) = els {
                self.visit_block(els);
            }
        }

        // Resolve the pattern.
        self.resolve_pattern_top(&local.pat, PatternSource::Let);
    }

    /// Build a map from pattern identifiers to binding-info's, and check the bindings are
    /// consistent when encountering or-patterns and never patterns.
    /// This is done hygienically: this could arise for a macro that expands into an or-pattern
    /// where one 'x' was from the user and one 'x' came from the macro.
    ///
    /// A never pattern by definition indicates an unreachable case. For example, matching on
    /// `Result<T, &!>` could look like:
    /// ```rust
    /// # #![feature(never_type)]
    /// # #![feature(never_patterns)]
    /// # fn bar(_x: u32) {}
    /// let foo: Result<u32, &!> = Ok(0);
    /// match foo {
    ///     Ok(x) => bar(x),
    ///     Err(&!),
    /// }
    /// ```
    /// This extends to product types: `(x, !)` is likewise unreachable. So it doesn't make sense to
    /// have a binding here, and we tell the user to use `_` instead.
    fn compute_and_check_binding_map(
        &mut self,
        pat: &Pat,
    ) -> Result<FxIndexMap<Ident, BindingInfo>, IsNeverPattern> {
        let mut binding_map = FxIndexMap::default();
        let mut is_never_pat = false;

        pat.walk(&mut |pat| {
            match pat.kind {
                PatKind::Ident(annotation, ident, ref sub_pat)
                    if sub_pat.is_some() || self.is_base_res_local(pat.id) =>
                {
                    binding_map.insert(ident, BindingInfo { span: ident.span, annotation });
                }
                PatKind::Or(ref ps) => {
                    // Check the consistency of this or-pattern and
                    // then add all bindings to the larger map.
                    match self.compute_and_check_or_pat_binding_map(ps) {
                        Ok(bm) => binding_map.extend(bm),
                        Err(IsNeverPattern) => is_never_pat = true,
                    }
                    return false;
                }
                PatKind::Never => is_never_pat = true,
                _ => {}
            }

            true
        });

        if is_never_pat {
            for (_, binding) in binding_map {
                self.report_error(binding.span, ResolutionError::BindingInNeverPattern);
            }
            Err(IsNeverPattern)
        } else {
            Ok(binding_map)
        }
    }

    fn is_base_res_local(&self, nid: NodeId) -> bool {
        matches!(
            self.r.partial_res_map.get(&nid).map(|res| res.expect_full_res()),
            Some(Res::Local(..))
        )
    }

    /// Compute the binding map for an or-pattern. Checks that all of the arms in the or-pattern
    /// have exactly the same set of bindings, with the same binding modes for each.
    /// Returns the computed binding map and a boolean indicating whether the pattern is a never
    /// pattern.
    ///
    /// A never pattern by definition indicates an unreachable case. For example, destructuring a
    /// `Result<T, &!>` could look like:
    /// ```rust
    /// # #![feature(never_type)]
    /// # #![feature(never_patterns)]
    /// # fn foo() -> Result<bool, &'static !> { Ok(true) }
    /// let (Ok(x) | Err(&!)) = foo();
    /// # let _ = x;
    /// ```
    /// Because the `Err(&!)` branch is never reached, it does not need to have the same bindings as
    /// the other branches of the or-pattern. So we must ignore never pattern when checking the
    /// bindings of an or-pattern.
    /// Moreover, if all the subpatterns are never patterns (e.g. `Ok(!) | Err(!)`), then the
    /// pattern as a whole counts as a never pattern (since it's definitionallly unreachable).
    fn compute_and_check_or_pat_binding_map(
        &mut self,
        pats: &[Pat],
    ) -> Result<FxIndexMap<Ident, BindingInfo>, IsNeverPattern> {
        let mut missing_vars = FxIndexMap::default();
        let mut inconsistent_vars = FxIndexMap::default();

        // 1) Compute the binding maps of all arms; we must ignore never patterns here.
        let not_never_pats = pats
            .iter()
            .filter_map(|pat| {
                let binding_map = self.compute_and_check_binding_map(pat).ok()?;
                Some((binding_map, pat))
            })
            .collect::<Vec<_>>();

        // 2) Record any missing bindings or binding mode inconsistencies.
        for &(ref map_outer, pat_outer) in not_never_pats.iter() {
            // Check against all arms except for the same pattern which is always self-consistent.
            let inners = not_never_pats.iter().filter(|(_, pat)| pat.id != pat_outer.id);

            for &(ref map, pat) in inners {
                for (&name, binding_inner) in map {
                    match map_outer.get(&name) {
                        None => {
                            // The inner binding is missing in the outer.
                            let binding_error =
                                missing_vars.entry(name).or_insert_with(|| BindingError {
                                    name,
                                    origin: Default::default(),
                                    target: Default::default(),
                                    could_be_path: name.as_str().starts_with(char::is_uppercase),
                                });
                            binding_error.origin.push((binding_inner.span, pat.clone()));
                            binding_error.target.push(pat_outer.clone());
                        }
                        Some(binding_outer) => {
                            if binding_outer.annotation != binding_inner.annotation {
                                // The binding modes in the outer and inner bindings differ.
                                inconsistent_vars
                                    .entry(name)
                                    .or_insert((binding_inner.span, binding_outer.span));
                            }
                        }
                    }
                }
            }
        }

        // 3) Report all missing variables we found.
        for (name, mut v) in missing_vars {
            if inconsistent_vars.contains_key(&name) {
                v.could_be_path = false;
            }
            self.report_error(
                v.origin.iter().next().expect("invariant: iterator is non-empty").0,
                ResolutionError::VariableNotBoundInPattern(v, self.parent_scope),
            );
        }

        // 4) Report all inconsistencies in binding modes we found.
        for (name, v) in inconsistent_vars {
            self.report_error(v.0, ResolutionError::VariableBoundWithDifferentMode(name, v.1));
        }

        // 5) Bubble up the final binding map.
        if not_never_pats.is_empty() {
            // All the patterns are never patterns, so the whole or-pattern is one too.
            Err(IsNeverPattern)
        } else {
            let mut binding_map = FxIndexMap::default();
            for (bm, _) in not_never_pats {
                binding_map.extend(bm);
            }
            Ok(binding_map)
        }
    }

    /// Check the consistency of bindings wrt or-patterns and never patterns.
    fn check_consistent_bindings(&mut self, pat: &'ast Pat) {
        let mut is_or_or_never = false;
        pat.walk(&mut |pat| match pat.kind {
            PatKind::Or(..) | PatKind::Never => {
                is_or_or_never = true;
                false
            }
            _ => true,
        });
        if is_or_or_never {
            let _ = self.compute_and_check_binding_map(pat);
        }
    }

    fn resolve_arm(&mut self, arm: &'ast Arm) {
        self.with_rib(ValueNS, RibKind::Normal, |this| {
            this.resolve_pattern_top(&arm.pat, PatternSource::Match);
            visit_opt!(this, visit_expr, arm.guard.as_ref().map(|g| &g.cond));
            visit_opt!(this, visit_expr, &arm.body);
        });
    }

    /// Arising from `source`, resolve a top level pattern.
    fn resolve_pattern_top(&mut self, pat: &'ast Pat, pat_src: PatternSource) {
        let mut bindings = smallvec![(PatBoundCtx::Product, Default::default())];
        self.resolve_pattern(pat, pat_src, &mut bindings);
        self.apply_pattern_bindings(bindings);
    }

    /// Apply the bindings from a pattern to the innermost rib of the current scope.
    fn apply_pattern_bindings(&mut self, mut pat_bindings: PatternBindings) {
        let rib_bindings = self.innermost_rib_bindings(ValueNS);
        let Some((_, pat_bindings)) = pat_bindings.pop() else {
            // tRust: invariant — pattern bindings stack is never empty when applying bindings
            bug!("tried applying nonexistent bindings from pattern");
        };

        if rib_bindings.is_empty() {
            // Often, such as for match arms, the bindings are introduced into a new rib.
            // In this case, we can move the bindings over directly.
            *rib_bindings = pat_bindings;
        } else {
            rib_bindings.extend(pat_bindings);
        }
    }

    /// Resolve bindings in a pattern. `apply_pattern_bindings` must be called after to introduce
    /// the bindings into scope.
    fn resolve_pattern(
        &mut self,
        pat: &'ast Pat,
        pat_src: PatternSource,
        bindings: &mut PatternBindings,
    ) {
        // We walk the pattern before declaring the pattern's inner bindings,
        // so that we avoid resolving a literal expression to a binding defined
        // by the pattern.
        // NB: `Self::visit_pat` must be used rather than `visit::walk_pat` to avoid resolving guard
        // patterns' guard expressions multiple times (#141265).
        self.visit_pat(pat);
        self.resolve_pattern_inner(pat, pat_src, bindings);
        // This has to happen *after* we determine which pat_idents are variants:
        self.check_consistent_bindings(pat);
    }

    /// Resolve bindings in a pattern. This is a helper to `resolve_pattern`.
    ///
    /// ### `bindings`
    ///
    /// A stack of sets of bindings accumulated.
    ///
    /// In each set, `PatBoundCtx::Product` denotes that a found binding in it should
    /// be interpreted as re-binding an already bound binding. This results in an error.
    /// Meanwhile, `PatBound::Or` denotes that a found binding in the set should result
    /// in reusing this binding rather than creating a fresh one.
    ///
    /// When called at the top level, the stack must have a single element
    /// with `PatBound::Product`. Otherwise, pushing to the stack happens as
    /// or-patterns (`p_0 | ... | p_n`) are encountered and the context needs
    /// to be switched to `PatBoundCtx::Or` and then `PatBoundCtx::Product` for each `p_i`.
    /// When each `p_i` has been dealt with, the top set is merged with its parent.
    /// When a whole or-pattern has been dealt with, the thing happens.
    ///
    /// See the implementation and `fresh_binding` for more details.
    #[tracing::instrument(skip(self, bindings), level = "debug")]
    fn resolve_pattern_inner(
        &mut self,
        pat: &'ast Pat,
        pat_src: PatternSource,
        bindings: &mut PatternBindings,
    ) {
        // Visit all direct subpatterns of this pattern.
        pat.walk(&mut |pat| {
            match pat.kind {
                PatKind::Ident(bmode, ident, ref sub) => {
                    // First try to resolve the identifier as some existing entity,
                    // then fall back to a fresh binding.
                    let has_sub = sub.is_some();
                    let res = self
                        .try_resolve_as_non_binding(pat_src, bmode, ident, has_sub)
                        .unwrap_or_else(|| self.fresh_binding(ident, pat.id, pat_src, bindings));
                    self.r.record_partial_res(pat.id, PartialRes::new(res));
                    self.r.record_pat_span(pat.id, pat.span);
                }
                PatKind::TupleStruct(ref qself, ref path, ref sub_patterns) => {
                    self.smart_resolve_path(
                        pat.id,
                        qself,
                        path,
                        PathSource::TupleStruct(
                            pat.span,
                            self.r.arenas.alloc_pattern_spans(sub_patterns.iter().map(|p| p.span)),
                        ),
                    );
                }
                PatKind::Path(ref qself, ref path) => {
                    self.smart_resolve_path(pat.id, qself, path, PathSource::Pat);
                }
                PatKind::Struct(ref qself, ref path, ref _fields, ref rest) => {
                    self.smart_resolve_path(pat.id, qself, path, PathSource::Struct(None));
                    self.record_patterns_with_skipped_bindings(pat, rest);
                }
                PatKind::Or(ref ps) => {
                    // Add a new set of bindings to the stack. `Or` here records that when a
                    // binding already exists in this set, it should not result in an error because
                    // `V1(a) | V2(a)` must be allowed and are checked for consistency later.
                    bindings.push((PatBoundCtx::Or, Default::default()));
                    for p in ps {
                        // Now we need to switch back to a product context so that each
                        // part of the or-pattern internally rejects already bound names.
                        // For example, `V1(a) | V2(a, a)` and `V1(a, a) | V2(a)` are bad.
                        bindings.push((PatBoundCtx::Product, Default::default()));
                        self.resolve_pattern_inner(p, pat_src, bindings);
                        // Move up the non-overlapping bindings to the or-pattern.
                        // Existing bindings just get "merged".
                        let collected = bindings.pop().expect("invariant: non-empty collection").1;
                        bindings.last_mut().expect("invariant: value is present").1.extend(collected);
                    }
                    // This or-pattern itself can itself be part of a product,
                    // e.g. `(V1(a) | V2(a), a)` or `(a, V1(a) | V2(a))`.
                    // Both cases bind `a` again in a product pattern and must be rejected.
                    let collected = bindings.pop().expect("invariant: non-empty collection").1;
                    bindings.last_mut().expect("invariant: value is present").1.extend(collected);

                    // Prevent visiting `ps` as we've already done so above.
                    return false;
                }
                PatKind::Guard(ref subpat, ref guard) => {
                    // Add a new set of bindings to the stack to collect bindings in `subpat`.
                    bindings.push((PatBoundCtx::Product, Default::default()));
                    // Resolving `subpat` adds bindings onto the newly-pushed context. After, the
                    // total number of contexts on the stack should be the same as before.
                    let binding_ctx_stack_len = bindings.len();
                    self.resolve_pattern_inner(subpat, pat_src, bindings);
                    assert_eq!(bindings.len(), binding_ctx_stack_len);
                    // These bindings, but none from the surrounding pattern, are visible in the
                    // guard; put them in scope and resolve `guard`.
                    let subpat_bindings = bindings.pop().expect("invariant: non-empty collection").1;
                    self.with_rib(ValueNS, RibKind::Normal, |this| {
                        *this.innermost_rib_bindings(ValueNS) = subpat_bindings.clone();
                        this.resolve_expr(&guard.cond, None);
                    });
                    // Propagate the subpattern's bindings upwards.
                    // NOTE(guard_patterns): for `if let` guards, we'll also need to get the
                    // bindings introduced by the guard from its rib and propagate them upwards.
                    // This will require checking the identifiers for overlaps with `bindings`, like
                    // what `fresh_binding` does (ideally sharing its logic). To keep them separate
                    // from `subpat_bindings`, we can introduce a fresh rib for the guard.
                    bindings.last_mut().expect("invariant: value is present").1.extend(subpat_bindings);
                    // Prevent visiting `subpat` as we've already done so above.
                    return false;
                }
                _ => {}
            }
            true
        });
    }

    fn record_patterns_with_skipped_bindings(&mut self, pat: &Pat, rest: &ast::PatFieldsRest) {
        match rest {
            ast::PatFieldsRest::Rest(_) | ast::PatFieldsRest::Recovered(_) => {
                // Record that the pattern doesn't introduce all the bindings it could.
                if let Some(partial_res) = self.r.partial_res_map.get(&pat.id)
                    && let Some(res) = partial_res.full_res()
                    && let Some(def_id) = res.opt_def_id()
                {
                    self.ribs[ValueNS]
                        .last_mut()
                        .expect("invariant: value is present")
                        .patterns_with_skipped_bindings
                        .entry(def_id)
                        .or_default()
                        .push((
                            pat.span,
                            match rest {
                                ast::PatFieldsRest::Recovered(guar) => Err(*guar),
                                _ => Ok(()),
                            },
                        ));
                }
            }
            ast::PatFieldsRest::None => {}
        }
    }

    fn fresh_binding(
        &mut self,
        ident: Ident,
        pat_id: NodeId,
        pat_src: PatternSource,
        bindings: &mut PatternBindings,
    ) -> Res {
        // Add the binding to the bindings map, if it doesn't already exist.
        // (We must not add it if it's in the bindings map because that breaks the assumptions
        // later passes make about or-patterns.)
        let ident = ident.normalize_to_macro_rules();

        // Already bound in a product pattern? e.g. `(a, a)` which is not allowed.
        let already_bound_and = bindings
            .iter()
            .any(|(ctx, map)| *ctx == PatBoundCtx::Product && map.contains_key(&ident));
        if already_bound_and {
            // Overlap in a product pattern somewhere; report an error.
            use ResolutionError::*;
            let error = match pat_src {
                // `fn f(a: u8, a: u8)`:
                PatternSource::FnParam => IdentifierBoundMoreThanOnceInParameterList,
                // `Variant(a, a)`:
                _ => IdentifierBoundMoreThanOnceInSamePattern,
            };
            self.report_error(ident.span, error(ident));
        }

        // Already bound in an or-pattern? e.g. `V1(a) | V2(a)`.
        // This is *required* for consistency which is checked later.
        let already_bound_or = bindings
            .iter()
            .find_map(|(ctx, map)| if *ctx == PatBoundCtx::Or { map.get(&ident) } else { None });
        let res = if let Some(&res) = already_bound_or {
            // `Variant1(a) | Variant2(a)`, ok
            // Reuse definition from the first `a`.
            res
        } else {
            // A completely fresh binding is added to the map.
            Res::Local(pat_id)
        };

        // Record as bound.
        bindings.last_mut().expect("invariant: value is present").1.insert(ident, res);
        res
    }

    fn innermost_rib_bindings(&mut self, ns: Namespace) -> &mut FxIndexMap<Ident, Res> {
        &mut self.ribs[ns].last_mut().expect("invariant: value is present").bindings
    }

    fn try_resolve_as_non_binding(
        &mut self,
        pat_src: PatternSource,
        ann: BindingMode,
        ident: Ident,
        has_sub: bool,
    ) -> Option<Res> {
        // An immutable (no `mut`) by-value (no `ref`) binding pattern without
        // a sub pattern (no `@ $pat`) is syntactically ambiguous as it could
        // also be interpreted as a path to e.g. a constant, variant, etc.
        let is_syntactic_ambiguity = !has_sub && ann == BindingMode::NONE;

        let ls_binding = self.maybe_resolve_ident_in_lexical_scope(ident, ValueNS)?;
        let (res, binding) = match ls_binding {
            LateDecl::Decl(binding)
                if is_syntactic_ambiguity && binding.is_ambiguity_recursive() =>
            {
                // For ambiguous bindings we don't know all their definitions and cannot check
                // whether they can be shadowed by fresh bindings or not, so force an error.
                // issues/33118#issuecomment-233962221 (see below) still applies here,
                // but we have to ignore it for backward compatibility.
                self.r.record_use(ident, binding, Used::Other);
                return None;
            }
            LateDecl::Decl(binding) => (binding.res(), Some(binding)),
            LateDecl::RibDef(res) => (res, None),
        };

        match res {
            Res::SelfCtor(_) // See #70549.
            | Res::Def(
                DefKind::Ctor(_, CtorKind::Const) | DefKind::Const { .. } | DefKind::AssocConst { .. } | DefKind::ConstParam,
                _,
            ) if is_syntactic_ambiguity => {
                // Disambiguate in favor of a unit struct/variant or constant pattern.
                if let Some(binding) = binding {
                    self.r.record_use(ident, binding, Used::Other);
                }
                Some(res)
            }
            Res::Def(DefKind::Ctor(..) | DefKind::Const { .. } | DefKind::AssocConst { .. } | DefKind::Static { .. }, _) => {
                // This is unambiguously a fresh binding, either syntactically
                // (e.g., `IDENT @ PAT` or `ref IDENT`) or because `IDENT` resolves
                // to something unusable as a pattern (e.g., constructor function),
                // but we still conservatively report an error, see
                // issues/33118#issuecomment-233962221 for one reason why.
                let binding = binding.expect("no binding for a ctor or static");
                self.report_error(
                    ident.span,
                    ResolutionError::BindingShadowsSomethingUnacceptable {
                        shadowing_binding: pat_src,
                        name: ident.name,
                        participle: if binding.is_import() { "imported" } else { "defined" },
                        article: binding.res().article(),
                        shadowed_binding: binding.res(),
                        shadowed_binding_span: binding.span,
                    },
                );
                None
            }
            Res::Def(DefKind::ConstParam, def_id) => {
                // Same as for DefKind::Const { .. } above, but here, `binding` is `None`, so we
                // have to construct the error differently
                self.report_error(
                    ident.span,
                    ResolutionError::BindingShadowsSomethingUnacceptable {
                        shadowing_binding: pat_src,
                        name: ident.name,
                        participle: "defined",
                        article: res.article(),
                        shadowed_binding: res,
                        shadowed_binding_span: self.r.def_span(def_id),
                    }
                );
                None
            }
            Res::Def(DefKind::Fn | DefKind::AssocFn, _) | Res::Local(..) | Res::Err => {
                // These entities are explicitly allowed to be shadowed by fresh bindings.
                None
            }
            Res::SelfCtor(_) => {
                // We resolve `Self` in pattern position as an ident sometimes during recovery,
                // so delay a bug instead of ICEing.
                self.r.dcx().span_delayed_bug(
                    ident.span,
                    "unexpected `SelfCtor` in pattern, expected identifier"
                );
                None
            }
            // tRust: invariant — all valid resolution kinds for pattern identifiers handled above
            _ => span_bug!(
                ident.span,
                "unexpected resolution for an identifier in pattern: {:?}",
                res,
            ),
        }
    }


}
