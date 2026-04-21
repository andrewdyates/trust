// tRust: split from hir.rs for maintainability
use super::*;


#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum GenericArg<'hir> {
    Lifetime(&'hir Lifetime),
    Type(&'hir Ty<'hir, AmbigArg>),
    Const(&'hir ConstArg<'hir, AmbigArg>),
    /// Inference variables in [`GenericArg`] are always represented by
    /// `GenericArg::Infer` instead of the `Infer` variants on [`TyKind`] and
    /// [`ConstArgKind`] as it is not clear until hir ty lowering whether a
    /// `_` argument is a type or const argument.
    ///
    /// However, some builtin types' generic arguments are represented by [`TyKind`]
    /// without a [`GenericArg`], instead directly storing a [`Ty`] or [`ConstArg`]. In
    /// such cases they *are* represented by the `Infer` variants on [`TyKind`] and
    /// [`ConstArgKind`] as it is not ambiguous whether the argument is a type or const.
    Infer(InferArg),
}

impl GenericArg<'_> {
    pub fn span(&self) -> Span {
        match self {
            GenericArg::Lifetime(l) => l.ident.span,
            GenericArg::Type(t) => t.span,
            GenericArg::Const(c) => c.span,
            GenericArg::Infer(i) => i.span,
        }
    }

    pub fn hir_id(&self) -> HirId {
        match self {
            GenericArg::Lifetime(l) => l.hir_id,
            GenericArg::Type(t) => t.hir_id,
            GenericArg::Const(c) => c.hir_id,
            GenericArg::Infer(i) => i.hir_id,
        }
    }

    pub fn descr(&self) -> &'static str {
        match self {
            GenericArg::Lifetime(_) => "lifetime",
            GenericArg::Type(_) => "type",
            GenericArg::Const(_) => "constant",
            GenericArg::Infer(_) => "placeholder",
        }
    }

    pub fn to_ord(&self) -> ast::ParamKindOrd {
        match self {
            GenericArg::Lifetime(_) => ast::ParamKindOrd::Lifetime,
            GenericArg::Type(_) | GenericArg::Const(_) | GenericArg::Infer(_) => {
                ast::ParamKindOrd::TypeOrConst
            }
        }
    }

    pub fn is_ty_or_const(&self) -> bool {
        match self {
            GenericArg::Lifetime(_) => false,
            GenericArg::Type(_) | GenericArg::Const(_) | GenericArg::Infer(_) => true,
        }
    }
}

/// The generic arguments and associated item constraints of a path segment.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct GenericArgs<'hir> {
    /// The generic arguments for this path segment.
    pub args: &'hir [GenericArg<'hir>],
    /// The associated item constraints for this path segment.
    pub constraints: &'hir [AssocItemConstraint<'hir>],
    /// Whether the arguments were written in parenthesized form (e.g., `Fn(T) -> U`).
    ///
    /// This is required mostly for pretty-printing and diagnostics,
    /// but also for changing lifetime elision rules to be "function-like".
    pub parenthesized: GenericArgsParentheses,
    /// The span encompassing the arguments, constraints and the surrounding brackets (`<>` or `()`).
    ///
    /// For example:
    ///
    /// ```ignore (illustrative)
    ///       Foo<A, B, AssocTy = D>           Fn(T, U, V) -> W
    ///          ^^^^^^^^^^^^^^^^^^^             ^^^^^^^^^
    /// ```
    ///
    /// Note that this may be:
    /// - empty, if there are no generic brackets (but there may be hidden lifetimes)
    /// - dummy, if this was generated during desugaring
    pub span_ext: Span,
}

impl<'hir> GenericArgs<'hir> {
    pub const NONE: &'hir GenericArgs<'hir> = &GenericArgs {
        args: &[],
        constraints: &[],
        parenthesized: GenericArgsParentheses::No,
        span_ext: DUMMY_SP,
    };

    /// Obtain the list of input types and the output type if the generic arguments are parenthesized.
    ///
    /// Returns the `Ty0, Ty1, ...` and the `RetTy` in `Trait(Ty0, Ty1, ...) -> RetTy`.
    /// Panics if the parenthesized arguments have an incorrect form (this shouldn't happen).
    pub fn paren_sugar_inputs_output(&self) -> Option<(&[Ty<'hir>], &Ty<'hir>)> {
        if self.parenthesized != GenericArgsParentheses::ParenSugar {
            return None;
        }

        let inputs = self
            .args
            .iter()
            .find_map(|arg| {
                let GenericArg::Type(ty) = arg else { return None };
                let TyKind::Tup(tys) = &ty.kind else { return None };
                Some(tys)
            })
            .expect("invariant: parenthesized generic args always contain a tuple type argument"); // tRust: unwrap -> expect

        Some((inputs, self.paren_sugar_output_inner()))
    }

    /// Obtain the output type if the generic arguments are parenthesized.
    ///
    /// Returns the `RetTy` in `Trait(Ty0, Ty1, ...) -> RetTy`.
    /// Panics if the parenthesized arguments have an incorrect form (this shouldn't happen).
    pub fn paren_sugar_output(&self) -> Option<&Ty<'hir>> {
        (self.parenthesized == GenericArgsParentheses::ParenSugar)
            .then(|| self.paren_sugar_output_inner())
    }

    fn paren_sugar_output_inner(&self) -> &Ty<'hir> {
        let [constraint] = self.constraints.try_into().expect("invariant: parenthesized sugar always has exactly one constraint"); // tRust: unwrap -> expect
        debug_assert_eq!(constraint.ident.name, sym::Output);
        constraint.ty().expect("invariant: Output constraint always has an associated type") // tRust: unwrap -> expect
    }

    pub fn has_err(&self) -> Option<ErrorGuaranteed> {
        self.args
            .iter()
            .find_map(|arg| {
                let GenericArg::Type(ty) = arg else { return None };
                let TyKind::Err(guar) = ty.kind else { return None };
                Some(guar)
            })
            .or_else(|| {
                self.constraints.iter().find_map(|constraint| {
                    let TyKind::Err(guar) = constraint.ty()?.kind else { return None };
                    Some(guar)
                })
            })
    }

    #[inline]
    pub fn num_lifetime_params(&self) -> usize {
        self.args.iter().filter(|arg| matches!(arg, GenericArg::Lifetime(_))).count()
    }

    #[inline]
    pub fn has_lifetime_params(&self) -> bool {
        self.args.iter().any(|arg| matches!(arg, GenericArg::Lifetime(_)))
    }

    #[inline]
    /// This function returns the number of type and const generic params.
    /// It should only be used for diagnostics.
    pub fn num_generic_params(&self) -> usize {
        self.args.iter().filter(|arg| !matches!(arg, GenericArg::Lifetime(_))).count()
    }

    /// The span encompassing the arguments and constraints[^1] inside the surrounding brackets.
    ///
    /// Returns `None` if the span is empty (i.e., no brackets) or dummy.
    ///
    /// [^1]: Unless of the form `-> Ty` (see [`GenericArgsParentheses`]).
    pub fn span(&self) -> Option<Span> {
        let span_ext = self.span_ext()?;
        Some(span_ext.with_lo(span_ext.lo() + BytePos(1)).with_hi(span_ext.hi() - BytePos(1)))
    }

    /// Returns span encompassing arguments and their surrounding `<>` or `()`
    pub fn span_ext(&self) -> Option<Span> {
        Some(self.span_ext).filter(|span| !span.is_empty())
    }

    pub fn is_empty(&self) -> bool {
        self.args.is_empty()
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, HashStable_Generic)]
pub enum GenericArgsParentheses {
    No,
    /// Bounds for `feature(return_type_notation)`, like `T: Trait<method(..): Send>`,
    /// where the args are explicitly elided with `..`
    ReturnTypeNotation,
    /// parenthesized function-family traits, like `T: Fn(u32) -> i32`
    ParenSugar,
}

/// The modifiers on a trait bound.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, HashStable_Generic)]
pub struct TraitBoundModifiers {
    pub constness: BoundConstness,
    pub polarity: BoundPolarity,
}

impl TraitBoundModifiers {
    pub const NONE: Self =
        TraitBoundModifiers { constness: BoundConstness::Never, polarity: BoundPolarity::Positive };
}

#[derive(Clone, Copy, Debug, HashStable_Generic)]
pub enum GenericBound<'hir> {
    Trait(PolyTraitRef<'hir>),
    Outlives(&'hir Lifetime),
    Use(&'hir [PreciseCapturingArg<'hir>], Span),
}

impl GenericBound<'_> {
    pub fn trait_ref(&self) -> Option<&TraitRef<'_>> {
        match self {
            GenericBound::Trait(data) => Some(&data.trait_ref),
            _ => None,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            GenericBound::Trait(t, ..) => t.span,
            GenericBound::Outlives(l) => l.ident.span,
            GenericBound::Use(_, span) => *span,
        }
    }
}

pub type GenericBounds<'hir> = &'hir [GenericBound<'hir>];

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, HashStable_Generic, Debug)]
pub enum MissingLifetimeKind {
    /// An explicit `'_`.
    Underscore,
    /// An elided lifetime `&' ty`.
    Ampersand,
    /// An elided lifetime in brackets with written brackets.
    Comma,
    /// An elided lifetime with elided brackets.
    Brackets,
}

#[derive(Copy, Clone, Debug, HashStable_Generic)]
pub enum LifetimeParamKind {
    // Indicates that the lifetime definition was explicitly declared (e.g., in
    // `fn foo<'a>(x: &'a u8) -> &'a u8 { x }`).
    Explicit,

    // Indication that the lifetime was elided (e.g., in both cases in
    // `fn foo(x: &u8) -> &'_ u8 { x }`).
    Elided(MissingLifetimeKind),

    // Indication that the lifetime name was somehow in error.
    Error,
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum GenericParamKind<'hir> {
    /// A lifetime definition (e.g., `'a: 'b + 'c + 'd`).
    Lifetime {
        kind: LifetimeParamKind,
    },
    Type {
        default: Option<&'hir Ty<'hir>>,
        synthetic: bool,
    },
    Const {
        ty: &'hir Ty<'hir>,
        /// Optional default value for the const generic param
        default: Option<&'hir ConstArg<'hir>>,
    },
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct GenericParam<'hir> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub def_id: LocalDefId,
    pub name: ParamName,
    pub span: Span,
    pub pure_wrt_drop: bool,
    pub kind: GenericParamKind<'hir>,
    pub colon_span: Option<Span>,
    pub source: GenericParamSource,
}

impl<'hir> GenericParam<'hir> {
    /// Synthetic type-parameters are inserted after normal ones.
    /// In order for normal parameters to be able to refer to synthetic ones,
    /// scans them first.
    pub fn is_impl_trait(&self) -> bool {
        matches!(self.kind, GenericParamKind::Type { synthetic: true, .. })
    }

    /// This can happen for `async fn`, e.g. `async fn f<'_>(&'_ self)`.
    ///
    /// See `lifetime_to_generic_param` in `rustc_ast_lowering` for more information.
    pub fn is_elided_lifetime(&self) -> bool {
        matches!(self.kind, GenericParamKind::Lifetime { kind: LifetimeParamKind::Elided(_) })
    }

    pub fn is_lifetime(&self) -> bool {
        matches!(self.kind, GenericParamKind::Lifetime { .. })
    }
}

/// Records where the generic parameter originated from.
///
/// This can either be from an item's generics, in which case it's typically
/// early-bound (but can be a late-bound lifetime in functions, for example),
/// or from a `for<...>` binder, in which case it's late-bound (and notably,
/// does not show up in the parent item's generics).
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum GenericParamSource {
    // Early or late-bound parameters defined on an item
    Generics,
    // Late-bound parameters defined via a `for<...>`
    Binder,
}

#[derive(Default)]
pub struct GenericParamCount {
    pub lifetimes: usize,
    pub types: usize,
    pub consts: usize,
    pub infer: usize,
}

/// Represents lifetimes and type parameters attached to a declaration
/// of a function, enum, trait, etc.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct Generics<'hir> {
    pub params: &'hir [GenericParam<'hir>],
    pub predicates: &'hir [WherePredicate<'hir>],
    pub has_where_clause_predicates: bool,
    pub where_clause_span: Span,
    pub span: Span,
}

impl<'hir> Generics<'hir> {
    pub const fn empty() -> &'hir Generics<'hir> {
        const NOPE: Generics<'_> = Generics {
            params: &[],
            predicates: &[],
            has_where_clause_predicates: false,
            where_clause_span: DUMMY_SP,
            span: DUMMY_SP,
        };
        &NOPE
    }

    pub fn get_named(&self, name: Symbol) -> Option<&GenericParam<'hir>> {
        self.params.iter().find(|&param| name == param.name.ident().name)
    }

    /// If there are generic parameters, return where to introduce a new one.
    pub fn span_for_lifetime_suggestion(&self) -> Option<Span> {
        if let Some(first) = self.params.first()
            && self.span.contains(first.span)
        {
            // `fn foo<A>(t: impl Trait)`
            //         ^ suggest `'a, ` here
            Some(first.span.shrink_to_lo())
        } else {
            None
        }
    }

    /// If there are generic parameters, return where to introduce a new one.
    pub fn span_for_param_suggestion(&self) -> Option<Span> {
        self.params.iter().any(|p| self.span.contains(p.span)).then(|| {
            // `fn foo<A>(t: impl Trait)`
            //          ^ suggest `, T: Trait` here
            self.span.with_lo(self.span.hi() - BytePos(1)).shrink_to_lo()
        })
    }

    /// `Span` where further predicates would be suggested, accounting for trailing commas, like
    ///  in `fn foo<T>(t: T) where T: Foo,` so we don't suggest two trailing commas.
    pub fn tail_span_for_predicate_suggestion(&self) -> Span {
        let end = self.where_clause_span.shrink_to_hi();
        if self.has_where_clause_predicates {
            self.predicates
                .iter()
                .rfind(|&p| p.kind.in_where_clause())
                .map_or(end, |p| p.span)
                .shrink_to_hi()
                .to(end)
        } else {
            end
        }
    }

    pub fn add_where_or_trailing_comma(&self) -> &'static str {
        if self.has_where_clause_predicates {
            ","
        } else if self.where_clause_span.is_empty() {
            " where"
        } else {
            // No where clause predicates, but we have `where` token
            ""
        }
    }

    pub fn bounds_for_param(
        &self,
        param_def_id: LocalDefId,
    ) -> impl Iterator<Item = &WhereBoundPredicate<'hir>> {
        self.predicates.iter().filter_map(move |pred| match pred.kind {
            WherePredicateKind::BoundPredicate(bp)
                if bp.is_param_bound(param_def_id.to_def_id()) =>
            {
                Some(bp)
            }
            _ => None,
        })
    }

    pub fn outlives_for_param(
        &self,
        param_def_id: LocalDefId,
    ) -> impl Iterator<Item = &WhereRegionPredicate<'_>> {
        self.predicates.iter().filter_map(move |pred| match pred.kind {
            WherePredicateKind::RegionPredicate(rp) if rp.is_param_bound(param_def_id) => Some(rp),
            _ => None,
        })
    }

    /// Returns a suggestable empty span right after the "final" bound of the generic parameter.
    ///
    /// If that bound needs to be wrapped in parentheses to avoid ambiguity with
    /// subsequent bounds, it also returns an empty span for an open parenthesis
    /// as the second component.
    ///
    /// E.g., adding `+ 'static` after `Fn() -> dyn Future<Output = ()>` or
    /// `Fn() -> &'static dyn Debug` requires parentheses:
    /// `Fn() -> (dyn Future<Output = ()>) + 'static` and
    /// `Fn() -> &'static (dyn Debug) + 'static`, respectively.
    pub fn bounds_span_for_suggestions(
        &self,
        param_def_id: LocalDefId,
    ) -> Option<(Span, Option<Span>)> {
        self.bounds_for_param(param_def_id).flat_map(|bp| bp.bounds.iter().rev()).find_map(
            |bound| {
                let span_for_parentheses = if let Some(trait_ref) = bound.trait_ref()
                    && let [.., segment] = trait_ref.path.segments
                    && let Some(ret_ty) = segment.args().paren_sugar_output()
                    && let ret_ty = ret_ty.peel_refs()
                    && let TyKind::TraitObject(_, tagged_ptr) = ret_ty.kind
                    && let TraitObjectSyntax::Dyn = tagged_ptr.tag()
                    && ret_ty.span.can_be_used_for_suggestions()
                {
                    Some(ret_ty.span)
                } else {
                    None
                };

                span_for_parentheses.map_or_else(
                    || {
                        // We include bounds that come from a `#[derive(_)]` but point at the user's
                        // code, as we use this method to get a span appropriate for suggestions.
                        let bs = bound.span();
                        // We use `from_expansion` instead of `can_be_used_for_suggestions` because
                        // the trait bound from imperfect derives do point at the type parameter,
                        // but expanded to a where clause, so we want to ignore those. This is only
                        // true for derive intrinsics.
                        bs.from_expansion().not().then(|| (bs.shrink_to_hi(), None))
                    },
                    |span| Some((span.shrink_to_hi(), Some(span.shrink_to_lo()))),
                )
            },
        )
    }

    pub fn span_for_predicate_removal(&self, pos: usize) -> Span {
        let predicate = &self.predicates[pos];
        let span = predicate.span;

        if !predicate.kind.in_where_clause() {
            // <T: ?Sized, U>
            //   ^^^^^^^^
            return span;
        }

        // We need to find out which comma to remove.
        if pos < self.predicates.len() - 1 {
            let next_pred = &self.predicates[pos + 1];
            if next_pred.kind.in_where_clause() {
                // where T: ?Sized, Foo: Bar,
                //       ^^^^^^^^^^^
                return span.until(next_pred.span);
            }
        }

        if pos > 0 {
            let prev_pred = &self.predicates[pos - 1];
            if prev_pred.kind.in_where_clause() {
                // where Foo: Bar, T: ?Sized,
                //               ^^^^^^^^^^^
                return prev_pred.span.shrink_to_hi().to(span);
            }
        }

        // This is the only predicate in the where clause.
        // where T: ?Sized
        // ^^^^^^^^^^^^^^^
        self.where_clause_span
    }

    pub fn span_for_bound_removal(&self, predicate_pos: usize, bound_pos: usize) -> Span {
        let predicate = &self.predicates[predicate_pos];
        let bounds = predicate.kind.bounds();

        if bounds.len() == 1 {
            return self.span_for_predicate_removal(predicate_pos);
        }

        let bound_span = bounds[bound_pos].span();
        if bound_pos < bounds.len() - 1 {
            // If there's another bound after the current bound
            // include the following '+' e.g.:
            //
            //  `T: Foo + CurrentBound + Bar`
            //            ^^^^^^^^^^^^^^^
            bound_span.to(bounds[bound_pos + 1].span().shrink_to_lo())
        } else {
            // If the current bound is the last bound
            // include the preceding '+' E.g.:
            //
            //  `T: Foo + Bar + CurrentBound`
            //               ^^^^^^^^^^^^^^^
            bound_span.with_lo(bounds[bound_pos - 1].span().hi())
        }
    }
}

/// A single predicate in a where-clause.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct WherePredicate<'hir> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub span: Span,
    pub kind: &'hir WherePredicateKind<'hir>,
}

/// The kind of a single predicate in a where-clause.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum WherePredicateKind<'hir> {
    /// A type bound (e.g., `for<'c> Foo: Send + Clone + 'c`).
    BoundPredicate(WhereBoundPredicate<'hir>),
    /// A lifetime predicate (e.g., `'a: 'b + 'c`).
    RegionPredicate(WhereRegionPredicate<'hir>),
    /// An equality predicate (unsupported).
    EqPredicate(WhereEqPredicate<'hir>),
}

impl<'hir> WherePredicateKind<'hir> {
    pub fn in_where_clause(&self) -> bool {
        match self {
            WherePredicateKind::BoundPredicate(p) => p.origin == PredicateOrigin::WhereClause,
            WherePredicateKind::RegionPredicate(p) => p.in_where_clause,
            WherePredicateKind::EqPredicate(_) => false,
        }
    }

    pub fn bounds(&self) -> GenericBounds<'hir> {
        match self {
            WherePredicateKind::BoundPredicate(p) => p.bounds,
            WherePredicateKind::RegionPredicate(p) => p.bounds,
            WherePredicateKind::EqPredicate(_) => &[],
        }
    }
}

#[derive(Copy, Clone, Debug, HashStable_Generic, PartialEq, Eq)]
pub enum PredicateOrigin {
    WhereClause,
    GenericParam,
    ImplTrait,
}

/// A type bound (e.g., `for<'c> Foo: Send + Clone + 'c`).
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct WhereBoundPredicate<'hir> {
    /// Origin of the predicate.
    pub origin: PredicateOrigin,
    /// Any generics from a `for` binding.
    pub bound_generic_params: &'hir [GenericParam<'hir>],
    /// The type being bounded.
    pub bounded_ty: &'hir Ty<'hir>,
    /// Trait and lifetime bounds (e.g., `Clone + Send + 'static`).
    pub bounds: GenericBounds<'hir>,
}

impl<'hir> WhereBoundPredicate<'hir> {
    /// Returns `true` if `param_def_id` matches the `bounded_ty` of this predicate.
    pub fn is_param_bound(&self, param_def_id: DefId) -> bool {
        self.bounded_ty.as_generic_param().is_some_and(|(def_id, _)| def_id == param_def_id)
    }
}

/// A lifetime predicate (e.g., `'a: 'b + 'c`).
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct WhereRegionPredicate<'hir> {
    pub in_where_clause: bool,
    pub lifetime: &'hir Lifetime,
    pub bounds: GenericBounds<'hir>,
}

impl<'hir> WhereRegionPredicate<'hir> {
    /// Returns `true` if `param_def_id` matches the `lifetime` of this predicate.
    fn is_param_bound(&self, param_def_id: LocalDefId) -> bool {
        self.lifetime.kind == LifetimeKind::Param(param_def_id)
    }
}

/// An equality predicate (e.g., `T = int`); currently unsupported.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct WhereEqPredicate<'hir> {
    pub lhs_ty: &'hir Ty<'hir>,
    pub rhs_ty: &'hir Ty<'hir>,
}

/// HIR node coupled with its parent's id in the same HIR owner.
///
/// The parent is trash when the node is a HIR owner.
