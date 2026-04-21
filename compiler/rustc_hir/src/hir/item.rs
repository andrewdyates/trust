// tRust: split from hir.rs for maintainability
use super::*;


// N.B., if you change this, you'll probably want to change the corresponding
// type structure in middle/ty.rs as well.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct MutTy<'hir> {
    pub ty: &'hir Ty<'hir>,
    pub mutbl: Mutability,
}

/// Represents a function's signature in a trait declaration,
/// trait implementation, or a free function.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct FnSig<'hir> {
    pub header: FnHeader,
    pub decl: &'hir FnDecl<'hir>,
    pub span: Span,
}

// The bodies for items are stored "out of line", in a separate
// hashmap in the `Crate`. Here we just record the hir-id of the item
// so it can fetched later.
#[derive(Copy, Clone, PartialEq, Eq, Encodable, Decodable, Debug, HashStable_Generic)]
pub struct TraitItemId {
    pub owner_id: OwnerId,
}

impl TraitItemId {
    #[inline]
    pub fn hir_id(&self) -> HirId {
        // Items are always HIR owners.
        HirId::make_owner(self.owner_id.def_id)
    }
}

/// Represents an item declaration within a trait declaration,
/// possibly including a default implementation. A trait item is
/// either required (meaning it doesn't have an implementation, just a
/// signature) or provided (meaning it has a default implementation).
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct TraitItem<'hir> {
    pub ident: Ident,
    pub owner_id: OwnerId,
    pub generics: &'hir Generics<'hir>,
    pub kind: TraitItemKind<'hir>,
    pub span: Span,
    pub defaultness: Defaultness,
    pub has_delayed_lints: bool,
}


impl<'hir> TraitItem<'hir> {
    #[inline]
    pub fn hir_id(&self) -> HirId {
        // Items are always HIR owners.
        HirId::make_owner(self.owner_id.def_id)
    }

    pub fn trait_item_id(&self) -> TraitItemId {
        TraitItemId { owner_id: self.owner_id }
    }

    expect_methods_self_kind! {
        expect_const, (&'hir Ty<'hir>, Option<ConstItemRhs<'hir>>),
            TraitItemKind::Const(ty, rhs, _), (ty, *rhs);

        expect_fn, (&FnSig<'hir>, &TraitFn<'hir>),
            TraitItemKind::Fn(ty, trfn), (ty, trfn);

        expect_type, (GenericBounds<'hir>, Option<&'hir Ty<'hir>>),
            TraitItemKind::Type(bounds, ty), (bounds, *ty);
    }
}

/// Represents a trait method's body (or just argument names).
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum TraitFn<'hir> {
    /// No default body in the trait, just a signature.
    Required(&'hir [Option<Ident>]),

    /// Both signature and body are provided in the trait.
    Provided(BodyId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, HashStable_Generic)]
pub enum IsTypeConst {
    No,
    Yes,
}

impl From<bool> for IsTypeConst {
    fn from(value: bool) -> Self {
        if value { Self::Yes } else { Self::No }
    }
}

impl From<IsTypeConst> for bool {
    fn from(value: IsTypeConst) -> Self {
        matches!(value, IsTypeConst::Yes)
    }
}

/// Represents a trait method or associated constant or type
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum TraitItemKind<'hir> {
    // tRust: known issue — (mgca) eventually want to move the option that is around `ConstItemRhs<'hir>`
    // into `ConstItemRhs`, much like `ast::ConstItemRhsKind`, but for now mark whether
    // this node is a TypeConst with a flag.
    /// An associated constant with an optional value (otherwise `impl`s must contain a value).
    Const(&'hir Ty<'hir>, Option<ConstItemRhs<'hir>>, IsTypeConst),
    /// An associated function with an optional body.
    Fn(FnSig<'hir>, TraitFn<'hir>),
    /// An associated type with (possibly empty) bounds and optional concrete
    /// type.
    Type(GenericBounds<'hir>, Option<&'hir Ty<'hir>>),
}

// The bodies for items are stored "out of line", in a separate
// hashmap in the `Crate`. Here we just record the hir-id of the item
// so it can fetched later.
#[derive(Copy, Clone, PartialEq, Eq, Encodable, Decodable, Debug, HashStable_Generic)]
pub struct ImplItemId {
    pub owner_id: OwnerId,
}

impl ImplItemId {
    #[inline]
    pub fn hir_id(&self) -> HirId {
        // Items are always HIR owners.
        HirId::make_owner(self.owner_id.def_id)
    }
}

/// Represents an associated item within an impl block.
///
/// Refer to [`Impl`] for an impl block declaration.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct ImplItem<'hir> {
    pub ident: Ident,
    pub owner_id: OwnerId,
    pub generics: &'hir Generics<'hir>,
    pub kind: ImplItemKind<'hir>,
    pub impl_kind: ImplItemImplKind,
    pub span: Span,
    pub has_delayed_lints: bool,
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum ImplItemImplKind {
    Inherent {
        vis_span: Span,
    },
    Trait {
        defaultness: Defaultness,
        /// Item in the trait that this item implements
        trait_item_def_id: Result<DefId, ErrorGuaranteed>,
    },
}

impl<'hir> ImplItem<'hir> {
    #[inline]
    pub fn hir_id(&self) -> HirId {
        // Items are always HIR owners.
        HirId::make_owner(self.owner_id.def_id)
    }

    pub fn impl_item_id(&self) -> ImplItemId {
        ImplItemId { owner_id: self.owner_id }
    }

    pub fn vis_span(&self) -> Option<Span> {
        match self.impl_kind {
            ImplItemImplKind::Trait { .. } => None,
            ImplItemImplKind::Inherent { vis_span, .. } => Some(vis_span),
        }
    }

    expect_methods_self_kind! {
        expect_const, (&'hir Ty<'hir>, ConstItemRhs<'hir>), ImplItemKind::Const(ty, rhs), (ty, *rhs);
        expect_fn,    (&FnSig<'hir>, BodyId),               ImplItemKind::Fn(ty, body),   (ty, *body);
        expect_type,  &'hir Ty<'hir>,                       ImplItemKind::Type(ty),       ty;
    }
}

/// Represents various kinds of content within an `impl`.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum ImplItemKind<'hir> {
    /// An associated constant of the given type, set to the constant result
    /// of the expression.
    Const(&'hir Ty<'hir>, ConstItemRhs<'hir>),
    /// An associated function implementation with the given signature and body.
    Fn(FnSig<'hir>, BodyId),
    /// An associated type.
    Type(&'hir Ty<'hir>),
}

/// A constraint on an associated item.
///
/// ### Examples
///
/// * the `A = Ty` and `B = Ty` in `Trait<A = Ty, B = Ty>`
/// * the `G<Ty> = Ty` in `Trait<G<Ty> = Ty>`
/// * the `A: Bound` in `Trait<A: Bound>`
/// * the `RetTy` in `Trait(ArgTy, ArgTy) -> RetTy`
/// * the `C = { Ct }` in `Trait<C = { Ct }>` (feature `min_generic_const_args`)
/// * the `f(..): Bound` in `Trait<f(..): Bound>` (feature `return_type_notation`)
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct AssocItemConstraint<'hir> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub ident: Ident,
    pub gen_args: &'hir GenericArgs<'hir>,
    pub kind: AssocItemConstraintKind<'hir>,
    pub span: Span,
}

impl<'hir> AssocItemConstraint<'hir> {
    /// Obtain the type on the RHS of an assoc ty equality constraint if applicable.
    pub fn ty(self) -> Option<&'hir Ty<'hir>> {
        match self.kind {
            AssocItemConstraintKind::Equality { term: Term::Ty(ty) } => Some(ty),
            _ => None,
        }
    }

    /// Obtain the const on the RHS of an assoc const equality constraint if applicable.
    pub fn ct(self) -> Option<&'hir ConstArg<'hir>> {
        match self.kind {
            AssocItemConstraintKind::Equality { term: Term::Const(ct) } => Some(ct),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum Term<'hir> {
    Ty(&'hir Ty<'hir>),
    Const(&'hir ConstArg<'hir>),
}

impl<'hir> From<&'hir Ty<'hir>> for Term<'hir> {
    fn from(ty: &'hir Ty<'hir>) -> Self {
        Term::Ty(ty)
    }
}

impl<'hir> From<&'hir ConstArg<'hir>> for Term<'hir> {
    fn from(c: &'hir ConstArg<'hir>) -> Self {
        Term::Const(c)
    }
}

/// The kind of [associated item constraint][AssocItemConstraint].
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum AssocItemConstraintKind<'hir> {
    /// An equality constraint for an associated item (e.g., `AssocTy = Ty` in `Trait<AssocTy = Ty>`).
    ///
    /// Also known as an *associated item binding* (we *bind* an associated item to a term).
    ///
    /// Furthermore, associated type equality constraints can also be referred to as *associated type
    /// bindings*. Similarly with associated const equality constraints and *associated const bindings*.
    Equality { term: Term<'hir> },
    /// A bound on an associated type (e.g., `AssocTy: Bound` in `Trait<AssocTy: Bound>`).
    Bound { bounds: &'hir [GenericBound<'hir>] },
}

impl<'hir> AssocItemConstraintKind<'hir> {
    pub fn descr(&self) -> &'static str {
        match self {
            AssocItemConstraintKind::Equality { .. } => "binding",
            AssocItemConstraintKind::Bound { .. } => "constraint",
        }
    }
}
