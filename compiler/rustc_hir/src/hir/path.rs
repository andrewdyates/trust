// tRust: split from hir.rs for maintainability
use super::*;


/// A `Path` is essentially Rust's notion of a name; for instance,
/// `std::cmp::PartialEq`. It's represented as a sequence of identifiers,
/// along with a bunch of supporting information.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct Path<'hir, R = Res> {
    pub span: Span,
    /// The resolution for the path.
    pub res: R,
    /// The segments in the path: the things separated by `::`.
    pub segments: &'hir [PathSegment<'hir>],
}

/// Up to three resolutions for type, value and macro namespaces.
pub type UsePath<'hir> = Path<'hir, PerNS<Option<Res>>>;

impl Path<'_> {
    pub fn is_global(&self) -> bool {
        self.segments.first().is_some_and(|segment| segment.ident.name == kw::PathRoot)
    }
}

/// A segment of a path: an identifier, an optional lifetime, and a set of
/// types.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct PathSegment<'hir> {
    /// The identifier portion of this path segment.
    pub ident: Ident,
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub res: Res,

    /// Type/lifetime parameters attached to this path. They come in
    /// two flavors: `Path<A,B,C>` and `Path(A,B) -> C`. Note that
    /// this is more than just simple syntactic sugar; the use of
    /// parens affects the region binding rules, so we preserve the
    /// distinction.
    pub args: Option<&'hir GenericArgs<'hir>>,

    /// Whether to infer remaining type parameters, if any.
    /// This only applies to expression and pattern paths, and
    /// out of those only the segments with no type parameters
    /// to begin with, e.g., `Vec::new` is `<Vec<..>>::new::<..>`.
    pub infer_args: bool,
}

impl<'hir> PathSegment<'hir> {
    /// Converts an identifier to the corresponding segment.
    pub fn new(ident: Ident, hir_id: HirId, res: Res) -> PathSegment<'hir> {
        PathSegment { ident, hir_id, res, infer_args: true, args: None }
    }

    pub fn invalid() -> Self {
        Self::new(Ident::dummy(), HirId::INVALID, Res::Err)
    }

    pub fn args(&self) -> &GenericArgs<'hir> {
        if let Some(ref args) = self.args { args } else { GenericArgs::NONE }
    }
}

#[derive(Clone, Copy, Debug, HashStable_Generic)]
pub enum ConstItemRhs<'hir> {
    Body(BodyId),
    TypeConst(&'hir ConstArg<'hir>),
}

impl<'hir> ConstItemRhs<'hir> {
    pub fn hir_id(&self) -> HirId {
        match self {
            ConstItemRhs::Body(body_id) => body_id.hir_id,
            ConstItemRhs::TypeConst(ct_arg) => ct_arg.hir_id,
        }
    }

    pub fn span<'tcx>(&self, tcx: impl crate::intravisit::HirTyCtxt<'tcx>) -> Span {
        match self {
            ConstItemRhs::Body(body_id) => tcx.hir_body(*body_id).value.span,
            ConstItemRhs::TypeConst(ct_arg) => ct_arg.span,
        }
    }
}

/// A constant that enters the type system, used for arguments to const generics (e.g. array lengths).
///
/// These are distinct from [`AnonConst`] as anon consts in the type system are not allowed
/// to use any generic parameters, therefore we must represent `N` differently. Additionally
/// future designs for supporting generic parameters in const arguments will likely not use
/// an anon const based design.
///
/// So, `ConstArg` (specifically, [`ConstArgKind`]) distinguishes between const args
/// that are [just paths](ConstArgKind::Path) (currently just bare const params)
/// versus const args that are literals or have arbitrary computations (e.g., `{ 1 + 3 }`).
///
/// For an explanation of the `Unambig` generic parameter see the dev-guide:
/// <https://rustc-dev-guide.rust-lang.org/ambig-unambig-ty-and-consts.html>
#[derive(Clone, Copy, Debug, HashStable_Generic)]
#[repr(C)]
pub struct ConstArg<'hir, Unambig = ()> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub kind: ConstArgKind<'hir, Unambig>,
    pub span: Span,
}

impl<'hir> ConstArg<'hir, AmbigArg> {
    /// Converts a `ConstArg` in an ambiguous position to one in an unambiguous position.
    ///
    /// Functions accepting unambiguous consts may expect the [`ConstArgKind::Infer`] variant
    /// to be used. Care should be taken to separately handle infer consts when calling this
    /// function as it cannot be handled by downstream code making use of the returned const.
    ///
    /// In practice this may mean overriding the [`Visitor::visit_infer`][visit_infer] method on hir visitors, or
    /// specifically matching on [`GenericArg::Infer`] when handling generic arguments.
    ///
    /// [visit_infer]: [rustc_hir::intravisit::Visitor::visit_infer]
    pub fn as_unambig_ct(&self) -> &ConstArg<'hir> {
        // SAFETY: `ConstArg` is `repr(C)` and `ConstArgKind` is marked `repr(u8)` so that the
        // layout is the same across different ZST type arguments.
        let ptr = self as *const ConstArg<'hir, AmbigArg> as *const ConstArg<'hir, ()>;
        // SAFETY: The invariants required by this unsafe operation are
        // satisfied because this cast only changes the ZST marker type and still points at the same initialized `ConstArg` value.
        unsafe { &*ptr }
    }
}

impl<'hir> ConstArg<'hir> {
    /// Converts a `ConstArg` in an unambiguous position to one in an ambiguous position. This is
    /// fallible as the [`ConstArgKind::Infer`] variant is not present in ambiguous positions.
    ///
    /// Functions accepting ambiguous consts will not handle the [`ConstArgKind::Infer`] variant, if
    /// infer consts are relevant to you then care should be taken to handle them separately.
    pub fn try_as_ambig_ct(&self) -> Option<&ConstArg<'hir, AmbigArg>> {
        if let ConstArgKind::Infer(()) = self.kind {
            return None;
        }

        // SAFETY: `ConstArg` is `repr(C)` and `ConstArgKind` is marked `repr(u8)` so that the layout is
        // the same across different ZST type arguments. We also asserted that the `self` is
        // not a `ConstArgKind::Infer` so there is no risk of transmuting a `()` to `AmbigArg`.
        let ptr = self as *const ConstArg<'hir> as *const ConstArg<'hir, AmbigArg>;
        // SAFETY: The invariants required by this unsafe operation are
        // satisfied because the layout matches and `Infer(())` was excluded above, so the value is valid as `ConstArgKind<'hir, AmbigArg>`.
        Some(unsafe { &*ptr })
    }
}

impl<'hir, Unambig> ConstArg<'hir, Unambig> {
    pub fn anon_const_hir_id(&self) -> Option<HirId> {
        match self.kind {
            ConstArgKind::Anon(ac) => Some(ac.hir_id),
            _ => None,
        }
    }
}

/// See [`ConstArg`].
#[derive(Clone, Copy, Debug, HashStable_Generic)]
#[repr(u8, C)]
pub enum ConstArgKind<'hir, Unambig = ()> {
    Tup(&'hir [&'hir ConstArg<'hir, Unambig>]),
    /// **Note:** Currently this is only used for bare const params
    /// (`N` where `fn foo<const N: usize>(...)`),
    /// not paths to any const (`N` where `const N: usize = ...`).
    ///
    /// However, in the future, we'll be using it for all of those.
    Path(QPath<'hir>),
    Anon(&'hir AnonConst),
    /// Represents construction of struct/struct variants
    Struct(QPath<'hir>, &'hir [&'hir ConstArgExprField<'hir>]),
    /// Tuple constructor variant
    TupleCall(QPath<'hir>, &'hir [&'hir ConstArg<'hir>]),
    /// Array literal argument
    Array(&'hir ConstArgArrayExpr<'hir>),
    /// Error const
    Error(ErrorGuaranteed),
    /// This variant is not always used to represent inference consts, sometimes
    /// [`GenericArg::Infer`] is used instead.
    Infer(Unambig),
    Literal {
        lit: LitKind,
        negated: bool,
    },
}

#[derive(Clone, Copy, Debug, HashStable_Generic)]
pub struct ConstArgExprField<'hir> {
    pub hir_id: HirId,
    pub span: Span,
    pub field: Ident,
    pub expr: &'hir ConstArg<'hir>,
}

#[derive(Clone, Copy, Debug, HashStable_Generic)]
pub struct ConstArgArrayExpr<'hir> {
    pub span: Span,
    pub elems: &'hir [&'hir ConstArg<'hir>],
}

#[derive(Clone, Copy, Debug, HashStable_Generic)]
pub struct InferArg {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub span: Span,
}

impl InferArg {
    pub fn to_ty(&self) -> Ty<'static> {
        Ty { kind: TyKind::Infer(()), span: self.span, hir_id: self.hir_id }
    }
}
