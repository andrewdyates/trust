// tRust: split from hir.rs for maintainability
use super::*;


/// An uninhabited enum used to make `Infer` variants on [`Ty`] and [`ConstArg`] be
/// unreachable. Zero-Variant enums are guaranteed to have the same layout as the never
/// type.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum AmbigArg {}

/// Represents a type in the `HIR`.
///
/// For an explanation of the `Unambig` generic parameter see the dev-guide:
/// <https://rustc-dev-guide.rust-lang.org/ambig-unambig-ty-and-consts.html>
#[derive(Debug, Clone, Copy, HashStable_Generic)]
#[repr(C)]
pub struct Ty<'hir, Unambig = ()> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub span: Span,
    pub kind: TyKind<'hir, Unambig>,
}

impl<'hir> Ty<'hir, AmbigArg> {
    /// Converts a `Ty` in an ambiguous position to one in an unambiguous position.
    ///
    /// Functions accepting an unambiguous types may expect the [`TyKind::Infer`] variant
    /// to be used. Care should be taken to separately handle infer types when calling this
    /// function as it cannot be handled by downstream code making use of the returned ty.
    ///
    /// In practice this may mean overriding the [`Visitor::visit_infer`][visit_infer] method on hir visitors, or
    /// specifically matching on [`GenericArg::Infer`] when handling generic arguments.
    ///
    /// [visit_infer]: [rustc_hir::intravisit::Visitor::visit_infer]
    pub fn as_unambig_ty(&self) -> &Ty<'hir> {
        // SAFETY: `Ty` is `repr(C)` and `TyKind` is marked `repr(u8)` so that the layout is
        // the same across different ZST type arguments.
        let ptr = self as *const Ty<'hir, AmbigArg> as *const Ty<'hir, ()>;
        // SAFETY: The invariants required by this unsafe operation are
        // satisfied because this cast only changes the ZST marker type and still points at the same initialized `Ty` value.
        unsafe { &*ptr }
    }
}

impl<'hir> Ty<'hir> {
    /// Converts a `Ty` in an unambiguous position to one in an ambiguous position. This is
    /// fallible as the [`TyKind::Infer`] variant is not present in ambiguous positions.
    ///
    /// Functions accepting ambiguous types will not handle the [`TyKind::Infer`] variant, if
    /// infer types are relevant to you then care should be taken to handle them separately.
    pub fn try_as_ambig_ty(&self) -> Option<&Ty<'hir, AmbigArg>> {
        if let TyKind::Infer(()) = self.kind {
            return None;
        }

        // SAFETY: `Ty` is `repr(C)` and `TyKind` is marked `repr(u8)` so that the layout is
        // the same across different ZST type arguments. We also asserted that the `self` is
        // not a `TyKind::Infer` so there is no risk of transmuting a `()` to `AmbigArg`.
        let ptr = self as *const Ty<'hir> as *const Ty<'hir, AmbigArg>;
        // SAFETY: The invariants required by this unsafe operation are
        // satisfied because the layout matches and `Infer(())` was excluded above, so the value is valid as `TyKind<'hir, AmbigArg>`.
        Some(unsafe { &*ptr })
    }
}

impl<'hir> Ty<'hir, AmbigArg> {
    pub fn peel_refs(&self) -> &Ty<'hir> {
        let mut final_ty = self.as_unambig_ty();
        while let TyKind::Ref(_, MutTy { ty, .. }) = &final_ty.kind {
            final_ty = ty;
        }
        final_ty
    }
}

impl<'hir> Ty<'hir> {
    pub fn peel_refs(&self) -> &Self {
        let mut final_ty = self;
        while let TyKind::Ref(_, MutTy { ty, .. }) = &final_ty.kind {
            final_ty = ty;
        }
        final_ty
    }

    /// Returns `true` if `param_def_id` matches the `bounded_ty` of this predicate.
    pub fn as_generic_param(&self) -> Option<(DefId, Ident)> {
        let TyKind::Path(QPath::Resolved(None, path)) = self.kind else {
            return None;
        };
        let [segment] = &path.segments else {
            return None;
        };
        match path.res {
            Res::Def(DefKind::TyParam, def_id) | Res::SelfTyParam { trait_: def_id } => {
                Some((def_id, segment.ident))
            }
            _ => None,
        }
    }

    pub fn find_self_aliases(&self) -> Vec<Span> {
        use crate::intravisit::Visitor;
        struct MyVisitor(Vec<Span>);
        impl<'v> Visitor<'v> for MyVisitor {
            fn visit_ty(&mut self, t: &'v Ty<'v, AmbigArg>) {
                if matches!(
                    &t.kind,
                    TyKind::Path(QPath::Resolved(
                        _,
                        Path { res: crate::def::Res::SelfTyAlias { .. }, .. },
                    ))
                ) {
                    self.0.push(t.span);
                    return;
                }
                crate::intravisit::walk_ty(self, t);
            }
        }

        let mut my_visitor = MyVisitor(vec![]);
        my_visitor.visit_ty_unambig(self);
        my_visitor.0
    }

    /// Whether `ty` is a type with `_` placeholders that can be inferred. Used in diagnostics only to
    /// use inference to provide suggestions for the appropriate type if possible.
    pub fn is_suggestable_infer_ty(&self) -> bool {
        fn are_suggestable_generic_args(generic_args: &[GenericArg<'_>]) -> bool {
            generic_args.iter().any(|arg| match arg {
                GenericArg::Type(ty) => ty.as_unambig_ty().is_suggestable_infer_ty(),
                GenericArg::Infer(_) => true,
                _ => false,
            })
        }
        debug!(?self);
        match &self.kind {
            TyKind::Infer(()) => true,
            TyKind::Slice(ty) => ty.is_suggestable_infer_ty(),
            TyKind::Array(ty, length) => {
                ty.is_suggestable_infer_ty() || matches!(length.kind, ConstArgKind::Infer(..))
            }
            TyKind::Tup(tys) => tys.iter().any(Self::is_suggestable_infer_ty),
            TyKind::Ptr(mut_ty) | TyKind::Ref(_, mut_ty) => mut_ty.ty.is_suggestable_infer_ty(),
            TyKind::Path(QPath::TypeRelative(ty, segment)) => {
                ty.is_suggestable_infer_ty() || are_suggestable_generic_args(segment.args().args)
            }
            TyKind::Path(QPath::Resolved(ty_opt, Path { segments, .. })) => {
                ty_opt.is_some_and(Self::is_suggestable_infer_ty)
                    || segments
                        .iter()
                        .any(|segment| are_suggestable_generic_args(segment.args().args))
            }
            _ => false,
        }
    }
}

/// Not represented directly in the AST; referred to by name through a `ty_path`.
#[derive(Copy, Clone, PartialEq, Eq, Encodable, Decodable, Hash, Debug, HashStable_Generic)]
pub enum PrimTy {
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    Str,
    Bool,
    Char,
}

impl PrimTy {
    /// All of the primitive types
    pub const ALL: [Self; 19] = [
        // any changes here should also be reflected in `PrimTy::from_name`
        Self::Int(IntTy::I8),
        Self::Int(IntTy::I16),
        Self::Int(IntTy::I32),
        Self::Int(IntTy::I64),
        Self::Int(IntTy::I128),
        Self::Int(IntTy::Isize),
        Self::Uint(UintTy::U8),
        Self::Uint(UintTy::U16),
        Self::Uint(UintTy::U32),
        Self::Uint(UintTy::U64),
        Self::Uint(UintTy::U128),
        Self::Uint(UintTy::Usize),
        Self::Float(FloatTy::F16),
        Self::Float(FloatTy::F32),
        Self::Float(FloatTy::F64),
        Self::Float(FloatTy::F128),
        Self::Bool,
        Self::Char,
        Self::Str,
    ];

    /// Like [`PrimTy::name`], but returns a &str instead of a symbol.
    ///
    /// Used by clippy.
    pub fn name_str(self) -> &'static str {
        match self {
            PrimTy::Int(i) => i.name_str(),
            PrimTy::Uint(u) => u.name_str(),
            PrimTy::Float(f) => f.name_str(),
            PrimTy::Str => "str",
            PrimTy::Bool => "bool",
            PrimTy::Char => "char",
        }
    }

    pub fn name(self) -> Symbol {
        match self {
            PrimTy::Int(i) => i.name(),
            PrimTy::Uint(u) => u.name(),
            PrimTy::Float(f) => f.name(),
            PrimTy::Str => sym::str,
            PrimTy::Bool => sym::bool,
            PrimTy::Char => sym::char,
        }
    }

    /// Returns the matching `PrimTy` for a `Symbol` such as "str" or "i32".
    /// Returns `None` if no matching type is found.
    pub fn from_name(name: Symbol) -> Option<Self> {
        let ty = match name {
            // any changes here should also be reflected in `PrimTy::ALL`
            sym::i8 => Self::Int(IntTy::I8),
            sym::i16 => Self::Int(IntTy::I16),
            sym::i32 => Self::Int(IntTy::I32),
            sym::i64 => Self::Int(IntTy::I64),
            sym::i128 => Self::Int(IntTy::I128),
            sym::isize => Self::Int(IntTy::Isize),
            sym::u8 => Self::Uint(UintTy::U8),
            sym::u16 => Self::Uint(UintTy::U16),
            sym::u32 => Self::Uint(UintTy::U32),
            sym::u64 => Self::Uint(UintTy::U64),
            sym::u128 => Self::Uint(UintTy::U128),
            sym::usize => Self::Uint(UintTy::Usize),
            sym::f16 => Self::Float(FloatTy::F16),
            sym::f32 => Self::Float(FloatTy::F32),
            sym::f64 => Self::Float(FloatTy::F64),
            sym::f128 => Self::Float(FloatTy::F128),
            sym::bool => Self::Bool,
            sym::char => Self::Char,
            sym::str => Self::Str,
            _ => return None,
        };
        Some(ty)
    }
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct FnPtrTy<'hir> {
    pub safety: Safety,
    pub abi: ExternAbi,
    pub generic_params: &'hir [GenericParam<'hir>],
    pub decl: &'hir FnDecl<'hir>,
    // `Option` because bare fn parameter identifiers are optional. We also end up
    // with `None` in some error cases, e.g. invalid parameter patterns.
    pub param_idents: &'hir [Option<Ident>],
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct UnsafeBinderTy<'hir> {
    pub generic_params: &'hir [GenericParam<'hir>],
    pub inner_ty: &'hir Ty<'hir>,
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct OpaqueTy<'hir> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub def_id: LocalDefId,
    pub bounds: GenericBounds<'hir>,
    pub origin: OpaqueTyOrigin<LocalDefId>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, HashStable_Generic, Encodable, Decodable)]
pub enum PreciseCapturingArgKind<T, U> {
    Lifetime(T),
    /// Non-lifetime argument (type or const)
    Param(U),
}

pub type PreciseCapturingArg<'hir> =
    PreciseCapturingArgKind<&'hir Lifetime, PreciseCapturingNonLifetimeArg>;

impl PreciseCapturingArg<'_> {
    pub fn hir_id(self) -> HirId {
        match self {
            PreciseCapturingArg::Lifetime(lt) => lt.hir_id,
            PreciseCapturingArg::Param(param) => param.hir_id,
        }
    }

    pub fn name(self) -> Symbol {
        match self {
            PreciseCapturingArg::Lifetime(lt) => lt.ident.name,
            PreciseCapturingArg::Param(param) => param.ident.name,
        }
    }
}

/// We need to have a [`Node`] for the [`HirId`] that we attach the type/const param
/// resolution to. Lifetimes don't have this problem, and for them, it's actually
/// kind of detrimental to use a custom node type versus just using [`Lifetime`],
/// since resolve_bound_vars operates on `Lifetime`s.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct PreciseCapturingNonLifetimeArg {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub ident: Ident,
    pub res: Res,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[derive(HashStable_Generic, Encodable, Decodable)]
pub enum RpitContext {
    Trait,
    TraitImpl,
}

/// From whence the opaque type came.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[derive(HashStable_Generic, Encodable, Decodable)]
pub enum OpaqueTyOrigin<D> {
    /// `-> impl Trait`
    FnReturn {
        /// The defining function.
        parent: D,
        // Whether this is an RPITIT (return position impl trait in trait)
        in_trait_or_impl: Option<RpitContext>,
    },
    /// `async fn`
    AsyncFn {
        /// The defining function.
        parent: D,
        // Whether this is an AFIT (async fn in trait)
        in_trait_or_impl: Option<RpitContext>,
    },
    /// type aliases: `type Foo = impl Trait;`
    TyAlias {
        /// The type alias or associated type parent of the TAIT/ATPIT
        parent: D,
        /// associated types in impl blocks for traits.
        in_assoc_ty: bool,
    },
}

// Ids of parent (or child) path segment that contains user-specified args
#[derive(Debug, Clone, Copy, PartialEq, Eq, HashStable_Generic)]
pub struct DelegationGenerics {
    pub parent_args_segment_id: Option<HirId>,
    pub child_args_segment_id: Option<HirId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, HashStable_Generic)]
pub enum InferDelegationSig<'hir> {
    Input(usize),
    // Place generics info here, as we always specify output type for delegations.
    Output(&'hir DelegationGenerics),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, HashStable_Generic)]
pub enum InferDelegation<'hir> {
    /// Infer the type of this `DefId` through `tcx.type_of(def_id).instantiate_identity()`,
    /// used for const types propagation.
    DefId(DefId),
    /// Used during signature inheritance, `DefId` corresponds to the signature function.
    Sig(DefId, InferDelegationSig<'hir>),
}

/// The various kinds of types recognized by the compiler.
///
/// For an explanation of the `Unambig` generic parameter see the dev-guide:
/// <https://rustc-dev-guide.rust-lang.org/ambig-unambig-ty-and-consts.html>
// SAFETY: `repr(u8)` is required so that `TyKind<()>` and `TyKind<!>` are layout compatible
#[repr(u8, C)]
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum TyKind<'hir, Unambig = ()> {
    /// Actual type should be inherited from `DefId` signature
    InferDelegation(InferDelegation<'hir>),
    /// A variable length slice (i.e., `[T]`).
    Slice(&'hir Ty<'hir>),
    /// A fixed length array (i.e., `[T; n]`).
    Array(&'hir Ty<'hir>, &'hir ConstArg<'hir>),
    /// A raw pointer (i.e., `*const T` or `*mut T`).
    Ptr(MutTy<'hir>),
    /// A reference (i.e., `&'a T` or `&'a mut T`).
    Ref(&'hir Lifetime, MutTy<'hir>),
    /// A function pointer (e.g., `fn(usize) -> bool`).
    FnPtr(&'hir FnPtrTy<'hir>),
    /// An unsafe binder type (e.g. `unsafe<'a> Foo<'a>`).
    UnsafeBinder(&'hir UnsafeBinderTy<'hir>),
    /// The never type (`!`).
    Never,
    /// A tuple (`(A, B, C, D, ...)`).
    Tup(&'hir [Ty<'hir>]),
    /// A path to a type definition (`module::module::...::Type`), or an
    /// associated type (e.g., `<Vec<T> as Trait>::Type` or `<T>::Target`).
    ///
    /// Type parameters may be stored in each `PathSegment`.
    Path(QPath<'hir>),
    /// An opaque type definition itself. This is only used for `impl Trait`.
    OpaqueDef(&'hir OpaqueTy<'hir>),
    /// A trait ascription type, which is `impl Trait` within a local binding.
    TraitAscription(GenericBounds<'hir>),
    /// A trait object type `Bound1 + Bound2 + Bound3`
    /// where `Bound` is a trait or a lifetime.
    ///
    /// We use pointer tagging to represent a `&'hir Lifetime` and `TraitObjectSyntax` pair
    /// as otherwise this type being `repr(C)` would result in `TyKind` increasing in size.
    TraitObject(&'hir [PolyTraitRef<'hir>], TaggedRef<'hir, Lifetime, TraitObjectSyntax>),
    /// Placeholder for a type that has failed to be defined.
    Err(rustc_span::ErrorGuaranteed),
    /// Pattern types (`pattern_type!(u32 is 1..)`)
    Pat(&'hir Ty<'hir>, &'hir TyPat<'hir>),
    /// Field representing type (`field_of!(Struct, field)`).
    ///
    /// The optional ident is the variant when an enum is passed `field_of!(Enum, Variant.field)`.
    FieldOf(&'hir Ty<'hir>, &'hir TyFieldPath),
    /// `TyKind::Infer` means the type should be inferred instead of it having been
    /// specified. This can appear anywhere in a type.
    ///
    /// This variant is not always used to represent inference types, sometimes
    /// [`GenericArg::Infer`] is used instead.
    Infer(Unambig),
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum InlineAsmOperand<'hir> {
    In {
        reg: InlineAsmRegOrRegClass,
        expr: &'hir Expr<'hir>,
    },
    Out {
        reg: InlineAsmRegOrRegClass,
        late: bool,
        expr: Option<&'hir Expr<'hir>>,
    },
    InOut {
        reg: InlineAsmRegOrRegClass,
        late: bool,
        expr: &'hir Expr<'hir>,
    },
    SplitInOut {
        reg: InlineAsmRegOrRegClass,
        late: bool,
        in_expr: &'hir Expr<'hir>,
        out_expr: Option<&'hir Expr<'hir>>,
    },
    Const {
        anon_const: ConstBlock,
    },
    SymFn {
        expr: &'hir Expr<'hir>,
    },
    SymStatic {
        path: QPath<'hir>,
        def_id: DefId,
    },
    Label {
        block: &'hir Block<'hir>,
    },
}

impl<'hir> InlineAsmOperand<'hir> {
    pub fn reg(&self) -> Option<InlineAsmRegOrRegClass> {
        match *self {
            Self::In { reg, .. }
            | Self::Out { reg, .. }
            | Self::InOut { reg, .. }
            | Self::SplitInOut { reg, .. } => Some(reg),
            Self::Const { .. }
            | Self::SymFn { .. }
            | Self::SymStatic { .. }
            | Self::Label { .. } => None,
        }
    }

    pub fn is_clobber(&self) -> bool {
        matches!(
            self,
            InlineAsmOperand::Out { reg: InlineAsmRegOrRegClass::Reg(_), late: _, expr: None }
        )
    }
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct InlineAsm<'hir> {
    pub asm_macro: ast::AsmMacro,
    pub template: &'hir [InlineAsmTemplatePiece],
    pub template_strs: &'hir [(Symbol, Option<Symbol>, Span)],
    pub operands: &'hir [(InlineAsmOperand<'hir>, Span)],
    pub options: InlineAsmOptions,
    pub line_spans: &'hir [Span],
}

impl InlineAsm<'_> {
    pub fn contains_label(&self) -> bool {
        self.operands.iter().any(|x| matches!(x.0, InlineAsmOperand::Label { .. }))
    }
}

/// Represents a parameter in a function header.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct Param<'hir> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub pat: &'hir Pat<'hir>,
    pub ty_span: Span,
    pub span: Span,
}

/// Represents the header (not the body) of a function declaration.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct FnDecl<'hir> {
    /// The types of the function's parameters.
    ///
    /// Additional argument data is stored in the function's [body](Body::params).
    pub inputs: &'hir [Ty<'hir>],
    pub output: FnRetTy<'hir>,
    pub c_variadic: bool,
    /// Does the function have an implicit self?
    pub implicit_self: ImplicitSelfKind,
    /// Is lifetime elision allowed.
    pub lifetime_elision_allowed: bool,
}

impl<'hir> FnDecl<'hir> {
    pub fn opt_delegation_sig_id(&self) -> Option<DefId> {
        if let FnRetTy::Return(ty) = self.output
            && let TyKind::InferDelegation(InferDelegation::Sig(sig_id, _)) = ty.kind
        {
            return Some(sig_id);
        }
        None
    }

    pub fn opt_delegation_generics(&self) -> Option<&'hir DelegationGenerics> {
        if let FnRetTy::Return(ty) = self.output
            && let TyKind::InferDelegation(InferDelegation::Sig(_, kind)) = ty.kind
            && let InferDelegationSig::Output(generics) = kind
        {
            return Some(generics);
        }

        None
    }
}

/// Represents what type of implicit self a function has, if any.
#[derive(Copy, Clone, PartialEq, Eq, Encodable, Decodable, Debug, HashStable_Generic)]
pub enum ImplicitSelfKind {
    /// Represents a `fn x(self);`.
    Imm,
    /// Represents a `fn x(mut self);`.
    Mut,
    /// Represents a `fn x(&self);`.
    RefImm,
    /// Represents a `fn x(&mut self);`.
    RefMut,
    /// Represents when a function does not have a self argument or
    /// when a function has a `self: X` argument.
    None,
}

impl ImplicitSelfKind {
    /// Does this represent an implicit self?
    pub fn has_implicit_self(&self) -> bool {
        !matches!(*self, ImplicitSelfKind::None)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Encodable, Decodable, Debug, HashStable_Generic)]
pub enum IsAsync {
    Async(Span),
    NotAsync,
}

impl IsAsync {
    pub fn is_async(self) -> bool {
        matches!(self, IsAsync::Async(_))
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Encodable, Decodable, HashStable_Generic)]
#[derive(Default)]
pub enum Defaultness {
    Default {
        has_value: bool,
    },
    #[default]
    Final,
}

impl Defaultness {
    pub fn has_value(&self) -> bool {
        match *self {
            Defaultness::Default { has_value } => has_value,
            Defaultness::Final => true,
        }
    }

    pub fn is_final(&self) -> bool {
        *self == Defaultness::Final
    }

    pub fn is_default(&self) -> bool {
        matches!(*self, Defaultness::Default { .. })
    }
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum FnRetTy<'hir> {
    /// Return type is not specified.
    ///
    /// Functions default to `()` and
    /// closures default to inference. Span points to where return
    /// type would be inserted.
    DefaultReturn(Span),
    /// Everything else.
    Return(&'hir Ty<'hir>),
}

impl<'hir> FnRetTy<'hir> {
    #[inline]
    pub fn span(&self) -> Span {
        match *self {
            Self::DefaultReturn(span) => span,
            Self::Return(ref ty) => ty.span,
        }
    }

    pub fn is_suggestable_infer_ty(&self) -> Option<&'hir Ty<'hir>> {
        if let Self::Return(ty) = self
            && ty.is_suggestable_infer_ty()
        {
            return Some(*ty);
        }
        None
    }
}

/// Represents `for<...>` binder before a closure
#[derive(Copy, Clone, Debug, HashStable_Generic)]
pub enum ClosureBinder {
    /// Binder is not specified.
    Default,
    /// Binder is specified.
    ///
    /// Span points to the whole `for<...>`.
    For { span: Span },
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
