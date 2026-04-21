// tRust: split from hir.rs for maintainability
use super::*;

pub struct Mod<'hir> {
    pub spans: ModSpans,
    pub item_ids: &'hir [ItemId],
}

#[derive(Copy, Clone, Debug, HashStable_Generic)]
pub struct ModSpans {
    /// A span from the first token past `{` to the last token until `}`.
    /// For `mod foo;`, the inner span ranges from the first token
    /// to the last token in the external file.
    pub inner_span: Span,
    pub inject_use_span: Span,
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct EnumDef<'hir> {
    pub variants: &'hir [Variant<'hir>],
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct Variant<'hir> {
    /// Name of the variant.
    pub ident: Ident,
    /// Id of the variant (not the constructor, see `VariantData::ctor_hir_id()`).
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub def_id: LocalDefId,
    /// Fields and constructor id of the variant.
    pub data: VariantData<'hir>,
    /// Explicit discriminant (e.g., `Foo = 1`).
    pub disr_expr: Option<&'hir AnonConst>,
    /// Span
    pub span: Span,
}

#[derive(Copy, Clone, PartialEq, Debug, HashStable_Generic)]
pub enum UseKind {
    /// One import, e.g., `use foo::bar` or `use foo::bar as baz`.
    /// Also produced for each element of a list `use`, e.g.
    /// `use foo::{a, b}` lowers to `use foo::a; use foo::b;`.
    ///
    /// The identifier is the name defined by the import. E.g. for `use
    /// foo::bar` it is `bar`, for `use foo::bar as baz` it is `baz`.
    Single(Ident),

    /// Glob import, e.g., `use foo::*`.
    Glob,

    /// Degenerate list import, e.g., `use foo::{a, b}` produces
    /// an additional `use foo::{}` for performing checks such as
    /// unstable feature gating. May be removed in the future.
    ListStem,
}

/// References to traits in impls.
///
/// `resolve` maps each `TraitRef`'s `ref_id` to its defining trait; that's all
/// that the `ref_id` is for. Note that `ref_id`'s value is not the `HirId` of the
/// trait being referred to but just a unique `HirId` that serves as a key
/// within the resolution map.
#[derive(Clone, Debug, Copy, HashStable_Generic)]
pub struct TraitRef<'hir> {
    pub path: &'hir Path<'hir>,
    // Don't hash the `ref_id`. It is tracked via the thing it is used to access.
    #[stable_hasher(ignore)]
    pub hir_ref_id: HirId,
}

impl TraitRef<'_> {
    /// Gets the `DefId` of the referenced trait. It _must_ actually be a trait or trait alias.
    pub fn trait_def_id(&self) -> Option<DefId> {
        match self.path.res {
            Res::Def(DefKind::Trait | DefKind::TraitAlias, did) => Some(did),
            Res::Err => None,
            res => panic!("{res:?} did not resolve to a trait or trait alias"),
        }
    }
}

#[derive(Clone, Debug, Copy, HashStable_Generic)]
pub struct PolyTraitRef<'hir> {
    /// The `'a` in `for<'a> Foo<&'a T>`.
    pub bound_generic_params: &'hir [GenericParam<'hir>],

    /// The constness and polarity of the trait ref.
    ///
    /// The `async` modifier is lowered directly into a different trait for now.
    pub modifiers: TraitBoundModifiers,

    /// The `Foo<&'a T>` in `for<'a> Foo<&'a T>`.
    pub trait_ref: TraitRef<'hir>,

    pub span: Span,
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct FieldDef<'hir> {
    pub span: Span,
    pub vis_span: Span,
    pub ident: Ident,
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub def_id: LocalDefId,
    pub ty: &'hir Ty<'hir>,
    pub safety: Safety,
    pub default: Option<&'hir AnonConst>,
}

impl FieldDef<'_> {
    // Still necessary in couple of places
    pub fn is_positional(&self) -> bool {
        self.ident.as_str().as_bytes()[0].is_ascii_digit()
    }
}

/// Fields and constructor IDs of enum variants and structs.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum VariantData<'hir> {
    /// A struct variant.
    ///
    /// E.g., `Bar { .. }` as in `enum Foo { Bar { .. } }`.
    Struct { fields: &'hir [FieldDef<'hir>], recovered: ast::Recovered },
    /// A tuple variant.
    ///
    /// E.g., `Bar(..)` as in `enum Foo { Bar(..) }`.
    Tuple(&'hir [FieldDef<'hir>], #[stable_hasher(ignore)] HirId, LocalDefId),
    /// A unit variant.
    ///
    /// E.g., `Bar = ..` as in `enum Foo { Bar = .. }`.
    Unit(#[stable_hasher(ignore)] HirId, LocalDefId),
}

impl<'hir> VariantData<'hir> {
    /// Return the fields of this variant.
    pub fn fields(&self) -> &'hir [FieldDef<'hir>] {
        match *self {
            VariantData::Struct { fields, .. } | VariantData::Tuple(fields, ..) => fields,
            _ => &[],
        }
    }

    pub fn ctor(&self) -> Option<(CtorKind, HirId, LocalDefId)> {
        match *self {
            VariantData::Tuple(_, hir_id, def_id) => Some((CtorKind::Fn, hir_id, def_id)),
            VariantData::Unit(hir_id, def_id) => Some((CtorKind::Const, hir_id, def_id)),
            VariantData::Struct { .. } => None,
        }
    }

    #[inline]
    pub fn ctor_kind(&self) -> Option<CtorKind> {
        self.ctor().map(|(kind, ..)| kind)
    }

    /// Return the `HirId` of this variant's constructor, if it has one.
    #[inline]
    pub fn ctor_hir_id(&self) -> Option<HirId> {
        self.ctor().map(|(_, hir_id, _)| hir_id)
    }

    /// Return the `LocalDefId` of this variant's constructor, if it has one.
    #[inline]
    pub fn ctor_def_id(&self) -> Option<LocalDefId> {
        self.ctor().map(|(.., def_id)| def_id)
    }
}

// The bodies for items are stored "out of line", in a separate
// hashmap in the `Crate`. Here we just record the hir-id of the item
// so it can fetched later.
#[derive(Copy, Clone, PartialEq, Eq, Encodable, Decodable, Debug, Hash, HashStable_Generic)]
pub struct ItemId {
    pub owner_id: OwnerId,
}

impl ItemId {
    #[inline]
    pub fn hir_id(&self) -> HirId {
        // Items are always HIR owners.
        HirId::make_owner(self.owner_id.def_id)
    }
}

/// An item
///
/// For more details, see the [rust lang reference].
/// Note that the reference does not document nightly-only features.
/// There may be also slight differences in the names and representation of AST nodes between
/// the compiler and the reference.
///
/// [rust lang reference]: https://doc.rust-lang.org/reference/items.html
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct Item<'hir> {
    pub owner_id: OwnerId,
    pub kind: ItemKind<'hir>,
    pub span: Span,
    pub vis_span: Span,
    pub has_delayed_lints: bool,
    /// hint to speed up collection: true if the item is a static or function and has
    /// either an `EiiImpls` or `EiiExternTarget` attribute
    pub eii: bool,
}

impl<'hir> Item<'hir> {
    #[inline]
    pub fn hir_id(&self) -> HirId {
        // Items are always HIR owners.
        HirId::make_owner(self.owner_id.def_id)
    }

    pub fn item_id(&self) -> ItemId {
        ItemId { owner_id: self.owner_id }
    }

    /// Check if this is an [`ItemKind::Enum`], [`ItemKind::Struct`] or
    /// [`ItemKind::Union`].
    pub fn is_adt(&self) -> bool {
        matches!(self.kind, ItemKind::Enum(..) | ItemKind::Struct(..) | ItemKind::Union(..))
    }

    /// Check if this is an [`ItemKind::Struct`] or [`ItemKind::Union`].
    pub fn is_struct_or_union(&self) -> bool {
        matches!(self.kind, ItemKind::Struct(..) | ItemKind::Union(..))
    }

    expect_methods_self_kind! {
        expect_extern_crate, (Option<Symbol>, Ident),
            ItemKind::ExternCrate(s, ident), (*s, *ident);

        expect_use, (&'hir UsePath<'hir>, UseKind), ItemKind::Use(p, uk), (p, *uk);

        expect_static, (Mutability, Ident, &'hir Ty<'hir>, BodyId),
            ItemKind::Static(mutbl, ident, ty, body), (*mutbl, *ident, ty, *body);

        expect_const, (Ident, &'hir Generics<'hir>, &'hir Ty<'hir>, ConstItemRhs<'hir>),
            ItemKind::Const(ident, generics, ty, rhs), (*ident, generics, ty, *rhs);

        expect_fn, (Ident, &FnSig<'hir>, &'hir Generics<'hir>, BodyId),
            ItemKind::Fn { ident, sig, generics, body, .. }, (*ident, sig, generics, *body);

        expect_macro, (Ident, &ast::MacroDef, MacroKinds),
            ItemKind::Macro(ident, def, mk), (*ident, def, *mk);

        expect_mod, (Ident, &'hir Mod<'hir>), ItemKind::Mod(ident, m), (*ident, m);

        expect_foreign_mod, (ExternAbi, &'hir [ForeignItemId]),
            ItemKind::ForeignMod { abi, items }, (*abi, items);

        expect_global_asm, &'hir InlineAsm<'hir>, ItemKind::GlobalAsm { asm, .. }, asm;

        expect_ty_alias, (Ident, &'hir Generics<'hir>, &'hir Ty<'hir>),
            ItemKind::TyAlias(ident, generics, ty), (*ident, generics, ty);

        expect_enum, (Ident, &'hir Generics<'hir>, &EnumDef<'hir>),
            ItemKind::Enum(ident, generics, def), (*ident, generics, def);

        expect_struct, (Ident, &'hir Generics<'hir>, &VariantData<'hir>),
            ItemKind::Struct(ident, generics, data), (*ident, generics, data);

        expect_union, (Ident, &'hir Generics<'hir>, &VariantData<'hir>),
            ItemKind::Union(ident, generics, data), (*ident, generics, data);

        expect_trait,
            (
                Constness,
                IsAuto,
                Safety,
                Ident,
                &'hir Generics<'hir>,
                GenericBounds<'hir>,
                &'hir [TraitItemId]
            ),
            ItemKind::Trait(constness, is_auto, safety, ident, generics, bounds, items),
            (*constness, *is_auto, *safety, *ident, generics, bounds, items);

        expect_trait_alias, (Constness, Ident, &'hir Generics<'hir>, GenericBounds<'hir>),
            ItemKind::TraitAlias(constness, ident, generics, bounds), (*constness, *ident, generics, bounds);

        expect_impl, &Impl<'hir>, ItemKind::Impl(imp), imp;
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[derive(Encodable, Decodable, HashStable_Generic, Default)]
pub enum Safety {
    /// This is the default variant, because the compiler messing up
    /// metadata encoding and failing to encode a `Safe` flag, means
    /// downstream crates think a thing is `Unsafe` instead of silently
    /// treating an unsafe thing as safe.
    #[default]
    Unsafe,
    Safe,
}

impl Safety {
    pub fn prefix_str(self) -> &'static str {
        match self {
            Self::Unsafe => "unsafe ",
            Self::Safe => "",
        }
    }

    #[inline]
    pub fn is_unsafe(self) -> bool {
        !self.is_safe()
    }

    #[inline]
    pub fn is_safe(self) -> bool {
        match self {
            Self::Unsafe => false,
            Self::Safe => true,
        }
    }
}

impl fmt::Display for Safety {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match *self {
            Self::Unsafe => "unsafe",
            Self::Safe => "safe",
        })
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Encodable, Decodable, HashStable_Generic)]
#[derive(Default)]
pub enum Constness {
    #[default]
    Const,
    NotConst,
}

impl fmt::Display for Constness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match *self {
            Self::Const => "const",
            Self::NotConst => "non-const",
        })
    }
}

/// The actual safety specified in syntax. We may treat
/// its safety different within the type system to create a
/// "sound by default" system that needs checking this enum
/// explicitly to allow unsafe operations.
#[derive(Copy, Clone, Debug, HashStable_Generic, PartialEq, Eq)]
pub enum HeaderSafety {
    /// A safe function annotated with `#[target_features]`.
    /// The type system treats this function as an unsafe function,
    /// but safety checking will check this enum to treat it as safe
    /// and allowing calling other safe target feature functions with
    /// the same features without requiring an additional unsafe block.
    SafeTargetFeatures,
    Normal(Safety),
}

impl From<Safety> for HeaderSafety {
    fn from(v: Safety) -> Self {
        Self::Normal(v)
    }
}

#[derive(Copy, Clone, Debug, HashStable_Generic)]
pub struct FnHeader {
    pub safety: HeaderSafety,
    pub constness: Constness,
    pub asyncness: IsAsync,
    pub abi: ExternAbi,
}

impl FnHeader {
    pub fn is_async(&self) -> bool {
        matches!(self.asyncness, IsAsync::Async(_))
    }

    pub fn is_const(&self) -> bool {
        matches!(self.constness, Constness::Const)
    }

    pub fn is_unsafe(&self) -> bool {
        self.safety().is_unsafe()
    }

    pub fn is_safe(&self) -> bool {
        self.safety().is_safe()
    }

    pub fn safety(&self) -> Safety {
        match self.safety {
            HeaderSafety::SafeTargetFeatures => Safety::Unsafe,
            HeaderSafety::Normal(safety) => safety,
        }
    }
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum ItemKind<'hir> {
    /// An `extern crate` item, with optional *original* crate name if the crate was renamed.
    ///
    /// E.g., `extern crate foo` or `extern crate foo_bar as foo`.
    ExternCrate(Option<Symbol>, Ident),

    /// `use foo::bar::*;` or `use foo::bar::baz as quux;`
    ///
    /// or just
    ///
    /// `use foo::bar::baz;` (with `as baz` implicitly on the right).
    Use(&'hir UsePath<'hir>, UseKind),

    /// A `static` item.
    Static(Mutability, Ident, &'hir Ty<'hir>, BodyId),
    /// A `const` item.
    Const(Ident, &'hir Generics<'hir>, &'hir Ty<'hir>, ConstItemRhs<'hir>),
    /// A function declaration.
    Fn {
        sig: FnSig<'hir>,
        ident: Ident,
        generics: &'hir Generics<'hir>,
        body: BodyId,
        /// Whether this function actually has a body.
        /// For functions without a body, `body` is synthesized (to avoid ICEs all over the
        /// compiler), but that code should never be translated.
        has_body: bool,
    },
    /// A MBE macro definition (`macro_rules!` or `macro`).
    Macro(Ident, &'hir ast::MacroDef, MacroKinds),
    /// A module.
    Mod(Ident, &'hir Mod<'hir>),
    /// An external module, e.g. `extern { .. }`.
    ForeignMod { abi: ExternAbi, items: &'hir [ForeignItemId] },
    /// Module-level inline assembly (from `global_asm!`).
    GlobalAsm {
        asm: &'hir InlineAsm<'hir>,
        /// A fake body which stores typeck results for the global asm's sym_fn
        /// operands, which are represented as path expressions. This body contains
        /// a single [`ExprKind::InlineAsm`] which points to the asm in the field
        /// above, and which is typechecked like a inline asm expr just for the
        /// typeck results.
        fake_body: BodyId,
    },
    /// A type alias, e.g., `type Foo = Bar<u8>`.
    TyAlias(Ident, &'hir Generics<'hir>, &'hir Ty<'hir>),
    /// An enum definition, e.g., `enum Foo<A, B> { C<A>, D<B> }`.
    Enum(Ident, &'hir Generics<'hir>, EnumDef<'hir>),
    /// A struct definition, e.g., `struct Foo<A> {x: A}`.
    Struct(Ident, &'hir Generics<'hir>, VariantData<'hir>),
    /// A union definition, e.g., `union Foo<A, B> {x: A, y: B}`.
    Union(Ident, &'hir Generics<'hir>, VariantData<'hir>),
    /// A trait definition.
    Trait(
        Constness,
        IsAuto,
        Safety,
        Ident,
        &'hir Generics<'hir>,
        GenericBounds<'hir>,
        &'hir [TraitItemId],
    ),
    /// A trait alias.
    TraitAlias(Constness, Ident, &'hir Generics<'hir>, GenericBounds<'hir>),

    /// An implementation, e.g., `impl<A> Trait for Foo { .. }`.
    Impl(Impl<'hir>),
}

/// Represents an impl block declaration.
///
/// E.g., `impl $Type { .. }` or `impl $Trait for $Type { .. }`
/// Refer to [`ImplItem`] for an associated item within an impl block.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct Impl<'hir> {
    pub generics: &'hir Generics<'hir>,
    pub of_trait: Option<&'hir TraitImplHeader<'hir>>,
    pub self_ty: &'hir Ty<'hir>,
    pub items: &'hir [ImplItemId],
    pub constness: Constness,
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct TraitImplHeader<'hir> {
    pub safety: Safety,
    pub polarity: ImplPolarity,
    pub defaultness: Defaultness,
    // We do not put a `Span` in `Defaultness` because it breaks foreign crate metadata
    // decoding as `Span`s cannot be decoded when a `Session` is not available.
    pub defaultness_span: Option<Span>,
    pub trait_ref: TraitRef<'hir>,
}

impl ItemKind<'_> {
    pub fn ident(&self) -> Option<Ident> {
        match *self {
            ItemKind::ExternCrate(_, ident)
            | ItemKind::Use(_, UseKind::Single(ident))
            | ItemKind::Static(_, ident, ..)
            | ItemKind::Const(ident, ..)
            | ItemKind::Fn { ident, .. }
            | ItemKind::Macro(ident, ..)
            | ItemKind::Mod(ident, ..)
            | ItemKind::TyAlias(ident, ..)
            | ItemKind::Enum(ident, ..)
            | ItemKind::Struct(ident, ..)
            | ItemKind::Union(ident, ..)
            | ItemKind::Trait(_, _, _, ident, ..)
            | ItemKind::TraitAlias(_, ident, ..) => Some(ident),

            ItemKind::Use(_, UseKind::Glob | UseKind::ListStem)
            | ItemKind::ForeignMod { .. }
            | ItemKind::GlobalAsm { .. }
            | ItemKind::Impl(_) => None,
        }
    }

    pub fn generics(&self) -> Option<&Generics<'_>> {
        Some(match self {
            ItemKind::Fn { generics, .. }
            | ItemKind::TyAlias(_, generics, _)
            | ItemKind::Const(_, generics, _, _)
            | ItemKind::Enum(_, generics, _)
            | ItemKind::Struct(_, generics, _)
            | ItemKind::Union(_, generics, _)
            | ItemKind::Trait(_, _, _, _, generics, _, _)
            | ItemKind::TraitAlias(_, _, generics, _)
            | ItemKind::Impl(Impl { generics, .. }) => generics,
            _ => return None,
        })
    }

    pub fn recovered(&self) -> bool {
        match self {
            ItemKind::Struct(
                _,
                _,
                VariantData::Struct { recovered: ast::Recovered::Yes(_), .. },
            ) => true,
            ItemKind::Union(
                _,
                _,
                VariantData::Struct { recovered: ast::Recovered::Yes(_), .. },
            ) => true,
            ItemKind::Enum(_, _, def) => def.variants.iter().any(|v| match v.data {
                VariantData::Struct { recovered: ast::Recovered::Yes(_), .. } => true,
                _ => false,
            }),
            _ => false,
        }
    }
}

// The bodies for items are stored "out of line", in a separate
// hashmap in the `Crate`. Here we just record the hir-id of the item
// so it can fetched later.
#[derive(Copy, Clone, PartialEq, Eq, Encodable, Decodable, Debug, HashStable_Generic)]
pub struct ForeignItemId {
    pub owner_id: OwnerId,
}

impl ForeignItemId {
    #[inline]
    pub fn hir_id(&self) -> HirId {
        // Items are always HIR owners.
        HirId::make_owner(self.owner_id.def_id)
    }
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct ForeignItem<'hir> {
    pub ident: Ident,
    pub kind: ForeignItemKind<'hir>,
    pub owner_id: OwnerId,
    pub span: Span,
    pub vis_span: Span,
    pub has_delayed_lints: bool,
}

impl ForeignItem<'_> {
    #[inline]
    pub fn hir_id(&self) -> HirId {
        // Items are always HIR owners.
        HirId::make_owner(self.owner_id.def_id)
    }

    pub fn foreign_item_id(&self) -> ForeignItemId {
        ForeignItemId { owner_id: self.owner_id }
    }
}

/// An item within an `extern` block.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum ForeignItemKind<'hir> {
    /// A foreign function.
    ///
    /// All argument idents are actually always present (i.e. `Some`), but
    /// `&[Option<Ident>]` is used because of code paths shared with `TraitFn`
    /// and `FnPtrTy`. The sharing is due to all of these cases not allowing
    /// arbitrary patterns for parameters.
    Fn(FnSig<'hir>, &'hir [Option<Ident>], &'hir Generics<'hir>),
    /// A foreign static item (`static ext: u8`).
    Static(&'hir Ty<'hir>, Mutability, Safety),
    /// A foreign type.
    Type,
}

/// A variable captured by a closure.
#[derive(Debug, Copy, Clone, HashStable_Generic)]
pub struct Upvar {
    /// First span where it is accessed (there can be multiple).
    pub span: Span,
}

// The TraitCandidate's import_ids is empty if the trait is defined in the same module, and
// has length > 0 if the trait is found through an chain of imports, starting with the
// import/use statement in the scope where the trait is used.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct TraitCandidate<'hir> {
    pub def_id: DefId,
    pub import_ids: &'hir [LocalDefId],
    // Indicates whether this trait candidate is ambiguously glob imported
    // in it's scope. Related to the AMBIGUOUS_GLOB_IMPORTED_TRAITS lint.
    // If this is set to true and the trait is used as a result of method lookup, this
    // lint is thrown.
    pub lint_ambiguous: bool,
}

#[derive(Copy, Clone, Debug, HashStable_Generic)]
