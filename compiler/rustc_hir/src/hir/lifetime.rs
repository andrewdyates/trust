// tRust: split from hir.rs for maintainability
use super::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq, HashStable_Generic)]
pub enum AngleBrackets {
    /// E.g. `Path`.
    Missing,
    /// E.g. `Path<>`.
    Empty,
    /// E.g. `Path<T>`.
    Full,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, HashStable_Generic)]
pub enum LifetimeSource {
    /// E.g. `&Type`, `&'_ Type`, `&'a Type`, `&mut Type`, `&'_ mut Type`, `&'a mut Type`
    Reference,

    /// E.g. `ContainsLifetime`, `ContainsLifetime<>`, `ContainsLifetime<'_>`,
    /// `ContainsLifetime<'a>`
    Path { angle_brackets: AngleBrackets },

    /// E.g. `impl Trait + '_`, `impl Trait + 'a`
    OutlivesBound,

    /// E.g. `impl Trait + use<'_>`, `impl Trait + use<'a>`
    PreciseCapturing,

    /// Other usages which have not yet been categorized. Feel free to
    /// add new sources that you find useful.
    ///
    /// Some non-exhaustive examples:
    /// - `where T: 'a`
    /// - `fn(_: dyn Trait + 'a)`
    Other,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, HashStable_Generic)]
pub enum LifetimeSyntax {
    /// E.g. `&Type`, `ContainsLifetime`
    Implicit,

    /// E.g. `&'_ Type`, `ContainsLifetime<'_>`, `impl Trait + '_`, `impl Trait + use<'_>`
    ExplicitAnonymous,

    /// E.g. `&'a Type`, `ContainsLifetime<'a>`, `impl Trait + 'a`, `impl Trait + use<'a>`
    ExplicitBound,
}

impl From<Ident> for LifetimeSyntax {
    fn from(ident: Ident) -> Self {
        let name = ident.name;

        if name == sym::empty {
            unreachable!("A lifetime name should never be empty");
        } else if name == kw::UnderscoreLifetime {
            LifetimeSyntax::ExplicitAnonymous
        } else {
            debug_assert!(name.as_str().starts_with('\''));
            LifetimeSyntax::ExplicitBound
        }
    }
}

/// A lifetime. The valid field combinations are non-obvious and not all
/// combinations are possible. The following example shows some of
/// them. See also the comments on `LifetimeKind` and `LifetimeSource`.
///
/// ```
/// #[repr(C)]
/// struct S<'a>(&'a u32);       // res=Param, name='a, source=Reference, syntax=ExplicitBound
/// unsafe extern "C" {
///     fn f1(s: S);             // res=Param, name='_, source=Path, syntax=Implicit
///     fn f2(s: S<'_>);         // res=Param, name='_, source=Path, syntax=ExplicitAnonymous
///     fn f3<'a>(s: S<'a>);     // res=Param, name='a, source=Path, syntax=ExplicitBound
/// }
///
/// struct St<'a> { x: &'a u32 } // res=Param, name='a, source=Reference, syntax=ExplicitBound
/// fn f() {
///     _ = St { x: &0 };        // res=Infer, name='_, source=Path, syntax=Implicit
///     _ = St::<'_> { x: &0 };  // res=Infer, name='_, source=Path, syntax=ExplicitAnonymous
/// }
///
/// struct Name<'a>(&'a str);    // res=Param,  name='a, source=Reference, syntax=ExplicitBound
/// const A: Name = Name("a");   // res=Static, name='_, source=Path, syntax=Implicit
/// const B: &str = "";          // res=Static, name='_, source=Reference, syntax=Implicit
/// static C: &'_ str = "";      // res=Static, name='_, source=Reference, syntax=ExplicitAnonymous
/// static D: &'static str = ""; // res=Static, name='static, source=Reference, syntax=ExplicitBound
///
/// trait Tr {}
/// fn tr(_: Box<dyn Tr>) {}     // res=ImplicitObjectLifetimeDefault, name='_, source=Other, syntax=Implicit
///
/// fn capture_outlives<'a>() ->
///     impl FnOnce() + 'a       // res=Param, ident='a, source=OutlivesBound, syntax=ExplicitBound
/// {
///     || {}
/// }
///
/// fn capture_precise<'a>() ->
///     impl FnOnce() + use<'a>  // res=Param, ident='a, source=PreciseCapturing, syntax=ExplicitBound
/// {
///     || {}
/// }
///
/// // (commented out because these cases trigger errors)
/// // struct S1<'a>(&'a str);   // res=Param, name='a, source=Reference, syntax=ExplicitBound
/// // struct S2(S1);            // res=Error, name='_, source=Path, syntax=Implicit
/// // struct S3(S1<'_>);        // res=Error, name='_, source=Path, syntax=ExplicitAnonymous
/// // struct S4(S1<'a>);        // res=Error, name='a, source=Path, syntax=ExplicitBound
/// ```
///
/// Some combinations that cannot occur are `LifetimeSyntax::Implicit` with
/// `LifetimeSource::OutlivesBound` or `LifetimeSource::PreciseCapturing`
/// — there's no way to "elide" these lifetimes.
#[derive(Debug, Copy, Clone, HashStable_Generic)]
// Raise the alignment to at least 4 bytes.
// This is relied on in other parts of the compiler (for pointer tagging):
// <https://github.com/rust-lang/rust/blob/ce5fdd7d42aba9a2925692e11af2bd39cf37798a/compiler/rustc_data_structures/src/tagged_ptr.rs#L163>
// Removing this `repr(4)` will cause the compiler to not build on platforms
// like `m68k` Linux, where the alignment of u32 and usize is only 2.
// Since `repr(align)` may only raise alignment, this has no effect on
// platforms where the alignment is already sufficient.
#[repr(align(4))]
pub struct Lifetime {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,

    /// Either a named lifetime definition (e.g. `'a`, `'static`) or an
    /// anonymous lifetime (`'_`, either explicitly written, or inserted for
    /// things like `&type`).
    pub ident: Ident,

    /// Semantics of this lifetime.
    pub kind: LifetimeKind,

    /// The context in which the lifetime occurred. See `Lifetime::suggestion`
    /// for example use.
    pub source: LifetimeSource,

    /// The syntax that the user used to declare this lifetime. See
    /// `Lifetime::suggestion` for example use.
    pub syntax: LifetimeSyntax,
}

#[derive(Debug, Copy, Clone, HashStable_Generic)]
pub enum ParamName {
    /// Some user-given name like `T` or `'x`.
    Plain(Ident),

    /// Indicates an illegal name was given and an error has been
    /// reported (so we should squelch other derived errors).
    ///
    /// Occurs when, e.g., `'_` is used in the wrong place, or a
    /// lifetime name is duplicated.
    Error(Ident),

    /// Synthetic name generated when user elided a lifetime in an impl header.
    ///
    /// E.g., the lifetimes in cases like these:
    /// ```ignore (fragment)
    /// impl Foo for &u32
    /// impl Foo<'_> for u32
    /// ```
    /// in that case, we rewrite to
    /// ```ignore (fragment)
    /// impl<'f> Foo for &'f u32
    /// impl<'f> Foo<'f> for u32
    /// ```
    /// where `'f` is something like `Fresh(0)`. The indices are
    /// unique per impl, but not necessarily continuous.
    Fresh,
}

impl ParamName {
    pub fn ident(&self) -> Ident {
        match *self {
            ParamName::Plain(ident) | ParamName::Error(ident) => ident,
            ParamName::Fresh => Ident::with_dummy_span(kw::UnderscoreLifetime),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, HashStable_Generic)]
pub enum LifetimeKind {
    /// User-given names or fresh (synthetic) names.
    Param(LocalDefId),

    /// Implicit lifetime in a context like `dyn Foo`. This is
    /// distinguished from implicit lifetimes elsewhere because the
    /// lifetime that they default to must appear elsewhere within the
    /// enclosing type. This means that, in an `impl Trait` context, we
    /// don't have to create a parameter for them. That is, `impl
    /// Trait<Item = &u32>` expands to an opaque type like `type
    /// Foo<'a> = impl Trait<Item = &'a u32>`, but `impl Trait<item =
    /// dyn Bar>` expands to `type Foo = impl Trait<Item = dyn Bar +
    /// 'static>`. The latter uses `ImplicitObjectLifetimeDefault` so
    /// that surrounding code knows not to create a lifetime
    /// parameter.
    ImplicitObjectLifetimeDefault,

    /// Indicates an error during lowering (usually `'_` in wrong place)
    /// that was already reported.
    Error(ErrorGuaranteed),

    /// User wrote an anonymous lifetime, either `'_` or nothing (which gets
    /// converted to `'_`). The semantics of this lifetime should be inferred
    /// by typechecking code.
    Infer,

    /// User wrote `'static` or nothing (which gets converted to `'_`).
    Static,
}

impl LifetimeKind {
    fn is_elided(&self) -> bool {
        match self {
            LifetimeKind::ImplicitObjectLifetimeDefault | LifetimeKind::Infer => true,

            // It might seem surprising that `Fresh` counts as not *elided*
            // -- but this is because, as far as the code in the compiler is
            // concerned -- `Fresh` variants act equivalently to "some fresh name".
            // They correspond to early-bound regions on an impl, in other words.
            LifetimeKind::Error(..) | LifetimeKind::Param(..) | LifetimeKind::Static => false,
        }
    }
}

impl fmt::Display for Lifetime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.ident.name.fmt(f)
    }
}

impl Lifetime {
    pub fn new(
        hir_id: HirId,
        ident: Ident,
        kind: LifetimeKind,
        source: LifetimeSource,
        syntax: LifetimeSyntax,
    ) -> Lifetime {
        let lifetime = Lifetime { hir_id, ident, kind, source, syntax };

        // Sanity check: elided lifetimes form a strict subset of anonymous lifetimes.
        #[cfg(debug_assertions)]
        match (lifetime.is_elided(), lifetime.is_anonymous()) {
            (false, false) => {} // e.g. `'a`
            (false, true) => {}  // e.g. explicit `'_`
            (true, true) => {}   // e.g. `&x`
            (true, false) => panic!("bad Lifetime"),
        }

        lifetime
    }

    pub fn is_elided(&self) -> bool {
        self.kind.is_elided()
    }

    pub fn is_anonymous(&self) -> bool {
        self.ident.name == kw::UnderscoreLifetime
    }

    pub fn is_implicit(&self) -> bool {
        matches!(self.syntax, LifetimeSyntax::Implicit)
    }

    pub fn is_static(&self) -> bool {
        self.kind == LifetimeKind::Static
    }

    pub fn suggestion(&self, new_lifetime: &str) -> (Span, String) {
        use LifetimeSource::*;
        use LifetimeSyntax::*;

        debug_assert!(new_lifetime.starts_with('\''));

        match (self.syntax, self.source) {
            // The user wrote `'a` or `'_`.
            (ExplicitBound | ExplicitAnonymous, _) => (self.ident.span, format!("{new_lifetime}")),

            // The user wrote `Path<T>`, and omitted the `'_,`.
            (Implicit, Path { angle_brackets: AngleBrackets::Full }) => {
                (self.ident.span, format!("{new_lifetime}, "))
            }

            // The user wrote `Path<>`, and omitted the `'_`..
            (Implicit, Path { angle_brackets: AngleBrackets::Empty }) => {
                (self.ident.span, format!("{new_lifetime}"))
            }

            // The user wrote `Path` and omitted the `<'_>`.
            (Implicit, Path { angle_brackets: AngleBrackets::Missing }) => {
                (self.ident.span.shrink_to_hi(), format!("<{new_lifetime}>"))
            }

            // The user wrote `&type` or `&mut type`.
            (Implicit, Reference) => (self.ident.span, format!("{new_lifetime} ")),

            (Implicit, source) => {
                unreachable!("can't suggest for a implicit lifetime of {source:?}")
            }
        }
    }
}
