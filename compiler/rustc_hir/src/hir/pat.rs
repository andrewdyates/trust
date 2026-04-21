// tRust: split from hir.rs for maintainability
use super::*;


#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct Closure<'hir> {
    pub def_id: LocalDefId,
    pub binder: ClosureBinder,
    pub constness: Constness,
    pub capture_clause: CaptureBy,
    pub bound_generic_params: &'hir [GenericParam<'hir>],
    pub fn_decl: &'hir FnDecl<'hir>,
    pub body: BodyId,
    /// The span of the declaration block: 'move |...| -> ...'
    pub fn_decl_span: Span,
    /// The span of the argument block `|...|`
    pub fn_arg_span: Option<Span>,
    pub kind: ClosureKind,
}

#[derive(Clone, PartialEq, Eq, Debug, Copy, Hash, HashStable_Generic, Encodable, Decodable)]
pub enum ClosureKind {
    /// This is a plain closure expression.
    Closure,
    /// This is a coroutine expression -- i.e. a closure expression in which
    /// we've found a `yield`. These can arise either from "plain" coroutine
    ///  usage (e.g. `let x = || { yield (); }`) or from a desugared expression
    /// (e.g. `async` and `gen` blocks).
    Coroutine(CoroutineKind),
    /// This is a coroutine-closure, which is a special sugared closure that
    /// returns one of the sugared coroutine (`async`/`gen`/`async gen`). It
    /// additionally allows capturing the coroutine's upvars by ref, and therefore
    /// needs to be specially treated during analysis and borrowck.
    CoroutineClosure(CoroutineDesugaring),
}

/// A block of statements `{ .. }`, which may have a label (in this case the
/// `targeted_by_break` field will be `true`) and may be `unsafe` by means of
/// the `rules` being anything but `DefaultBlock`.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct Block<'hir> {
    /// Statements in a block.
    pub stmts: &'hir [Stmt<'hir>],
    /// An expression at the end of the block
    /// without a semicolon, if any.
    pub expr: Option<&'hir Expr<'hir>>,
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    // SAFETY: Documentation only; this field records whether a parsed block used
    // `unsafe`, and no unsafe operation is performed here.
    /// Distinguishes between `unsafe { ... }` and `{ ... }`.
    pub rules: BlockCheckMode,
    /// The span includes the curly braces `{` and `}` around the block.
    pub span: Span,
    /// If true, then there may exist `break 'a` values that aim to
    /// break out of this block early.
    /// Used by `'label: {}` blocks and by `try {}` blocks.
    pub targeted_by_break: bool,
}

impl<'hir> Block<'hir> {
    pub fn innermost_block(&self) -> &Block<'hir> {
        let mut block = self;
        while let Some(Expr { kind: ExprKind::Block(inner_block, _), .. }) = block.expr {
            block = inner_block;
        }
        block
    }
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct TyFieldPath {
    pub variant: Option<Ident>,
    pub field: Ident,
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct TyPat<'hir> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub kind: TyPatKind<'hir>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct Pat<'hir> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub kind: PatKind<'hir>,
    pub span: Span,
    /// Whether to use default binding modes.
    /// At present, this is false only for destructuring assignment.
    pub default_binding_modes: bool,
}

impl<'hir> Pat<'hir> {
    fn walk_short_(&self, it: &mut impl FnMut(&Pat<'hir>) -> bool) -> bool {
        if !it(self) {
            return false;
        }

        use PatKind::*;
        match self.kind {
            Missing => unreachable!(),
            Wild | Never | Expr(_) | Range(..) | Binding(.., None) | Err(_) => true,
            Box(s) | Deref(s) | Ref(s, _, _) | Binding(.., Some(s)) | Guard(s, _) => {
                s.walk_short_(it)
            }
            Struct(_, fields, _) => fields.iter().all(|field| field.pat.walk_short_(it)),
            TupleStruct(_, s, _) | Tuple(s, _) | Or(s) => s.iter().all(|p| p.walk_short_(it)),
            Slice(before, slice, after) => {
                before.iter().chain(slice).chain(after.iter()).all(|p| p.walk_short_(it))
            }
        }
    }

    /// Walk the pattern in left-to-right order,
    /// short circuiting (with `.all(..)`) if `false` is returned.
    ///
    /// Note that when visiting e.g. `Tuple(ps)`,
    /// if visiting `ps[0]` returns `false`,
    /// then `ps[1]` will not be visited.
    pub fn walk_short(&self, mut it: impl FnMut(&Pat<'hir>) -> bool) -> bool {
        self.walk_short_(&mut it)
    }

    fn walk_(&self, it: &mut impl FnMut(&Pat<'hir>) -> bool) {
        if !it(self) {
            return;
        }

        use PatKind::*;
        match self.kind {
            Missing | Wild | Never | Expr(_) | Range(..) | Binding(.., None) | Err(_) => {}
            Box(s) | Deref(s) | Ref(s, _, _) | Binding(.., Some(s)) | Guard(s, _) => s.walk_(it),
            Struct(_, fields, _) => fields.iter().for_each(|field| field.pat.walk_(it)),
            TupleStruct(_, s, _) | Tuple(s, _) | Or(s) => s.iter().for_each(|p| p.walk_(it)),
            Slice(before, slice, after) => {
                before.iter().chain(slice).chain(after.iter()).for_each(|p| p.walk_(it))
            }
        }
    }

    /// Walk the pattern in left-to-right order.
    ///
    /// If `it(pat)` returns `false`, the children are not visited.
    pub fn walk(&self, mut it: impl FnMut(&Pat<'hir>) -> bool) {
        self.walk_(&mut it)
    }

    /// Walk the pattern in left-to-right order.
    ///
    /// If you always want to recurse, prefer this method over `walk`.
    pub fn walk_always(&self, mut it: impl FnMut(&Pat<'_>)) {
        self.walk(|p| {
            it(p);
            true
        })
    }

    /// Whether this a never pattern.
    pub fn is_never_pattern(&self) -> bool {
        let mut is_never_pattern = false;
        self.walk(|pat| match &pat.kind {
            PatKind::Never => {
                is_never_pattern = true;
                false
            }
            PatKind::Or(s) => {
                is_never_pattern = s.iter().all(|p| p.is_never_pattern());
                false
            }
            _ => true,
        });
        is_never_pattern
    }

    /// Whether this pattern constitutes a read of value of the scrutinee that
    /// it is matching against. This is used to determine whether we should
    /// perform `NeverToAny` coercions.
    ///
    /// See [`expr_guaranteed_to_constitute_read_for_never`][m] for the nuances of
    /// what happens when this returns true.
    ///
    /// [m]: ../../rustc_middle/ty/struct.TyCtxt.html#method.expr_guaranteed_to_constitute_read_for_never
    pub fn is_guaranteed_to_constitute_read_for_never(&self) -> bool {
        match self.kind {
            // Does not constitute a read.
            PatKind::Wild => false,

            // The guard cannot affect if we make a read or not (it runs after the inner pattern
            // has matched), therefore it's irrelevant.
            PatKind::Guard(pat, _) => pat.is_guaranteed_to_constitute_read_for_never(),

            // This is unnecessarily restrictive when the pattern that doesn't
            // constitute a read is unreachable.
            //
            // For example `match *never_ptr { value => {}, _ => {} }` or
            // `match *never_ptr { _ if false => {}, value => {} }`.
            //
            // It is however fine to be restrictive here; only returning `true`
            // can lead to unsoundness.
            PatKind::Or(subpats) => {
                subpats.iter().all(|pat| pat.is_guaranteed_to_constitute_read_for_never())
            }

            // Does constitute a read, since it is equivalent to a discriminant read.
            PatKind::Never => true,

            // All of these constitute a read, or match on something that isn't `!`,
            // which would require a `NeverToAny` coercion.
            PatKind::Missing
            | PatKind::Binding(_, _, _, _)
            | PatKind::Struct(_, _, _)
            | PatKind::TupleStruct(_, _, _)
            | PatKind::Tuple(_, _)
            | PatKind::Box(_)
            | PatKind::Ref(_, _, _)
            | PatKind::Deref(_)
            | PatKind::Expr(_)
            | PatKind::Range(_, _, _)
            | PatKind::Slice(_, _, _)
            | PatKind::Err(_) => true,
        }
    }
}

/// A single field in a struct pattern.
///
/// Patterns like the fields of Foo `{ x, ref y, ref mut z }`
/// are treated the same as` x: x, y: ref y, z: ref mut z`,
/// except `is_shorthand` is true.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct PatField<'hir> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    /// The identifier for the field.
    pub ident: Ident,
    /// The pattern the field is destructured to.
    pub pat: &'hir Pat<'hir>,
    pub is_shorthand: bool,
    pub span: Span,
}

#[derive(Copy, Clone, PartialEq, Debug, HashStable_Generic, Hash, Eq, Encodable, Decodable)]
pub enum RangeEnd {
    Included,
    Excluded,
}

impl fmt::Display for RangeEnd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            RangeEnd::Included => "..=",
            RangeEnd::Excluded => "..",
        })
    }
}

// Equivalent to `Option<usize>`. That type takes up 16 bytes on 64-bit, but
// this type only takes up 4 bytes, at the cost of being restricted to a
// maximum value of `u32::MAX - 1`. In practice, this is more than enough.
#[derive(Clone, Copy, PartialEq, Eq, Hash, HashStable_Generic)]
pub struct DotDotPos(u32);

impl DotDotPos {
    /// Panics if n >= u32::MAX.
    pub fn new(n: Option<usize>) -> Self {
        match n {
            Some(n) => {
                assert!(n < u32::MAX as usize);
                Self(n as u32)
            }
            None => Self(u32::MAX),
        }
    }

    pub fn as_opt_usize(&self) -> Option<usize> {
        if self.0 == u32::MAX { None } else { Some(self.0 as usize) }
    }
}

impl fmt::Debug for DotDotPos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_opt_usize().fmt(f)
    }
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct PatExpr<'hir> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub span: Span,
    pub kind: PatExprKind<'hir>,
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum PatExprKind<'hir> {
    Lit {
        lit: Lit,
        negated: bool,
    },
    /// A path pattern for a unit struct/variant or a (maybe-associated) constant.
    Path(QPath<'hir>),
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum TyPatKind<'hir> {
    /// A range pattern (e.g., `1..=2` or `1..2`).
    Range(&'hir ConstArg<'hir>, &'hir ConstArg<'hir>),

    /// A pattern that excludes null pointers
    NotNull,

    /// A list of patterns where only one needs to be satisfied
    Or(&'hir [TyPat<'hir>]),

    /// A placeholder for a pattern that wasn't well formed in some way.
    Err(ErrorGuaranteed),
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum PatKind<'hir> {
    /// A missing pattern, e.g. for an anonymous param in a bare fn like `fn f(u32)`.
    Missing,

    /// Represents a wildcard pattern (i.e., `_`).
    Wild,

    /// A fresh binding `ref mut binding @ OPT_SUBPATTERN`.
    /// The `HirId` is the canonical ID for the variable being bound,
    /// (e.g., in `Ok(x) | Err(x)`, both `x` use the same canonical ID),
    /// which is the pattern ID of the first `x`.
    ///
    /// The `BindingMode` is what's provided by the user, before match
    /// ergonomics are applied. For the binding mode actually in use,
    /// see [`TypeckResults::extract_binding_mode`].
    ///
    /// [`TypeckResults::extract_binding_mode`]: ../../rustc_middle/ty/struct.TypeckResults.html#method.extract_binding_mode
    Binding(BindingMode, HirId, Ident, Option<&'hir Pat<'hir>>),

    /// A struct or struct variant pattern (e.g., `Variant {x, y, ..}`).
    /// The `Option` contains the span of a possible `..`.
    Struct(QPath<'hir>, &'hir [PatField<'hir>], Option<Span>),

    /// A tuple struct/variant pattern `Variant(x, y, .., z)`.
    /// If the `..` pattern fragment is present, then `DotDotPos` denotes its position.
    /// `0 <= position <= subpats.len()`
    TupleStruct(QPath<'hir>, &'hir [Pat<'hir>], DotDotPos),

    /// An or-pattern `A | B | C`.
    /// Invariant: `pats.len() >= 2`.
    Or(&'hir [Pat<'hir>]),

    /// A never pattern `!`.
    Never,

    /// A tuple pattern (e.g., `(a, b)`).
    /// If the `..` pattern fragment is present, then `DotDotPos` denotes its position.
    /// `0 <= position <= subpats.len()`
    Tuple(&'hir [Pat<'hir>], DotDotPos),

    /// A `box` pattern.
    Box(&'hir Pat<'hir>),

    /// A `deref` pattern (currently `deref!()` macro-based syntax).
    Deref(&'hir Pat<'hir>),

    /// A reference pattern (e.g., `&mut (a, b)`).
    Ref(&'hir Pat<'hir>, Pinnedness, Mutability),

    /// A literal, const block or path.
    Expr(&'hir PatExpr<'hir>),

    /// A guard pattern (e.g., `x if guard(x)`).
    Guard(&'hir Pat<'hir>, &'hir Expr<'hir>),

    /// A range pattern (e.g., `1..=2` or `1..2`).
    Range(Option<&'hir PatExpr<'hir>>, Option<&'hir PatExpr<'hir>>, RangeEnd),

    /// A slice pattern, `[before_0, ..., before_n, (slice, after_0, ..., after_n)?]`.
    ///
    /// Here, `slice` is lowered from the syntax `($binding_mode $ident @)? ..`.
    /// If `slice` exists, then `after` can be non-empty.
    ///
    /// The representation for e.g., `[a, b, .., c, d]` is:
    /// ```ignore (illustrative)
    /// PatKind::Slice([Binding(a), Binding(b)], Some(Wild), [Binding(c), Binding(d)])
    /// ```
    Slice(&'hir [Pat<'hir>], Option<&'hir Pat<'hir>>, &'hir [Pat<'hir>]),

    /// A placeholder for a pattern that wasn't well formed in some way.
    Err(ErrorGuaranteed),
}
