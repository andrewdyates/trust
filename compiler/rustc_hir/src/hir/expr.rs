// tRust: split from hir.rs for maintainability
use super::*;


/// The type of source expression that caused this coroutine to be created.
#[derive(Clone, PartialEq, Eq, Debug, Copy, Hash, HashStable_Generic, Encodable, Decodable)]
pub enum CoroutineKind {
    /// A coroutine that comes from a desugaring.
    Desugared(CoroutineDesugaring, CoroutineSource),

    /// A coroutine literal created via a `yield` inside a closure.
    Coroutine(Movability),
}

impl CoroutineKind {
    pub fn movability(self) -> Movability {
        match self {
            CoroutineKind::Desugared(CoroutineDesugaring::Async, _)
            | CoroutineKind::Desugared(CoroutineDesugaring::AsyncGen, _) => Movability::Static,
            CoroutineKind::Desugared(CoroutineDesugaring::Gen, _) => Movability::Movable,
            CoroutineKind::Coroutine(mov) => mov,
        }
    }

    pub fn is_fn_like(self) -> bool {
        matches!(self, CoroutineKind::Desugared(_, CoroutineSource::Fn))
    }

    pub fn to_plural_string(&self) -> String {
        match self {
            CoroutineKind::Desugared(d, CoroutineSource::Fn) => format!("{d:#}fn bodies"),
            CoroutineKind::Desugared(d, CoroutineSource::Block) => format!("{d:#}blocks"),
            CoroutineKind::Desugared(d, CoroutineSource::Closure) => format!("{d:#}closure bodies"),
            CoroutineKind::Coroutine(_) => "coroutines".to_string(),
        }
    }
}

impl fmt::Display for CoroutineKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CoroutineKind::Desugared(d, k) => {
                d.fmt(f)?;
                k.fmt(f)
            }
            CoroutineKind::Coroutine(_) => f.write_str("coroutine"),
        }
    }
}

/// In the case of a coroutine created as part of an async/gen construct,
/// which kind of async/gen construct caused it to be created?
///
/// This helps error messages but is also used to drive coercions in
/// type-checking (see #60424).
#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, HashStable_Generic, Encodable, Decodable)]
pub enum CoroutineSource {
    /// An explicit `async`/`gen` block written by the user.
    Block,

    /// An explicit `async`/`gen` closure written by the user.
    Closure,

    /// The `async`/`gen` block generated as the body of an async/gen function.
    Fn,
}

impl fmt::Display for CoroutineSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CoroutineSource::Block => "block",
            CoroutineSource::Closure => "closure body",
            CoroutineSource::Fn => "fn body",
        }
        .fmt(f)
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Copy, Hash, HashStable_Generic, Encodable, Decodable)]
pub enum CoroutineDesugaring {
    /// An explicit `async` block or the body of an `async` function.
    Async,

    /// An explicit `gen` block or the body of a `gen` function.
    Gen,

    /// An explicit `async gen` block or the body of an `async gen` function,
    /// which is able to both `yield` and `.await`.
    AsyncGen,
}

impl fmt::Display for CoroutineDesugaring {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CoroutineDesugaring::Async => {
                if f.alternate() {
                    f.write_str("`async` ")?;
                } else {
                    f.write_str("async ")?
                }
            }
            CoroutineDesugaring::Gen => {
                if f.alternate() {
                    f.write_str("`gen` ")?;
                } else {
                    f.write_str("gen ")?
                }
            }
            CoroutineDesugaring::AsyncGen => {
                if f.alternate() {
                    f.write_str("`async gen` ")?;
                } else {
                    f.write_str("async gen ")?
                }
            }
        }

        Ok(())
    }
}

#[derive(Copy, Clone, Debug)]
pub enum BodyOwnerKind {
    /// Functions and methods.
    Fn,

    /// Closures
    Closure,

    /// Constants and associated constants, also including inline constants.
    Const { inline: bool },

    /// Initializer of a `static` item.
    Static(Mutability),

    /// Fake body for a global asm to store its const-like value types.
    GlobalAsm,
}

impl BodyOwnerKind {
    pub fn is_fn_or_closure(self) -> bool {
        match self {
            BodyOwnerKind::Fn | BodyOwnerKind::Closure => true,
            BodyOwnerKind::Const { .. } | BodyOwnerKind::Static(_) | BodyOwnerKind::GlobalAsm => {
                false
            }
        }
    }
}

/// The kind of an item that requires const-checking.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstContext {
    /// A `const fn`.
    ConstFn,

    /// A `static` or `static mut`.
    Static(Mutability),

    /// A `const`, associated `const`, or other const context.
    ///
    /// Other contexts include:
    /// - Array length expressions
    /// - Enum discriminants
    /// - Const generics
    ///
    /// For the most part, other contexts are treated just like a regular `const`, so they are
    /// lumped into the same category.
    Const { inline: bool },
}

impl ConstContext {
    /// A description of this const context that can appear between backticks in an error message.
    ///
    /// E.g. `const` or `static mut`.
    pub fn keyword_name(self) -> &'static str {
        match self {
            Self::Const { .. } => "const",
            Self::Static(Mutability::Not) => "static",
            Self::Static(Mutability::Mut) => "static mut",
            Self::ConstFn => "const fn",
        }
    }
}

/// A colloquial, trivially pluralizable description of this const context for use in error
/// messages.
impl fmt::Display for ConstContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::Const { .. } => write!(f, "constant"),
            Self::Static(_) => write!(f, "static"),
            Self::ConstFn => write!(f, "constant function"),
        }
    }
}

impl IntoDiagArg for ConstContext {
    fn into_diag_arg(self, _: &mut Option<std::path::PathBuf>) -> DiagArgValue {
        DiagArgValue::Str(Cow::Borrowed(match self {
            ConstContext::ConstFn => "const_fn",
            ConstContext::Static(_) => "static",
            ConstContext::Const { .. } => "const",
        }))
    }
}

/// A literal.
pub type Lit = Spanned<LitKind>;

/// A constant (expression) that's not an item or associated item,
/// but needs its own `DefId` for type-checking, const-eval, etc.
/// These are usually found nested inside types (e.g., array lengths)
/// or expressions (e.g., repeat counts), and also used to define
/// explicit discriminant values for enum variants.
///
/// You can check if this anon const is a default in a const param
/// `const N: usize = { ... }` with `tcx.hir_opt_const_param_default_param_def_id(..)`
#[derive(Copy, Clone, Debug, HashStable_Generic)]
pub struct AnonConst {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub def_id: LocalDefId,
    pub body: BodyId,
    pub span: Span,
}

/// An inline constant expression `const { something }`.
#[derive(Copy, Clone, Debug, HashStable_Generic)]
pub struct ConstBlock {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub def_id: LocalDefId,
    pub body: BodyId,
}

/// An expression.
///
/// For more details, see the [rust lang reference].
/// Note that the reference does not document nightly-only features.
/// There may be also slight differences in the names and representation of AST nodes between
/// the compiler and the reference.
///
/// [rust lang reference]: https://doc.rust-lang.org/reference/expressions.html
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct Expr<'hir> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub kind: ExprKind<'hir>,
    pub span: Span,
}

impl Expr<'_> {
    pub fn precedence(&self, has_attr: &dyn Fn(HirId) -> bool) -> ExprPrecedence {
        let prefix_attrs_precedence = || -> ExprPrecedence {
            if has_attr(self.hir_id) { ExprPrecedence::Prefix } else { ExprPrecedence::Unambiguous }
        };

        match &self.kind {
            ExprKind::Closure(closure) => {
                match closure.fn_decl.output {
                    FnRetTy::DefaultReturn(_) => ExprPrecedence::Jump,
                    FnRetTy::Return(_) => prefix_attrs_precedence(),
                }
            }

            ExprKind::Break(..)
            | ExprKind::Ret(..)
            | ExprKind::Yield(..)
            | ExprKind::Become(..) => ExprPrecedence::Jump,

            // Binop-like expr kinds, handled by `AssocOp`.
            ExprKind::Binary(op, ..) => op.node.precedence(),
            ExprKind::Cast(..) => ExprPrecedence::Cast,

            ExprKind::Assign(..) |
            ExprKind::AssignOp(..) => ExprPrecedence::Assign,

            // Unary, prefix
            ExprKind::AddrOf(..)
            // Here `let pats = expr` has `let pats =` as a "unary" prefix of `expr`.
            // However, this is not exactly right. When `let _ = a` is the LHS of a binop we
            // need parens sometimes. E.g. we can print `(let _ = a) && b` as `let _ = a && b`
            // but we need to print `(let _ = a) < b` as-is with parens.
            | ExprKind::Let(..)
            | ExprKind::Unary(..) => ExprPrecedence::Prefix,

            // Need parens if and only if there are prefix attributes.
            ExprKind::Array(_)
            | ExprKind::Block(..)
            | ExprKind::Call(..)
            | ExprKind::ConstBlock(_)
            | ExprKind::Continue(..)
            | ExprKind::Field(..)
            | ExprKind::If(..)
            | ExprKind::Index(..)
            | ExprKind::InlineAsm(..)
            | ExprKind::Lit(_)
            | ExprKind::Loop(..)
            | ExprKind::Match(..)
            | ExprKind::MethodCall(..)
            | ExprKind::OffsetOf(..)
            | ExprKind::Path(..)
            | ExprKind::Repeat(..)
            | ExprKind::Struct(..)
            | ExprKind::Tup(_)
            | ExprKind::Type(..)
            | ExprKind::UnsafeBinderCast(..)
            | ExprKind::Use(..)
            | ExprKind::Err(_) => prefix_attrs_precedence(),

            ExprKind::DropTemps(expr, ..) => expr.precedence(has_attr),
        }
    }

    /// Whether this looks like a place expr, without checking for deref
    /// adjustments.
    /// This will return `true` in some potentially surprising cases such as
    /// `CONSTANT.field`.
    pub fn is_syntactic_place_expr(&self) -> bool {
        self.is_place_expr(|_| true)
    }

    /// Whether this is a place expression.
    ///
    /// `allow_projections_from` should return `true` if indexing a field or index expression based
    /// on the given expression should be considered a place expression.
    pub fn is_place_expr(&self, mut allow_projections_from: impl FnMut(&Self) -> bool) -> bool {
        match self.kind {
            ExprKind::Path(QPath::Resolved(_, ref path)) => {
                matches!(path.res, Res::Local(..) | Res::Def(DefKind::Static { .. }, _) | Res::Err)
            }

            // Type ascription inherits its place expression kind from its
            // operand. See:
            // https://github.com/rust-lang/rfcs/blob/master/text/0803-type-ascription.md#type-ascription-and-temporaries
            ExprKind::Type(ref e, _) => e.is_place_expr(allow_projections_from),

            // Unsafe binder cast preserves place-ness of the sub-expression.
            ExprKind::UnsafeBinderCast(_, e, _) => e.is_place_expr(allow_projections_from),

            ExprKind::Unary(UnOp::Deref, _) => true,

            ExprKind::Field(ref base, _) | ExprKind::Index(ref base, _, _) => {
                allow_projections_from(base) || base.is_place_expr(allow_projections_from)
            }

            // Suppress errors for bad expressions.
            ExprKind::Err(_guar)
            | ExprKind::Let(&LetExpr { recovered: ast::Recovered::Yes(_guar), .. }) => true,

            // Partially qualified paths in expressions can only legally
            // refer to associated items which are always rvalues.
            ExprKind::Path(QPath::TypeRelative(..))
            | ExprKind::Call(..)
            | ExprKind::MethodCall(..)
            | ExprKind::Use(..)
            | ExprKind::Struct(..)
            | ExprKind::Tup(..)
            | ExprKind::If(..)
            | ExprKind::Match(..)
            | ExprKind::Closure { .. }
            | ExprKind::Block(..)
            | ExprKind::Repeat(..)
            | ExprKind::Array(..)
            | ExprKind::Break(..)
            | ExprKind::Continue(..)
            | ExprKind::Ret(..)
            | ExprKind::Become(..)
            | ExprKind::Let(..)
            | ExprKind::Loop(..)
            | ExprKind::Assign(..)
            | ExprKind::InlineAsm(..)
            | ExprKind::OffsetOf(..)
            | ExprKind::AssignOp(..)
            | ExprKind::Lit(_)
            | ExprKind::ConstBlock(..)
            | ExprKind::Unary(..)
            | ExprKind::AddrOf(..)
            | ExprKind::Binary(..)
            | ExprKind::Yield(..)
            | ExprKind::Cast(..)
            | ExprKind::DropTemps(..) => false,
        }
    }

    /// If this is a desugared range expression,
    /// returns the span of the range without desugaring context.
    pub fn range_span(&self) -> Option<Span> {
        is_range_literal(self).then(|| self.span.parent_callsite().expect("invariant: range literal desugaring always has a parent callsite span")) // tRust: unwrap -> expect
    }

    /// Check if expression is an integer literal that can be used
    /// where `usize` is expected.
    pub fn is_size_lit(&self) -> bool {
        matches!(
            self.kind,
            ExprKind::Lit(Lit {
                node: LitKind::Int(_, LitIntType::Unsuffixed | LitIntType::Unsigned(UintTy::Usize)),
                ..
            })
        )
    }

    /// If `Self.kind` is `ExprKind::DropTemps(expr)`, drill down until we get a non-`DropTemps`
    /// `Expr`. This is used in suggestions to ignore this `ExprKind` as it is semantically
    /// silent, only signaling the ownership system. By doing this, suggestions that check the
    /// `ExprKind` of any given `Expr` for presentation don't have to care about `DropTemps`
    /// beyond remembering to call this function before doing analysis on it.
    pub fn peel_drop_temps(&self) -> &Self {
        let mut expr = self;
        while let ExprKind::DropTemps(inner) = &expr.kind {
            expr = inner;
        }
        expr
    }

    pub fn peel_blocks(&self) -> &Self {
        let mut expr = self;
        while let ExprKind::Block(Block { expr: Some(inner), .. }, _) = &expr.kind {
            expr = inner;
        }
        expr
    }

    pub fn peel_borrows(&self) -> &Self {
        let mut expr = self;
        while let ExprKind::AddrOf(.., inner) = &expr.kind {
            expr = inner;
        }
        expr
    }

    pub fn can_have_side_effects(&self) -> bool {
        match self.peel_drop_temps().kind {
            ExprKind::Path(_) | ExprKind::Lit(_) | ExprKind::OffsetOf(..) | ExprKind::Use(..) => {
                false
            }
            ExprKind::Type(base, _)
            | ExprKind::Unary(_, base)
            | ExprKind::Field(base, _)
            | ExprKind::Index(base, _, _)
            | ExprKind::AddrOf(.., base)
            | ExprKind::Cast(base, _)
            | ExprKind::UnsafeBinderCast(_, base, _) => {
                // This isn't exactly true for `Index` and all `Unary`, but we are using this
                // method exclusively for diagnostics and there's a *cultural* pressure against
                // them being used only for its side-effects.
                base.can_have_side_effects()
            }
            ExprKind::Binary(_, lhs, rhs) => {
                // This isn't exactly true for all `Binary`, but we are using this
                // method exclusively for diagnostics and there's a *cultural* pressure against
                // them being used only for its side-effects.
                lhs.can_have_side_effects() || rhs.can_have_side_effects()
            }
            ExprKind::Struct(_, fields, init) => {
                let init_side_effects = match init {
                    StructTailExpr::Base(init) => init.can_have_side_effects(),
                    StructTailExpr::DefaultFields(_)
                    | StructTailExpr::None
                    | StructTailExpr::NoneWithError(_) => false,
                };
                fields.iter().map(|field| field.expr).any(|e| e.can_have_side_effects())
                    || init_side_effects
            }

            ExprKind::Array(args)
            | ExprKind::Tup(args)
            | ExprKind::Call(
                Expr {
                    kind:
                        ExprKind::Path(QPath::Resolved(
                            None,
                            Path { res: Res::Def(DefKind::Ctor(_, CtorKind::Fn), _), .. },
                        )),
                    ..
                },
                args,
            ) => args.iter().any(|arg| arg.can_have_side_effects()),
            ExprKind::Repeat(arg, _) => arg.can_have_side_effects(),
            ExprKind::If(..)
            | ExprKind::Match(..)
            | ExprKind::MethodCall(..)
            | ExprKind::Call(..)
            | ExprKind::Closure { .. }
            | ExprKind::Block(..)
            | ExprKind::Break(..)
            | ExprKind::Continue(..)
            | ExprKind::Ret(..)
            | ExprKind::Become(..)
            | ExprKind::Let(..)
            | ExprKind::Loop(..)
            | ExprKind::Assign(..)
            | ExprKind::InlineAsm(..)
            | ExprKind::AssignOp(..)
            | ExprKind::ConstBlock(..)
            | ExprKind::Yield(..)
            | ExprKind::DropTemps(..)
            | ExprKind::Err(_) => true,
        }
    }

    /// To a first-order approximation, is this a pattern?
    pub fn is_approximately_pattern(&self) -> bool {
        match &self.kind {
            ExprKind::Array(_)
            | ExprKind::Call(..)
            | ExprKind::Tup(_)
            | ExprKind::Lit(_)
            | ExprKind::Path(_)
            | ExprKind::Struct(..) => true,
            _ => false,
        }
    }

    /// Whether this and the `other` expression are the same for purposes of an indexing operation.
    ///
    /// This is only used for diagnostics to see if we have things like `foo[i]` where `foo` is
    /// borrowed multiple times with `i`.
    pub fn equivalent_for_indexing(&self, other: &Expr<'_>) -> bool {
        match (self.kind, other.kind) {
            (ExprKind::Lit(lit1), ExprKind::Lit(lit2)) => lit1.node == lit2.node,
            (
                ExprKind::Path(QPath::Resolved(None, path1)),
                ExprKind::Path(QPath::Resolved(None, path2)),
            ) => path1.res == path2.res,
            (
                ExprKind::Struct(
                    &QPath::Resolved(None, &Path { res: Res::Def(_, path1_def_id), .. }),
                    args1,
                    StructTailExpr::None,
                ),
                ExprKind::Struct(
                    &QPath::Resolved(None, &Path { res: Res::Def(_, path2_def_id), .. }),
                    args2,
                    StructTailExpr::None,
                ),
            ) => {
                path2_def_id == path1_def_id
                    && is_range_literal(self)
                    && is_range_literal(other)
                    && std::iter::zip(args1, args2)
                        .all(|(a, b)| a.expr.equivalent_for_indexing(b.expr))
            }
            _ => false,
        }
    }

    pub fn method_ident(&self) -> Option<Ident> {
        match self.kind {
            ExprKind::MethodCall(receiver_method, ..) => Some(receiver_method.ident),
            ExprKind::Unary(_, expr) | ExprKind::AddrOf(.., expr) => expr.method_ident(),
            _ => None,
        }
    }
}

/// Checks if the specified expression is a built-in range literal.
/// (See: `LoweringContext::lower_expr()`).
pub fn is_range_literal(expr: &Expr<'_>) -> bool {
    if let ExprKind::Struct(QPath::Resolved(None, path), _, StructTailExpr::None) = expr.kind
        && let [.., segment] = path.segments
        && let sym::RangeFrom
        | sym::RangeFull
        | sym::Range
        | sym::RangeToInclusive
        | sym::RangeTo
        | sym::RangeFromCopy
        | sym::RangeCopy
        | sym::RangeInclusiveCopy
        | sym::RangeToInclusiveCopy = segment.ident.name
        && expr.span.is_desugaring(DesugaringKind::RangeExpr)
    {
        true
    } else if let ExprKind::Call(func, _) = &expr.kind
        && let ExprKind::Path(QPath::Resolved(None, path)) = func.kind
        && let [.., segment] = path.segments
        && let sym::range_inclusive_new = segment.ident.name
        && expr.span.is_desugaring(DesugaringKind::RangeExpr)
    {
        true
    } else {
        false
    }
}

/// Checks if the specified expression needs parentheses for prefix
/// or postfix suggestions to be valid.
/// For example, `a + b` requires parentheses to suggest `&(a + b)`,
/// but just `a` does not.
/// Similarly, `(a + b).c()` also requires parentheses.
/// This should not be used for other types of suggestions.
pub fn expr_needs_parens(expr: &Expr<'_>) -> bool {
    match expr.kind {
        // parenthesize if needed (Issue #46756)
        ExprKind::Cast(_, _) | ExprKind::Binary(_, _, _) => true,
        // parenthesize borrows of range literals (Issue #54505)
        _ if is_range_literal(expr) => true,
        _ => false,
    }
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum ExprKind<'hir> {
    /// Allow anonymous constants from an inline `const` block
    ConstBlock(ConstBlock),
    /// An array (e.g., `[a, b, c, d]`).
    Array(&'hir [Expr<'hir>]),
    /// A function call.
    ///
    /// The first field resolves to the function itself (usually an `ExprKind::Path`),
    /// and the second field is the list of arguments.
    /// This also represents calling the constructor of
    /// tuple-like ADTs such as tuple structs and enum variants.
    Call(&'hir Expr<'hir>, &'hir [Expr<'hir>]),
    /// A method call (e.g., `x.foo::<'static, Bar, Baz>(a, b, c, d)`).
    ///
    /// The `PathSegment` represents the method name and its generic arguments
    /// (within the angle brackets).
    /// The `&Expr` is the expression that evaluates
    /// to the object on which the method is being called on (the receiver),
    /// and the `&[Expr]` is the rest of the arguments.
    /// Thus, `x.foo::<Bar, Baz>(a, b, c, d)` is represented as
    /// `ExprKind::MethodCall(PathSegment { foo, [Bar, Baz] }, x, [a, b, c, d], span)`.
    /// The final `Span` represents the span of the function and arguments
    /// (e.g. `foo::<Bar, Baz>(a, b, c, d)` in `x.foo::<Bar, Baz>(a, b, c, d)`
    ///
    /// To resolve the called method to a `DefId`, call [`type_dependent_def_id`] with
    /// the `hir_id` of the `MethodCall` node itself.
    ///
    /// [`type_dependent_def_id`]: ../../rustc_middle/ty/struct.TypeckResults.html#method.type_dependent_def_id
    MethodCall(&'hir PathSegment<'hir>, &'hir Expr<'hir>, &'hir [Expr<'hir>], Span),
    /// An use expression (e.g., `var.use`).
    Use(&'hir Expr<'hir>, Span),
    /// A tuple (e.g., `(a, b, c, d)`).
    Tup(&'hir [Expr<'hir>]),
    /// A binary operation (e.g., `a + b`, `a * b`).
    Binary(BinOp, &'hir Expr<'hir>, &'hir Expr<'hir>),
    /// A unary operation (e.g., `!x`, `*x`).
    Unary(UnOp, &'hir Expr<'hir>),
    /// A literal (e.g., `1`, `"foo"`).
    Lit(Lit),
    /// A cast (e.g., `foo as f64`).
    Cast(&'hir Expr<'hir>, &'hir Ty<'hir>),
    /// A type ascription (e.g., `x: Foo`). See RFC 3307.
    Type(&'hir Expr<'hir>, &'hir Ty<'hir>),
    /// Wraps the expression in a terminating scope.
    /// This makes it semantically equivalent to `{ let _t = expr; _t }`.
    ///
    /// This construct only exists to tweak the drop order in AST lowering.
    /// An example of that is the desugaring of `for` loops.
    DropTemps(&'hir Expr<'hir>),
    /// A `let $pat = $expr` expression.
    ///
    /// These are not [`LetStmt`] and only occur as expressions.
    /// The `let Some(x) = foo()` in `if let Some(x) = foo()` is an example of `Let(..)`.
    Let(&'hir LetExpr<'hir>),
    /// An `if` block, with an optional else block.
    ///
    /// I.e., `if <expr> { <expr> } else { <expr> }`.
    ///
    /// The "then" expr is always `ExprKind::Block`. If present, the "else" expr is always
    /// `ExprKind::Block` (for `else`) or `ExprKind::If` (for `else if`).
    /// Note that using an `Expr` instead of a `Block` for the "then" part is intentional,
    /// as it simplifies the type coercion machinery.
    If(&'hir Expr<'hir>, &'hir Expr<'hir>, Option<&'hir Expr<'hir>>),
    /// A conditionless loop (can be exited with `break`, `continue`, or `return`).
    ///
    /// I.e., `'label: loop { <block> }`.
    ///
    /// The `Span` is the loop header (`for x in y`/`while let pat = expr`).
    Loop(&'hir Block<'hir>, Option<Label>, LoopSource, Span),
    /// A `match` block, with a source that indicates whether or not it is
    /// the result of a desugaring, and if so, which kind.
    Match(&'hir Expr<'hir>, &'hir [Arm<'hir>], MatchSource),
    /// A closure (e.g., `move |a, b, c| {a + b + c}`).
    ///
    /// The `Span` is the argument block `|...|`.
    ///
    /// This may also be a coroutine literal or an `async block` as indicated by the
    /// `Option<Movability>`.
    Closure(&'hir Closure<'hir>),
    /// A block (e.g., `'label: { ... }`).
    Block(&'hir Block<'hir>, Option<Label>),

    /// An assignment (e.g., `a = foo()`).
    Assign(&'hir Expr<'hir>, &'hir Expr<'hir>, Span),
    /// An assignment with an operator.
    ///
    /// E.g., `a += 1`.
    AssignOp(AssignOp, &'hir Expr<'hir>, &'hir Expr<'hir>),
    /// Access of a named (e.g., `obj.foo`) or unnamed (e.g., `obj.0`) struct or tuple field.
    Field(&'hir Expr<'hir>, Ident),
    /// An indexing operation (`foo[2]`).
    /// Similar to [`ExprKind::MethodCall`], the final `Span` represents the span of the brackets
    /// and index.
    Index(&'hir Expr<'hir>, &'hir Expr<'hir>, Span),

    /// Path to a definition, possibly containing lifetime or type parameters.
    Path(QPath<'hir>),

    /// A referencing operation (i.e., `&a` or `&mut a`).
    AddrOf(BorrowKind, Mutability, &'hir Expr<'hir>),
    /// A `break`, with an optional label to break.
    Break(Destination, Option<&'hir Expr<'hir>>),
    /// A `continue`, with an optional label.
    Continue(Destination),
    /// A `return`, with an optional value to be returned.
    Ret(Option<&'hir Expr<'hir>>),
    /// A `become`, with the value to be returned.
    Become(&'hir Expr<'hir>),

    /// Inline assembly (from `asm!`), with its outputs and inputs.
    InlineAsm(&'hir InlineAsm<'hir>),

    /// Field offset (`offset_of!`)
    OffsetOf(&'hir Ty<'hir>, &'hir [Ident]),

    /// A struct or struct-like variant literal expression.
    ///
    /// E.g., `Foo {x: 1, y: 2}`, or `Foo {x: 1, .. base}`,
    /// where `base` is the `Option<Expr>`.
    Struct(&'hir QPath<'hir>, &'hir [ExprField<'hir>], StructTailExpr<'hir>),

    /// An array literal constructed from one repeated element.
    ///
    /// E.g., `[1; 5]`. The first expression is the element
    /// to be repeated; the second is the number of times to repeat it.
    Repeat(&'hir Expr<'hir>, &'hir ConstArg<'hir>),

    /// A suspension point for coroutines (i.e., `yield <expr>`).
    Yield(&'hir Expr<'hir>, YieldSource),

    /// Operators which can be used to interconvert `unsafe` binder types.
    /// e.g. `unsafe<'a> &'a i32` <=> `&i32`.
    UnsafeBinderCast(UnsafeBinderCastKind, &'hir Expr<'hir>, Option<&'hir Ty<'hir>>),

    /// A placeholder for an expression that wasn't syntactically well formed in some way.
    Err(rustc_span::ErrorGuaranteed),
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum StructTailExpr<'hir> {
    /// A struct expression where all the fields are explicitly enumerated: `Foo { a, b }`.
    None,
    /// A struct expression with a "base", an expression of the same type as the outer struct that
    /// will be used to populate any fields not explicitly mentioned: `Foo { ..base }`
    Base(&'hir Expr<'hir>),
    /// A struct expression with a `..` tail but no "base" expression. The values from the struct
    /// fields' default values will be used to populate any fields not explicitly mentioned:
    /// `Foo { .. }`.
    DefaultFields(Span),
    /// No trailing `..` was written, and also, a parse error occurred inside the struct braces.
    ///
    /// This struct should be treated similarly to as if it had an `..` in it,
    /// in particular rather than reporting missing fields, because the parse error
    /// makes which fields the struct was intended to have not fully known.
    NoneWithError(ErrorGuaranteed),
}

/// Represents an optionally `Self`-qualified value/type path or associated extension.
///
/// To resolve the path to a `DefId`, call [`qpath_res`].
///
/// [`qpath_res`]: ../../rustc_middle/ty/struct.TypeckResults.html#method.qpath_res
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum QPath<'hir> {
    /// Path to a definition, optionally "fully-qualified" with a `Self`
    /// type, if the path points to an associated item in a trait.
    ///
    /// E.g., an unqualified path like `Clone::clone` has `None` for `Self`,
    /// while `<Vec<T> as Clone>::clone` has `Some(Vec<T>)` for `Self`,
    /// even though they both have the same two-segment `Clone::clone` `Path`.
    Resolved(Option<&'hir Ty<'hir>>, &'hir Path<'hir>),

    /// Type-related paths (e.g., `<T>::default` or `<T>::Output`).
    /// Will be resolved by type-checking to an associated item.
    ///
    /// UFCS source paths can desugar into this, with `Vec::new` turning into
    /// `<Vec>::new`, and `T::X::Y::method` into `<<<T>::X>::Y>::method`,
    /// the `X` and `Y` nodes each being a `TyKind::Path(QPath::TypeRelative(..))`.
    TypeRelative(&'hir Ty<'hir>, &'hir PathSegment<'hir>),
}

impl<'hir> QPath<'hir> {
    /// Returns the span of this `QPath`.
    pub fn span(&self) -> Span {
        match *self {
            QPath::Resolved(_, path) => path.span,
            QPath::TypeRelative(qself, ps) => qself.span.to(ps.ident.span),
        }
    }

    /// Returns the span of the qself of this `QPath`. For example, `()` in
    /// `<() as Trait>::method`.
    pub fn qself_span(&self) -> Span {
        match *self {
            QPath::Resolved(_, path) => path.span,
            QPath::TypeRelative(qself, _) => qself.span,
        }
    }
}

/// Hints at the original code for a let statement.
#[derive(Copy, Clone, Debug, HashStable_Generic)]
pub enum LocalSource {
    /// A `match _ { .. }`.
    Normal,
    /// When lowering async functions, we create locals within the `async move` so that
    /// all parameters are dropped after the future is polled.
    ///
    /// ```ignore (pseudo-Rust)
    /// async fn foo(<pattern> @ x: Type) {
    ///     async move {
    ///         let <pattern> = x;
    ///     }
    /// }
    /// ```
    AsyncFn,
    /// A desugared `<expr>.await`.
    AwaitDesugar,
    /// A desugared `expr = expr`, where the LHS is a tuple, struct, array or underscore expression.
    AssignDesugar,
    /// A contract `#[ensures(..)]` attribute injects a let binding for the check that runs at point of return.
    Contract,
}

/// Hints at the original code for a `match _ { .. }`.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, HashStable_Generic, Encodable, Decodable)]
pub enum MatchSource {
    /// A `match _ { .. }`.
    Normal,
    /// A `expr.match { .. }`.
    Postfix,
    /// A desugared `for _ in _ { .. }` loop.
    ForLoopDesugar,
    /// A desugared `?` operator.
    TryDesugar(HirId),
    /// A desugared `<expr>.await`.
    AwaitDesugar,
    /// A desugared `format_args!()`.
    FormatArgs,
}

impl MatchSource {
    #[inline]
    pub const fn name(self) -> &'static str {
        use MatchSource::*;
        match self {
            Normal => "match",
            Postfix => ".match",
            ForLoopDesugar => "for",
            TryDesugar(_) => "?",
            AwaitDesugar => ".await",
            FormatArgs => "format_args!()",
        }
    }
}

/// The loop type that yielded an `ExprKind::Loop`.
#[derive(Copy, Clone, PartialEq, Debug, HashStable_Generic)]
pub enum LoopSource {
    /// A `loop { .. }` loop.
    Loop,
    /// A `while _ { .. }` loop.
    While,
    /// A `for _ in _ { .. }` loop.
    ForLoop,
}

impl LoopSource {
    pub fn name(self) -> &'static str {
        match self {
            LoopSource::Loop => "loop",
            LoopSource::While => "while",
            LoopSource::ForLoop => "for",
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, HashStable_Generic)]
pub enum LoopIdError {
    OutsideLoopScope,
    UnlabeledCfInWhileCondition,
    UnresolvedLabel,
}

impl fmt::Display for LoopIdError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            LoopIdError::OutsideLoopScope => "not inside loop scope",
            LoopIdError::UnlabeledCfInWhileCondition => {
                "unlabeled control flow (break or continue) in while condition"
            }
            LoopIdError::UnresolvedLabel => "label not found",
        })
    }
}

#[derive(Copy, Clone, Debug, PartialEq, HashStable_Generic)]
pub struct Destination {
    /// This is `Some(_)` iff there is an explicit user-specified 'label
    pub label: Option<Label>,

    /// These errors are caught and then reported during the diagnostics pass in
    /// `librustc_passes/loops.rs`
    pub target_id: Result<HirId, LoopIdError>,
}

/// The yield kind that caused an `ExprKind::Yield`.
#[derive(Copy, Clone, Debug, HashStable_Generic)]
pub enum YieldSource {
    /// An `<expr>.await`.
    Await { expr: Option<HirId> },
    /// A plain `yield`.
    Yield,
}

impl fmt::Display for YieldSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            YieldSource::Await { .. } => "`await`",
            YieldSource::Yield => "`yield`",
        })
    }
}
