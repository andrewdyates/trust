// tRust: split from hir.rs for maintainability
use super::*;


/// A statement.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct Stmt<'hir> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub kind: StmtKind<'hir>,
    pub span: Span,
}

/// The contents of a statement.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub enum StmtKind<'hir> {
    /// A local (`let`) binding.
    Let(&'hir LetStmt<'hir>),

    /// An item binding.
    Item(ItemId),

    /// An expression without a trailing semi-colon (must have unit type).
    Expr(&'hir Expr<'hir>),

    /// An expression with a trailing semi-colon (may have any type).
    Semi(&'hir Expr<'hir>),
}

/// Represents a `let` statement (i.e., `let <pat>:<ty> = <init>;`).
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct LetStmt<'hir> {
    /// Span of `super` in `super let`.
    pub super_: Option<Span>,
    pub pat: &'hir Pat<'hir>,
    /// Type annotation, if any (otherwise the type will be inferred).
    pub ty: Option<&'hir Ty<'hir>>,
    /// Initializer expression to set the value, if any.
    pub init: Option<&'hir Expr<'hir>>,
    /// Else block for a `let...else` binding.
    pub els: Option<&'hir Block<'hir>>,
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub span: Span,
    /// Can be `ForLoopDesugar` if the `let` statement is part of a `for` loop
    /// desugaring, or `AssignDesugar` if it is the result of a complex
    /// assignment desugaring. Otherwise will be `Normal`.
    pub source: LocalSource,
}

/// Represents a single arm of a `match` expression, e.g.
/// `<pat> (if <guard>) => <body>`.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct Arm<'hir> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub span: Span,
    /// If this pattern and the optional guard matches, then `body` is evaluated.
    pub pat: &'hir Pat<'hir>,
    /// Optional guard clause.
    pub guard: Option<&'hir Expr<'hir>>,
    /// The expression the arm evaluates to if this arm matches.
    pub body: &'hir Expr<'hir>,
}

/// Represents a `let <pat>[: <ty>] = <expr>` expression (not a [`LetStmt`]), occurring in an `if-let`
/// or `let-else`, evaluating to a boolean. Typically the pattern is refutable.
///
/// In an `if let`, imagine it as `if (let <pat> = <expr>) { ... }`; in a let-else, it is part of
/// the desugaring to if-let. Only let-else supports the type annotation at present.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct LetExpr<'hir> {
    pub span: Span,
    pub pat: &'hir Pat<'hir>,
    pub ty: Option<&'hir Ty<'hir>>,
    pub init: &'hir Expr<'hir>,
    /// `Recovered::Yes` when this let expressions is not in a syntactically valid location.
    /// Used to prevent building MIR in such situations.
    pub recovered: ast::Recovered,
}

#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct ExprField<'hir> {
    #[stable_hasher(ignore)]
    pub hir_id: HirId,
    pub ident: Ident,
    pub expr: &'hir Expr<'hir>,
    pub span: Span,
    pub is_shorthand: bool,
}

#[derive(Copy, Clone, PartialEq, Debug, HashStable_Generic)]
pub enum BlockCheckMode {
    DefaultBlock,
    UnsafeBlock(UnsafeSource),
}

#[derive(Copy, Clone, PartialEq, Debug, HashStable_Generic)]
pub enum UnsafeSource {
    CompilerGenerated,
    UserProvided,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, HashStable_Generic)]
pub struct BodyId {
    pub hir_id: HirId,
}

/// The body of a function, closure, or constant value. In the case of
/// a function, the body contains not only the function body itself
/// (which is an expression), but also the argument patterns, since
/// those are something that the caller doesn't really care about.
///
/// # Examples
///
/// ```
/// fn foo((x, y): (u32, u32)) -> u32 {
///     x + y
/// }
/// ```
///
/// Here, the `Body` associated with `foo()` would contain:
///
/// - an `params` array containing the `(x, y)` pattern
/// - a `value` containing the `x + y` expression (maybe wrapped in a block)
/// - `coroutine_kind` would be `None`
///
/// All bodies have an **owner**, which can be accessed via the HIR
/// map using `body_owner_def_id()`.
#[derive(Debug, Clone, Copy, HashStable_Generic)]
pub struct Body<'hir> {
    pub params: &'hir [Param<'hir>],
    pub value: &'hir Expr<'hir>,
}

impl<'hir> Body<'hir> {
    pub fn id(&self) -> BodyId {
        BodyId { hir_id: self.value.hir_id }
    }
}
