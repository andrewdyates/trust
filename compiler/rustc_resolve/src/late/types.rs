// tRust: Split from late.rs -- type definitions for late name resolution.
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

type Res = def::Res<NodeId>;

use diagnostics::{ElisionFnParameter, LifetimeElisionCandidate, MissingLifetime};

#[derive(Copy, Clone, Debug)]
struct BindingInfo {
    span: Span,
    annotation: BindingMode,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum PatternSource {
    Match,
    Let,
    For,
    FnParam,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum IsRepeatExpr {
    No,
    Yes,
}

struct IsNeverPattern;

/// Describes whether an `AnonConst` is a type level const arg or
/// some other form of anon const (i.e. inline consts or enum discriminants)
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum AnonConstKind {
    EnumDiscriminant,
    FieldDefaultValue,
    InlineConst,
    ConstArg(IsRepeatExpr),
}

impl PatternSource {
    fn descr(self) -> &'static str {
        match self {
            PatternSource::Match => "match binding",
            PatternSource::Let => "let binding",
            PatternSource::For => "for binding",
            PatternSource::FnParam => "function parameter",
        }
    }
}

impl IntoDiagArg for PatternSource {
    fn into_diag_arg(self, _: &mut Option<std::path::PathBuf>) -> DiagArgValue {
        DiagArgValue::Str(Cow::Borrowed(self.descr()))
    }
}

/// Denotes whether the context for the set of already bound bindings is a `Product`
/// or `Or` context. This is used in e.g., `fresh_binding` and `resolve_pattern_inner`.
/// See those functions for more information.
#[derive(PartialEq)]
enum PatBoundCtx {
    /// A product pattern context, e.g., `Variant(a, b)`.
    Product,
    /// An or-pattern context, e.g., `p_0 | ... | p_n`.
    Or,
}

/// Tracks bindings resolved within a pattern. This serves two purposes:
///
/// - This tracks when identifiers are bound multiple times within a pattern. In a product context,
///   this is an error. In an or-pattern, this lets us reuse the same resolution for each instance.
///   See `fresh_binding` and `resolve_pattern_inner` for more information.
///
/// - The guard expression of a guard pattern may use bindings from within the guard pattern, but
///   not from elsewhere in the pattern containing it. This allows us to isolate the bindings in the
///   subpattern to construct the scope for the guard.
///
/// Each identifier must map to at most one distinct [`Res`].
type PatternBindings = SmallVec<[(PatBoundCtx, FxIndexMap<Ident, Res>); 1]>;

/// Does this the item (from the item rib scope) allow generic parameters?
#[derive(Copy, Clone, Debug)]
pub(crate) enum HasGenericParams {
    Yes(Span),
    No,
}

/// May this constant have generics?
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum ConstantHasGenerics {
    Yes,
    No(NoConstantGenericsReason),
}

impl ConstantHasGenerics {
    fn force_yes_if(self, b: bool) -> Self {
        if b { Self::Yes } else { self }
    }
}

/// Reason for why an anon const is not allowed to reference generic parameters
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum NoConstantGenericsReason {
    /// Const arguments are only allowed to use generic parameters when:
    /// - `feature(generic_const_exprs)` is enabled
    /// or
    /// - the const argument is a sole const generic parameter, i.e. `foo::<{ N }>()`
    ///
    /// If neither of the above are true then this is used as the cause.
    NonTrivialConstArg,
    /// Enum discriminants are not allowed to reference generic parameters ever, this
    /// is used when an anon const is in the following position:
    ///
    /// ```rust,compile_fail
    /// enum Foo<const N: isize> {
    ///     Variant = { N }, // this anon const is not allowed to use generics
    /// }
    /// ```
    IsEnumDiscriminant,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum ConstantItemKind {
    Const,
    Static,
}

impl ConstantItemKind {
    pub(crate) fn as_str(&self) -> &'static str {
        match self {
            Self::Const => "const",
            Self::Static => "static",
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum RecordPartialRes {
    Yes,
    No,
}

/// The rib kind restricts certain accesses,
/// e.g. to a `Res::Local` of an outer item.
#[derive(Copy, Clone, Debug)]
pub(crate) enum RibKind<'ra> {
    /// No restriction needs to be applied.
    Normal,

    /// We passed through an `ast::Block`.
    /// Behaves like `Normal`, but also partially like `Module` if the block contains items.
    /// `Block(None)` must be always processed in the same way as `Block(Some(module))`
    /// with empty `module`. The module can be `None` only because creation of some definitely
    /// empty modules is skipped as an optimization.
    Block(Option<Module<'ra>>),

    /// We passed through an impl or trait and are now in one of its
    /// methods or associated types. Allow references to ty params that impl or trait
    /// binds. Disallow any other upvars (including other ty params that are
    /// upvars).
    AssocItem,

    /// We passed through a function, closure or coroutine signature. Disallow labels.
    FnOrCoroutine,

    /// We passed through an item scope. Disallow upvars.
    Item(HasGenericParams, DefKind),

    /// We're in a constant item. Can't refer to dynamic stuff.
    ///
    /// The item may reference generic parameters in trivial constant expressions.
    /// All other constants aren't allowed to use generic params at all.
    ConstantItem(ConstantHasGenerics, Option<(Ident, ConstantItemKind)>),

    /// We passed through a module item.
    Module(Module<'ra>),

    /// We passed through a `macro_rules!` statement
    MacroDefinition(DefId),

    /// All bindings in this rib are generic parameters that can't be used
    /// from the default of a generic parameter because they're not declared
    /// before said generic parameter. Also see the `visit_generics` override.
    ForwardGenericParamBan(ForwardGenericParamBanReason),

    /// We are inside of the type of a const parameter. Can't refer to any
    /// parameters.
    ConstParamTy,

    /// We are inside a `sym` inline assembly operand. Can only refer to
    /// globals.
    InlineAsmSym,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum ForwardGenericParamBanReason {
    Default,
    ConstParamTy,
}

impl RibKind<'_> {
    /// Whether this rib kind contains generic parameters, as opposed to local
    /// variables.
    pub(crate) fn contains_params(&self) -> bool {
        match self {
            RibKind::Normal
            | RibKind::Block(..)
            | RibKind::FnOrCoroutine
            | RibKind::ConstantItem(..)
            | RibKind::Module(_)
            | RibKind::MacroDefinition(_)
            | RibKind::InlineAsmSym => false,
            RibKind::ConstParamTy
            | RibKind::AssocItem
            | RibKind::Item(..)
            | RibKind::ForwardGenericParamBan(_) => true,
        }
    }

    /// This rib forbids referring to labels defined in upwards ribs.
    fn is_label_barrier(self) -> bool {
        match self {
            RibKind::Normal | RibKind::MacroDefinition(..) => false,
            RibKind::FnOrCoroutine | RibKind::ConstantItem(..) => true,
            // tRust: invariant — is_label_barrier only applies to Normal, MacroDefinition, FnOrCoroutine, ConstantItem ribs
            kind => bug!("unexpected rib kind: {kind:?}"),
        }
    }
}

/// A single local scope.
///
/// A rib represents a scope names can live in. Note that these appear in many places, not just
/// around braces. At any place where the list of accessible names (of the given namespace)
/// changes or a new restrictions on the name accessibility are introduced, a new rib is put onto a
/// stack. This may be, for example, a `let` statement (because it introduces variables), a macro,
/// etc.
///
/// Different [rib kinds](enum@RibKind) are transparent for different names.
///
/// The resolution keeps a separate stack of ribs as it traverses the AST for each namespace. When
/// resolving, the name is looked up from inside out.
#[derive(Debug)]
pub(crate) struct Rib<'ra, R = Res> {
    pub bindings: FxIndexMap<Ident, R>,
    pub patterns_with_skipped_bindings: UnordMap<DefId, Vec<(Span, Result<(), ErrorGuaranteed>)>>,
    pub kind: RibKind<'ra>,
}

impl<'ra, R> Rib<'ra, R> {
    fn new(kind: RibKind<'ra>) -> Rib<'ra, R> {
        Rib {
            bindings: Default::default(),
            patterns_with_skipped_bindings: Default::default(),
            kind,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum LifetimeUseSet {
    One { use_span: Span, use_ctxt: visit::LifetimeCtxt },
    Many,
}

#[derive(Copy, Clone, Debug)]
enum LifetimeRibKind {
    // -- Ribs introducing named lifetimes
    //
    /// This rib declares generic parameters.
    /// Only for this kind the `LifetimeRib::bindings` field can be non-empty.
    Generics { binder: NodeId, span: Span, kind: LifetimeBinderKind },

    // -- Ribs introducing unnamed lifetimes
    //
    /// Create a new anonymous lifetime parameter and reference it.
    ///
    /// If `report_in_path`, report an error when encountering lifetime elision in a path:
    /// ```compile_fail
    /// struct Foo<'a> { x: &'a () }
    /// async fn foo(x: Foo) {}
    /// ```
    ///
    /// Note: the error should not trigger when the elided lifetime is in a pattern or
    /// expression-position path:
    /// ```
    /// struct Foo<'a> { x: &'a () }
    /// async fn foo(Foo { x: _ }: Foo<'_>) {}
    /// ```
    AnonymousCreateParameter { binder: NodeId, report_in_path: bool },

    /// Replace all anonymous lifetimes by provided lifetime.
    Elided(LifetimeRes),

    // -- Barrier ribs that stop lifetime lookup, or continue it but produce an error later.
    //
    /// Give a hard error when either `&` or `'_` is written. Used to
    /// rule out things like `where T: Foo<'_>`. Does not imply an
    /// error on default object bounds (e.g., `Box<dyn Foo>`).
    AnonymousReportError,

    /// Resolves elided lifetimes to `'static` if there are no other lifetimes in scope,
    /// otherwise give a warning that the previous behavior of introducing a new early-bound
    /// lifetime is a bug and will be removed (if `emit_lint` is enabled).
    StaticIfNoLifetimeInScope { lint_id: NodeId, emit_lint: bool },

    /// Signal we cannot find which should be the anonymous lifetime.
    ElisionFailure,

    /// This rib forbids usage of generic parameters inside of const parameter types.
    ///
    /// While this is desirable to support eventually, it is difficult to do and so is
    /// currently forbidden. See rust-lang/project-const-generics#28 for more info.
    ConstParamTy,

    /// Usage of generic parameters is forbidden in various positions for anon consts:
    /// - const arguments when `generic_const_exprs` is not enabled
    /// - enum discriminant values
    ///
    /// This rib emits an error when a lifetime would resolve to a lifetime parameter.
    ConcreteAnonConst(NoConstantGenericsReason),

    /// This rib acts as a barrier to forbid reference to lifetimes of a parent item.
    Item,
}

#[derive(Copy, Clone, Debug)]
enum LifetimeBinderKind {
    FnPtrType,
    PolyTrait,
    WhereBound,
    // Item covers foreign items, ADTs, type aliases, trait associated items and
    // trait alias associated items.
    Item,
    ConstItem,
    Function,
    Closure,
    ImplBlock,
    // Covers only `impl` associated types.
    ImplAssocType,
}

impl LifetimeBinderKind {
    fn descr(self) -> &'static str {
        use LifetimeBinderKind::*;
        match self {
            FnPtrType => "type",
            PolyTrait => "bound",
            WhereBound => "bound",
            Item | ConstItem => "item",
            ImplAssocType => "associated type",
            ImplBlock => "impl block",
            Function => "function",
            Closure => "closure",
        }
    }
}

#[derive(Debug)]
struct LifetimeRib {
    kind: LifetimeRibKind,
    // We need to preserve insertion order for async fns.
    bindings: FxIndexMap<Ident, (NodeId, LifetimeRes)>,
}

impl LifetimeRib {
    fn new(kind: LifetimeRibKind) -> LifetimeRib {
        LifetimeRib { bindings: Default::default(), kind }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum AliasPossibility {
    No,
    Maybe,
}

#[derive(Copy, Clone, Debug)]
pub(crate) enum PathSource<'a, 'ast, 'ra> {
    /// Type paths `Path`.
    Type,
    /// Trait paths in bounds or impls.
    Trait(AliasPossibility),
    /// Expression paths `path`, with optional parent context.
    Expr(Option<&'ast Expr>),
    /// Paths in path patterns `Path`.
    Pat,
    /// Paths in struct expressions and patterns `Path { .. }`.
    Struct(Option<&'a Expr>),
    /// Paths in tuple struct patterns `Path(..)`.
    TupleStruct(Span, &'ra [Span]),
    /// `m::A::B` in `<T as m::A>::B::C`.
    ///
    /// Second field holds the "cause" of this one, i.e. the context within
    /// which the trait item is resolved. Used for diagnostics.
    TraitItem(Namespace, &'a PathSource<'a, 'ast, 'ra>),
    /// Paths in delegation item
    Delegation,
    /// An arg in a `use<'a, N>` precise-capturing bound.
    PreciseCapturingArg(Namespace),
    /// Paths that end with `(..)`, for return type notation.
    ReturnTypeNotation,
    /// Paths from `#[define_opaque]` attributes
    DefineOpaques,
    /// Resolving a macro
    Macro,
    /// Paths for module or crate root. Used for restrictions.
    Module,
}

impl PathSource<'_, '_, '_> {
    fn namespace(self) -> Namespace {
        match self {
            PathSource::Type
            | PathSource::Trait(_)
            | PathSource::Struct(_)
            | PathSource::DefineOpaques
            | PathSource::Module => TypeNS,
            PathSource::Expr(..)
            | PathSource::Pat
            | PathSource::TupleStruct(..)
            | PathSource::Delegation
            | PathSource::ReturnTypeNotation => ValueNS,
            PathSource::TraitItem(ns, _) => ns,
            PathSource::PreciseCapturingArg(ns) => ns,
            PathSource::Macro => MacroNS,
        }
    }

    fn defer_to_typeck(self) -> bool {
        match self {
            PathSource::Type
            | PathSource::Expr(..)
            | PathSource::Pat
            | PathSource::Struct(_)
            | PathSource::TupleStruct(..)
            | PathSource::ReturnTypeNotation => true,
            PathSource::Trait(_)
            | PathSource::TraitItem(..)
            | PathSource::DefineOpaques
            | PathSource::Delegation
            | PathSource::PreciseCapturingArg(..)
            | PathSource::Macro
            | PathSource::Module => false,
        }
    }

    fn descr_expected(self) -> &'static str {
        match &self {
            PathSource::DefineOpaques => "type alias or associated type with opaqaue types",
            PathSource::Type => "type",
            PathSource::Trait(_) => "trait",
            PathSource::Pat => "unit struct, unit variant or constant",
            PathSource::Struct(_) => "struct, variant or union type",
            PathSource::TraitItem(ValueNS, PathSource::TupleStruct(..))
            | PathSource::TupleStruct(..) => "tuple struct or tuple variant",
            PathSource::TraitItem(ns, _) => match ns {
                TypeNS => "associated type",
                ValueNS => "method or associated constant",
                // tRust: invariant — macros cannot be associated items in a trait
                MacroNS => bug!("associated macro"),
            },
            PathSource::Expr(parent) => match parent.as_ref().map(|p| &p.kind) {
                // "function" here means "anything callable" rather than `DefKind::Fn`,
                // this is not precise but usually more helpful than just "value".
                Some(ExprKind::Call(call_expr, _)) => match &call_expr.kind {
                    // the case of `::some_crate()`
                    ExprKind::Path(_, path)
                        if let [segment, _] = path.segments.as_slice()
                            && segment.ident.name == kw::PathRoot =>
                    {
                        "external crate"
                    }
                    ExprKind::Path(_, path)
                        if let Some(segment) = path.segments.last()
                            && let Some(c) = segment.ident.to_string().chars().next()
                            && c.is_uppercase() =>
                    {
                        "function, tuple struct or tuple variant"
                    }
                    _ => "function",
                },
                _ => "value",
            },
            PathSource::ReturnTypeNotation | PathSource::Delegation => "function",
            PathSource::PreciseCapturingArg(..) => "type or const parameter",
            PathSource::Macro => "macro",
            PathSource::Module => "module",
        }
    }

    fn is_call(self) -> bool {
        matches!(self, PathSource::Expr(Some(&Expr { kind: ExprKind::Call(..), .. })))
    }

    pub(crate) fn is_expected(self, res: Res) -> bool {
        match self {
            PathSource::DefineOpaques => {
                matches!(
                    res,
                    Res::Def(
                        DefKind::Struct
                            | DefKind::Union
                            | DefKind::Enum
                            | DefKind::TyAlias
                            | DefKind::AssocTy,
                        _
                    ) | Res::SelfTyAlias { .. }
                )
            }
            PathSource::Type => matches!(
                res,
                Res::Def(
                    DefKind::Struct
                        | DefKind::Union
                        | DefKind::Enum
                        | DefKind::Trait
                        | DefKind::TraitAlias
                        | DefKind::TyAlias
                        | DefKind::AssocTy
                        | DefKind::TyParam
                        | DefKind::OpaqueTy
                        | DefKind::ForeignTy,
                    _,
                ) | Res::PrimTy(..)
                    | Res::SelfTyParam { .. }
                    | Res::SelfTyAlias { .. }
            ),
            PathSource::Trait(AliasPossibility::No) => matches!(res, Res::Def(DefKind::Trait, _)),
            PathSource::Trait(AliasPossibility::Maybe) => {
                matches!(res, Res::Def(DefKind::Trait | DefKind::TraitAlias, _))
            }
            PathSource::Expr(..) => matches!(
                res,
                Res::Def(
                    DefKind::Ctor(_, CtorKind::Const | CtorKind::Fn)
                        | DefKind::Const { .. }
                        | DefKind::Static { .. }
                        | DefKind::Fn
                        | DefKind::AssocFn
                        | DefKind::AssocConst { .. }
                        | DefKind::ConstParam,
                    _,
                ) | Res::Local(..)
                    | Res::SelfCtor(..)
            ),
            PathSource::Pat => {
                res.expected_in_unit_struct_pat()
                    || matches!(
                        res,
                        Res::Def(DefKind::Const { .. } | DefKind::AssocConst { .. }, _)
                    )
            }
            PathSource::TupleStruct(..) => res.expected_in_tuple_struct_pat(),
            PathSource::Struct(_) => matches!(
                res,
                Res::Def(
                    DefKind::Struct
                        | DefKind::Union
                        | DefKind::Variant
                        | DefKind::TyAlias
                        | DefKind::AssocTy,
                    _,
                ) | Res::SelfTyParam { .. }
                    | Res::SelfTyAlias { .. }
            ),
            PathSource::TraitItem(ns, _) => match res {
                Res::Def(DefKind::AssocConst { .. } | DefKind::AssocFn, _) if ns == ValueNS => true,
                Res::Def(DefKind::AssocTy, _) if ns == TypeNS => true,
                _ => false,
            },
            PathSource::ReturnTypeNotation => match res {
                Res::Def(DefKind::AssocFn, _) => true,
                _ => false,
            },
            PathSource::Delegation => matches!(res, Res::Def(DefKind::Fn | DefKind::AssocFn, _)),
            PathSource::PreciseCapturingArg(ValueNS) => {
                matches!(res, Res::Def(DefKind::ConstParam, _))
            }
            // We allow `SelfTyAlias` here so we can give a more descriptive error later.
            PathSource::PreciseCapturingArg(TypeNS) => matches!(
                res,
                Res::Def(DefKind::TyParam, _) | Res::SelfTyParam { .. } | Res::SelfTyAlias { .. }
            ),
            PathSource::PreciseCapturingArg(MacroNS) => false,
            PathSource::Macro => matches!(res, Res::Def(DefKind::Macro(_), _)),
            PathSource::Module => matches!(res, Res::Def(DefKind::Mod, _)),
        }
    }

    fn error_code(self, has_unexpected_resolution: bool) -> ErrCode {
        match (self, has_unexpected_resolution) {
            (PathSource::Trait(_), true) => E0404,
            (PathSource::Trait(_), false) => E0405,
            (PathSource::Type | PathSource::DefineOpaques, true) => E0573,
            (PathSource::Type | PathSource::DefineOpaques, false) => E0425,
            (PathSource::Struct(_), true) => E0574,
            (PathSource::Struct(_), false) => E0422,
            (PathSource::Expr(..), true) | (PathSource::Delegation, true) => E0423,
            (PathSource::Expr(..), false) | (PathSource::Delegation, false) => E0425,
            (PathSource::Pat | PathSource::TupleStruct(..), true) => E0532,
            (PathSource::Pat | PathSource::TupleStruct(..), false) => E0531,
            (PathSource::TraitItem(..) | PathSource::ReturnTypeNotation, true) => E0575,
            (PathSource::TraitItem(..) | PathSource::ReturnTypeNotation, false) => E0576,
            (PathSource::PreciseCapturingArg(..), true) => E0799,
            (PathSource::PreciseCapturingArg(..), false) => E0800,
            (PathSource::Macro, _) => E0425,
            // NOTE: there is no dedicated error code for this case yet.
            // E0577 already covers the same situation for visibilities,
            // so we reuse it here for now. It may make sense to generalize
            // it for restrictions in the future.
            (PathSource::Module, true) => E0577,
            (PathSource::Module, false) => E0433,
        }
    }
}

/// At this point for most items we can answer whether that item is exported or not,
/// but some items like impls require type information to determine exported-ness, so we make a
/// conservative estimate for them (e.g. based on nominal visibility).
#[derive(Clone, Copy)]
enum MaybeExported<'a> {
    Ok(NodeId),
    Impl(Option<DefId>),
    ImplItem(Result<DefId, &'a ast::Visibility>),
    NestedUse(&'a ast::Visibility),
}

impl MaybeExported<'_> {
    fn eval(self, r: &Resolver<'_, '_>) -> bool {
        let def_id = match self {
            MaybeExported::Ok(node_id) => Some(r.local_def_id(node_id)),
            MaybeExported::Impl(Some(trait_def_id)) | MaybeExported::ImplItem(Ok(trait_def_id)) => {
                trait_def_id.as_local()
            }
            MaybeExported::Impl(None) => return true,
            MaybeExported::ImplItem(Err(vis)) | MaybeExported::NestedUse(vis) => {
                return vis.kind.is_pub();
            }
        };
        def_id.is_none_or(|def_id| r.effective_visibilities.is_exported(def_id))
    }
}

/// Used for recording UnnecessaryQualification.
#[derive(Debug)]
pub(crate) struct UnnecessaryQualification<'ra> {
    pub decl: LateDecl<'ra>,
    pub node_id: NodeId,
    pub path_span: Span,
    pub removal_span: Span,
}
