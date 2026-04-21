// tRust: split from diagnostics.rs (Part of #857)

use std::borrow::Cow;
use std::iter;
use std::ops::Deref;

use rustc_ast::visit::{FnCtxt, FnKind, LifetimeCtxt, Visitor, walk_ty};
use rustc_ast::{
    self as ast, AngleBracketedArg, AssocItemKind, DUMMY_NODE_ID, Expr, ExprKind, GenericArg,
    GenericArgs, GenericParam, GenericParamKind, Item, ItemKind, MethodCall, NodeId, Path,
    PathSegment, Ty, TyKind,
};
use rustc_ast_pretty::pprust::{path_to_string, where_bound_predicate_to_string};
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet};
use rustc_errors::codes::*;
use rustc_errors::{
    Applicability, Diag, ErrorGuaranteed, MultiSpan, SuggestionStyle, pluralize,
    struct_span_code_err,
};
use rustc_hir as hir;
use rustc_hir::def::Namespace::{self, *};
use rustc_hir::def::{self, CtorKind, CtorOf, DefKind, MacroKinds};
use rustc_hir::def_id::{CRATE_DEF_ID, DefId};
use rustc_hir::{MissingLifetimeKind, PrimTy, find_attr};
use rustc_middle::ty;
use rustc_session::{Session, lint};
use rustc_span::edit_distance::{edit_distance, find_best_match_for_name};
use rustc_span::edition::Edition;
use rustc_span::{DUMMY_SP, Ident, Span, Symbol, kw, sym};
use thin_vec::ThinVec;
use tracing::debug;

use super::NoConstantGenericsReason;
use crate::diagnostics::{ImportSuggestion, LabelSuggestion, TypoSuggestion};
use crate::late::{
    AliasPossibility, LateResolutionVisitor, LifetimeBinderKind, LifetimeRes, LifetimeRibKind,
    LifetimeUseSet, QSelf, RibKind,
};
use crate::ty::fast_reject::SimplifiedType;
use crate::{
    Finalize, Module, ModuleKind, ModuleOrUniformRoot, ParentScope, PathResult, PathSource,
    Resolver, ScopeSet, Segment, errors, path_names_to_string,
};
type Res = def::Res<ast::NodeId>;

/// A field or associated item from self type suggested in case of resolution failure.
enum AssocSuggestion {
    Field(Span),
    MethodWithSelf { called: bool },
    AssocFn { called: bool },
    AssocType,
    AssocConst,
}

impl AssocSuggestion {
    fn action(&self) -> &'static str {
        match self {
            AssocSuggestion::Field(_) => "use the available field",
            AssocSuggestion::MethodWithSelf { called: true } => {
                "call the method with the fully-qualified path"
            }
            AssocSuggestion::MethodWithSelf { called: false } => {
                "refer to the method with the fully-qualified path"
            }
            AssocSuggestion::AssocFn { called: true } => "call the associated function",
            AssocSuggestion::AssocFn { called: false } => "refer to the associated function",
            AssocSuggestion::AssocConst => "use the associated `const`",
            AssocSuggestion::AssocType => "use the associated type",
        }
    }
}

fn is_self_type(path: &[Segment], namespace: Namespace) -> bool {
    namespace == TypeNS && path.len() == 1 && path[0].ident.name == kw::SelfUpper
}

fn is_self_value(path: &[Segment], namespace: Namespace) -> bool {
    namespace == ValueNS && path.len() == 1 && path[0].ident.name == kw::SelfLower
}

fn path_to_string_without_assoc_item_bindings(path: &Path) -> String {
    let mut path = path.clone();
    for segment in &mut path.segments {
        let mut remove_args = false;
        if let Some(args) = segment.args.as_deref_mut()
            && let ast::GenericArgs::AngleBracketed(angle_bracketed) = args
        {
            angle_bracketed.args.retain(|arg| matches!(arg, ast::AngleBracketedArg::Arg(_)));
            remove_args = angle_bracketed.args.is_empty();
        }
        if remove_args {
            segment.args = None;
        }
    }
    path_to_string(&path)
}

/// Gets the stringified path for an enum from an `ImportSuggestion` for an enum variant.
fn import_candidate_to_enum_paths(suggestion: &ImportSuggestion) -> (String, String) {
    let variant_path = &suggestion.path;
    let variant_path_string = path_names_to_string(variant_path);

    let path_len = suggestion.path.segments.len();
    let enum_path = ast::Path {
        span: suggestion.path.span,
        segments: suggestion.path.segments[0..path_len - 1].iter().cloned().collect(),
        tokens: None,
    };
    let enum_path_string = path_names_to_string(&enum_path);

    (variant_path_string, enum_path_string)
}

/// Description of an elided lifetime.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) struct MissingLifetime {
    /// Used to overwrite the resolution with the suggestion, to avoid cascading errors.
    pub id: NodeId,
    /// As we cannot yet emit lints in this crate and have to buffer them instead,
    /// we need to associate each lint with some `NodeId`,
    /// however for some `MissingLifetime`s their `NodeId`s are "fake",
    /// in a sense that they are temporary and not get preserved down the line,
    /// which means that the lints for those nodes will not get emitted.
    /// To combat this, we can try to use some other `NodeId`s as a fallback option.
    pub id_for_lint: NodeId,
    /// Where to suggest adding the lifetime.
    pub span: Span,
    /// How the lifetime was introduced, to have the correct space and comma.
    pub kind: MissingLifetimeKind,
    /// Number of elided lifetimes, used for elision in path.
    pub count: usize,
}

/// Description of the lifetimes appearing in a function parameter.
/// This is used to provide a literal explanation to the elision failure.
#[derive(Clone, Debug)]
pub(super) struct ElisionFnParameter {
    /// The index of the argument in the original definition.
    pub index: usize,
    /// The name of the argument if it's a simple ident.
    pub ident: Option<Ident>,
    /// The number of lifetimes in the parameter.
    pub lifetime_count: usize,
    /// The span of the parameter.
    pub span: Span,
}

/// Description of lifetimes that appear as candidates for elision.
/// This is used to suggest introducing an explicit lifetime.
#[derive(Clone, Copy, Debug)]
pub(super) enum LifetimeElisionCandidate {
    /// This is not a real lifetime.
    Ignore,
    /// There is a named lifetime, we won't suggest anything.
    Named,
    Missing(MissingLifetime),
}

/// Only used for diagnostics.
#[derive(Debug)]
struct BaseError {
    msg: String,
    fallback_label: String,
    span: Span,
    span_label: Option<(Span, &'static str)>,
    could_be_expr: bool,
    suggestion: Option<(Span, &'static str, String)>,
    module: Option<DefId>,
}

#[derive(Debug)]
enum TypoCandidate {
    Typo(TypoSuggestion),
    Shadowed(Res, Option<Span>),
    None,
}

impl TypoCandidate {
    fn to_opt_suggestion(self) -> Option<TypoSuggestion> {
        match self {
            TypoCandidate::Typo(sugg) => Some(sugg),
            TypoCandidate::Shadowed(_, _) | TypoCandidate::None => None,
        }
    }
}

mod resolve_errors;
mod suggestions;
mod context_help;
mod lifetime;

pub(super) use lifetime::signal_lifetime_shadowing;
pub(super) use lifetime::signal_label_shadowing;
