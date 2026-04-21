// tRust: Split from monolithic late.rs (5,610 lines) into submodules.
// Part of #843, #838
//! "Late resolution" is the pass that resolves most of names in a crate beside imports and macros.
//! It runs when the crate is fully expanded and its module structure is fully built.
//! So it just walks through the crate and resolves all the expressions, types, etc.
//!
//! If you wonder why there's no `early.rs`, that's because it's split into three files -
//! `build_reduced_graph.rs`, `macros.rs` and `imports.rs`.

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


mod diagnostics;
mod types;
mod visitor;
mod lifetime;
mod item;
mod pattern;
mod path;
mod expr;
mod collect;

use diagnostics::{ElisionFnParameter, LifetimeElisionCandidate, MissingLifetime};

// Re-export all public types so external callers are unaffected
pub(crate) use types::*;

type Res = def::Res<NodeId>;

// ---- Core struct definitions ----

#[derive(Default, Debug)]
pub(crate) struct DiagMetadata<'ast> {
    /// The current trait's associated items' ident, used for diagnostic suggestions.
    current_trait_assoc_items: Option<&'ast [Box<AssocItem>]>,

    /// The current self type if inside an impl (used for better errors).
    pub(crate) current_self_type: Option<Ty>,

    /// The current self item if inside an ADT (used for better errors).
    current_self_item: Option<NodeId>,

    /// The current item being evaluated (used for suggestions and more detail in errors).
    pub(crate) current_item: Option<&'ast Item>,

    /// When processing generic arguments and encountering an unresolved ident not found,
    /// suggest introducing a type or const param depending on the context.
    currently_processing_generic_args: bool,

    /// The current enclosing (non-closure) function (used for better errors).
    current_function: Option<(FnKind<'ast>, Span)>,

    /// A list of labels as of yet unused. Labels will be removed from this map when
    /// they are used (in a `break` or `continue` statement)
    unused_labels: FxIndexMap<NodeId, Span>,

    /// Only used for better errors on `let <pat>: <expr, not type>;`.
    current_let_binding: Option<(Span, Option<Span>, Option<Span>)>,

    current_pat: Option<&'ast Pat>,

    /// Used to detect possible `if let` written without `let` and to provide structured suggestion.
    in_if_condition: Option<&'ast Expr>,

    /// Used to detect possible new binding written without `let` and to provide structured suggestion.
    in_assignment: Option<&'ast Expr>,
    is_assign_rhs: bool,

    /// If we are setting an associated type in trait impl, is it a non-GAT type?
    in_non_gat_assoc_type: Option<bool>,

    /// Used to detect possible `.` -> `..` typo when calling methods.
    in_range: Option<(&'ast Expr, &'ast Expr)>,

    /// If we are currently in a trait object definition. Used to point at the bounds when
    /// encountering a struct or enum.
    current_trait_object: Option<&'ast [ast::GenericBound]>,

    /// Given `where <T as Bar>::Baz: String`, suggest `where T: Bar<Baz = String>`.
    current_where_predicate: Option<&'ast WherePredicate>,

    current_type_path: Option<&'ast Ty>,

    /// The current impl items (used to suggest).
    current_impl_items: Option<&'ast [Box<AssocItem>]>,

    /// The current impl items (used to suggest).
    current_impl_item: Option<&'ast AssocItem>,

    /// When processing impl trait
    currently_processing_impl_trait: Option<(TraitRef, Ty)>,

    /// Accumulate the errors due to missed lifetime elision,
    /// and report them all at once for each function.
    current_elision_failures:
        Vec<(MissingLifetime, LifetimeElisionCandidate, Either<NodeId, Range<NodeId>>)>,
}

struct LateResolutionVisitor<'a, 'ast, 'ra, 'tcx> {
    r: &'a mut Resolver<'ra, 'tcx>,

    /// The module that represents the current item scope.
    parent_scope: ParentScope<'ra>,

    /// The current set of local scopes for types and values.
    ribs: PerNS<Vec<Rib<'ra>>>,

    /// Previous popped `rib`, only used for diagnostic.
    last_block_rib: Option<Rib<'ra>>,

    /// The current set of local scopes, for labels.
    label_ribs: Vec<Rib<'ra, NodeId>>,

    /// The current set of local scopes for lifetimes.
    lifetime_ribs: Vec<LifetimeRib>,

    /// We are looking for lifetimes in an elision context.
    /// The set contains all the resolutions that we encountered so far.
    /// They will be used to determine the correct lifetime for the fn return type.
    /// The `LifetimeElisionCandidate` is used for diagnostics, to suggest introducing named
    /// lifetimes.
    lifetime_elision_candidates: Option<Vec<(LifetimeRes, LifetimeElisionCandidate)>>,

    /// The trait that the current context can refer to.
    current_trait_ref: Option<(Module<'ra>, TraitRef)>,

    /// Fields used to add information to diagnostic errors.
    diag_metadata: Box<DiagMetadata<'ast>>,

    /// State used to know whether to ignore resolution errors for function bodies.
    ///
    /// In particular, rustdoc uses this to avoid giving errors for `cfg()` items.
    /// In most cases this will be `None`, in which case errors will always be reported.
    /// If it is `true`, then it will be updated when entering a nested function or trait body.
    in_func_body: bool,

    /// Count the number of places a lifetime is used.
    lifetime_uses: FxHashMap<LocalDefId, LifetimeUseSet>,
}

// ---- Core constructor and resolve helpers ----

/// Walks the whole crate in DFS order, visiting each item, resolving names as it goes.
impl<'a, 'ast, 'ra, 'tcx> LateResolutionVisitor<'a, 'ast, 'ra, 'tcx> {
    fn new(resolver: &'a mut Resolver<'ra, 'tcx>) -> LateResolutionVisitor<'a, 'ast, 'ra, 'tcx> {
        // During late resolution we only track the module component of the parent scope,
        // although it may be useful to track other components as well for diagnostics.
        let graph_root = resolver.graph_root;
        let parent_scope = ParentScope::module(graph_root, resolver.arenas);
        let start_rib_kind = RibKind::Module(graph_root);
        LateResolutionVisitor {
            r: resolver,
            parent_scope,
            ribs: PerNS {
                value_ns: vec![Rib::new(start_rib_kind)],
                type_ns: vec![Rib::new(start_rib_kind)],
                macro_ns: vec![Rib::new(start_rib_kind)],
            },
            last_block_rib: None,
            label_ribs: Vec::new(),
            lifetime_ribs: Vec::new(),
            lifetime_elision_candidates: None,
            current_trait_ref: None,
            diag_metadata: Default::default(),
            // errors at module scope should always be reported
            in_func_body: false,
            lifetime_uses: Default::default(),
        }
    }

    fn maybe_resolve_ident_in_lexical_scope(
        &mut self,
        ident: Ident,
        ns: Namespace,
    ) -> Option<LateDecl<'ra>> {
        self.r.resolve_ident_in_lexical_scope(
            ident,
            ns,
            &self.parent_scope,
            None,
            &self.ribs[ns],
            None,
            Some(&self.diag_metadata),
        )
    }

    fn resolve_ident_in_lexical_scope(
        &mut self,
        ident: Ident,
        ns: Namespace,
        finalize: Option<Finalize>,
        ignore_decl: Option<Decl<'ra>>,
    ) -> Option<LateDecl<'ra>> {
        self.r.resolve_ident_in_lexical_scope(
            ident,
            ns,
            &self.parent_scope,
            finalize,
            &self.ribs[ns],
            ignore_decl,
            Some(&self.diag_metadata),
        )
    }

    fn resolve_path(
        &mut self,
        path: &[Segment],
        opt_ns: Option<Namespace>, // `None` indicates a module path in import
        finalize: Option<Finalize>,
        source: PathSource<'_, 'ast, 'ra>,
    ) -> PathResult<'ra> {
        self.r.cm().resolve_path_with_ribs(
            path,
            opt_ns,
            &self.parent_scope,
            Some(source),
            finalize.map(|finalize| Finalize { stage: Stage::Late, ..finalize }),
            Some(&self.ribs),
            None,
            None,
            Some(&self.diag_metadata),
        )
    }

    // AST resolution
    //
    // We maintain a list of value ribs and type ribs.
    //
    // Simultaneously, we keep track of the current position in the module
    // graph in the `parent_scope.module` pointer. When we go to resolve a name in
    // the value or type namespaces, we first look through all the ribs and
    // then query the module graph. When we resolve a name in the module
    // namespace, we can skip all the ribs (since nested modules are not
    // allowed within blocks in Rust) and jump straight to the current module
    // graph node.
    //
    // Named implementations are handled separately. When we find a method
    // call, we consult the module node to find all of the implementations in
    // scope. This information is lazily cached in the module node. We then
    // generate a fake "implementation scope" containing all the
    // implementations thus found, for compatibility with old resolve pass.


}
