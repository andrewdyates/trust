// tRust: split from hir.rs for maintainability
use super::*;

pub enum OwnerNode<'hir> {
    Item(&'hir Item<'hir>),
    ForeignItem(&'hir ForeignItem<'hir>),
    TraitItem(&'hir TraitItem<'hir>),
    ImplItem(&'hir ImplItem<'hir>),
    Crate(&'hir Mod<'hir>),
    Synthetic,
}

impl<'hir> OwnerNode<'hir> {
    pub fn span(&self) -> Span {
        match self {
            OwnerNode::Item(Item { span, .. })
            | OwnerNode::ForeignItem(ForeignItem { span, .. })
            | OwnerNode::ImplItem(ImplItem { span, .. })
            | OwnerNode::TraitItem(TraitItem { span, .. }) => *span,
            OwnerNode::Crate(Mod { spans: ModSpans { inner_span, .. }, .. }) => *inner_span,
            OwnerNode::Synthetic => unreachable!(),
        }
    }

    pub fn fn_sig(self) -> Option<&'hir FnSig<'hir>> {
        match self {
            OwnerNode::TraitItem(TraitItem { kind: TraitItemKind::Fn(fn_sig, _), .. })
            | OwnerNode::ImplItem(ImplItem { kind: ImplItemKind::Fn(fn_sig, _), .. })
            | OwnerNode::Item(Item { kind: ItemKind::Fn { sig: fn_sig, .. }, .. })
            | OwnerNode::ForeignItem(ForeignItem {
                kind: ForeignItemKind::Fn(fn_sig, _, _), ..
            }) => Some(fn_sig),
            _ => None,
        }
    }

    pub fn fn_decl(self) -> Option<&'hir FnDecl<'hir>> {
        match self {
            OwnerNode::TraitItem(TraitItem { kind: TraitItemKind::Fn(fn_sig, _), .. })
            | OwnerNode::ImplItem(ImplItem { kind: ImplItemKind::Fn(fn_sig, _), .. })
            | OwnerNode::Item(Item { kind: ItemKind::Fn { sig: fn_sig, .. }, .. })
            | OwnerNode::ForeignItem(ForeignItem {
                kind: ForeignItemKind::Fn(fn_sig, _, _), ..
            }) => Some(fn_sig.decl),
            _ => None,
        }
    }

    pub fn body_id(&self) -> Option<BodyId> {
        match self {
            OwnerNode::Item(Item {
                kind:
                    ItemKind::Static(_, _, _, body)
                    | ItemKind::Const(.., ConstItemRhs::Body(body))
                    | ItemKind::Fn { body, .. },
                ..
            })
            | OwnerNode::TraitItem(TraitItem {
                kind:
                    TraitItemKind::Fn(_, TraitFn::Provided(body))
                    | TraitItemKind::Const(_, Some(ConstItemRhs::Body(body)), _),
                ..
            })
            | OwnerNode::ImplItem(ImplItem {
                kind: ImplItemKind::Fn(_, body) | ImplItemKind::Const(_, ConstItemRhs::Body(body)),
                ..
            }) => Some(*body),
            _ => None,
        }
    }

    pub fn generics(self) -> Option<&'hir Generics<'hir>> {
        Node::generics(self.into())
    }

    pub fn def_id(self) -> OwnerId {
        match self {
            OwnerNode::Item(Item { owner_id, .. })
            | OwnerNode::TraitItem(TraitItem { owner_id, .. })
            | OwnerNode::ImplItem(ImplItem { owner_id, .. })
            | OwnerNode::ForeignItem(ForeignItem { owner_id, .. }) => *owner_id,
            OwnerNode::Crate(..) => crate::CRATE_HIR_ID.owner,
            OwnerNode::Synthetic => unreachable!(),
        }
    }

    /// Check if node is an impl block.
    pub fn is_impl_block(&self) -> bool {
        matches!(self, OwnerNode::Item(Item { kind: ItemKind::Impl(_), .. }))
    }

    expect_methods_self! {
        expect_item,         &'hir Item<'hir>,        OwnerNode::Item(n),        n;
        expect_foreign_item, &'hir ForeignItem<'hir>, OwnerNode::ForeignItem(n), n;
        expect_impl_item,    &'hir ImplItem<'hir>,    OwnerNode::ImplItem(n),    n;
        expect_trait_item,   &'hir TraitItem<'hir>,   OwnerNode::TraitItem(n),   n;
    }
}

impl<'hir> From<&'hir Item<'hir>> for OwnerNode<'hir> {
    fn from(val: &'hir Item<'hir>) -> Self {
        OwnerNode::Item(val)
    }
}

impl<'hir> From<&'hir ForeignItem<'hir>> for OwnerNode<'hir> {
    fn from(val: &'hir ForeignItem<'hir>) -> Self {
        OwnerNode::ForeignItem(val)
    }
}

impl<'hir> From<&'hir ImplItem<'hir>> for OwnerNode<'hir> {
    fn from(val: &'hir ImplItem<'hir>) -> Self {
        OwnerNode::ImplItem(val)
    }
}

impl<'hir> From<&'hir TraitItem<'hir>> for OwnerNode<'hir> {
    fn from(val: &'hir TraitItem<'hir>) -> Self {
        OwnerNode::TraitItem(val)
    }
}

impl<'hir> From<OwnerNode<'hir>> for Node<'hir> {
    fn from(val: OwnerNode<'hir>) -> Self {
        match val {
            OwnerNode::Item(n) => Node::Item(n),
            OwnerNode::ForeignItem(n) => Node::ForeignItem(n),
            OwnerNode::ImplItem(n) => Node::ImplItem(n),
            OwnerNode::TraitItem(n) => Node::TraitItem(n),
            OwnerNode::Crate(n) => Node::Crate(n),
            OwnerNode::Synthetic => Node::Synthetic,
        }
    }
}

#[derive(Copy, Clone, Debug, HashStable_Generic)]
pub enum Node<'hir> {
    Param(&'hir Param<'hir>),
    Item(&'hir Item<'hir>),
    ForeignItem(&'hir ForeignItem<'hir>),
    TraitItem(&'hir TraitItem<'hir>),
    ImplItem(&'hir ImplItem<'hir>),
    Variant(&'hir Variant<'hir>),
    Field(&'hir FieldDef<'hir>),
    AnonConst(&'hir AnonConst),
    ConstBlock(&'hir ConstBlock),
    ConstArg(&'hir ConstArg<'hir>),
    Expr(&'hir Expr<'hir>),
    ExprField(&'hir ExprField<'hir>),
    ConstArgExprField(&'hir ConstArgExprField<'hir>),
    Stmt(&'hir Stmt<'hir>),
    PathSegment(&'hir PathSegment<'hir>),
    Ty(&'hir Ty<'hir>),
    AssocItemConstraint(&'hir AssocItemConstraint<'hir>),
    TraitRef(&'hir TraitRef<'hir>),
    OpaqueTy(&'hir OpaqueTy<'hir>),
    TyPat(&'hir TyPat<'hir>),
    Pat(&'hir Pat<'hir>),
    PatField(&'hir PatField<'hir>),
    /// Needed as its own node with its own HirId for tracking
    /// the unadjusted type of literals within patterns
    /// (e.g. byte str literals not being of slice type).
    PatExpr(&'hir PatExpr<'hir>),
    Arm(&'hir Arm<'hir>),
    Block(&'hir Block<'hir>),
    LetStmt(&'hir LetStmt<'hir>),
    /// `Ctor` refers to the constructor of an enum variant or struct. Only tuple or unit variants
    /// with synthesized constructors.
    Ctor(&'hir VariantData<'hir>),
    Lifetime(&'hir Lifetime),
    GenericParam(&'hir GenericParam<'hir>),
    Crate(&'hir Mod<'hir>),
    Infer(&'hir InferArg),
    WherePredicate(&'hir WherePredicate<'hir>),
    PreciseCapturingNonLifetimeArg(&'hir PreciseCapturingNonLifetimeArg),
    // Created by query feeding
    Synthetic,
    Err(Span),
}

impl<'hir> Node<'hir> {
    /// Get the identifier of this `Node`, if applicable.
    ///
    /// # Edge cases
    ///
    /// Calling `.ident()` on a [`Node::Ctor`] will return `None`
    /// because `Ctor`s do not have identifiers themselves.
    /// Instead, call `.ident()` on the parent struct/variant, like so:
    ///
    /// ```ignore (illustrative)
    /// ctor
    ///     .ctor_hir_id()
    ///     .map(|ctor_id| tcx.parent_hir_node(ctor_id))
    ///     .and_then(|parent| parent.ident())
    /// ```
    pub fn ident(&self) -> Option<Ident> {
        match self {
            Node::Item(item) => item.kind.ident(),
            Node::TraitItem(TraitItem { ident, .. })
            | Node::ImplItem(ImplItem { ident, .. })
            | Node::ForeignItem(ForeignItem { ident, .. })
            | Node::Field(FieldDef { ident, .. })
            | Node::Variant(Variant { ident, .. })
            | Node::PathSegment(PathSegment { ident, .. }) => Some(*ident),
            Node::Lifetime(lt) => Some(lt.ident),
            Node::GenericParam(p) => Some(p.name.ident()),
            Node::AssocItemConstraint(c) => Some(c.ident),
            Node::PatField(f) => Some(f.ident),
            Node::ExprField(f) => Some(f.ident),
            Node::ConstArgExprField(f) => Some(f.field),
            Node::PreciseCapturingNonLifetimeArg(a) => Some(a.ident),
            Node::Param(..)
            | Node::AnonConst(..)
            | Node::ConstBlock(..)
            | Node::ConstArg(..)
            | Node::Expr(..)
            | Node::Stmt(..)
            | Node::Block(..)
            | Node::Ctor(..)
            | Node::Pat(..)
            | Node::TyPat(..)
            | Node::PatExpr(..)
            | Node::Arm(..)
            | Node::LetStmt(..)
            | Node::Crate(..)
            | Node::Ty(..)
            | Node::TraitRef(..)
            | Node::OpaqueTy(..)
            | Node::Infer(..)
            | Node::WherePredicate(..)
            | Node::Synthetic
            | Node::Err(..) => None,
        }
    }

    pub fn fn_decl(self) -> Option<&'hir FnDecl<'hir>> {
        match self {
            Node::TraitItem(TraitItem { kind: TraitItemKind::Fn(fn_sig, _), .. })
            | Node::ImplItem(ImplItem { kind: ImplItemKind::Fn(fn_sig, _), .. })
            | Node::Item(Item { kind: ItemKind::Fn { sig: fn_sig, .. }, .. })
            | Node::ForeignItem(ForeignItem { kind: ForeignItemKind::Fn(fn_sig, _, _), .. }) => {
                Some(fn_sig.decl)
            }
            Node::Expr(Expr { kind: ExprKind::Closure(Closure { fn_decl, .. }), .. }) => {
                Some(fn_decl)
            }
            _ => None,
        }
    }

    /// Get a `hir::Impl` if the node is an impl block for the given `trait_def_id`.
    pub fn impl_block_of_trait(self, trait_def_id: DefId) -> Option<&'hir Impl<'hir>> {
        if let Node::Item(Item { kind: ItemKind::Impl(impl_block), .. }) = self
            && let Some(of_trait) = impl_block.of_trait
            && let Some(trait_id) = of_trait.trait_ref.trait_def_id()
            && trait_id == trait_def_id
        {
            Some(impl_block)
        } else {
            None
        }
    }

    pub fn fn_sig(self) -> Option<&'hir FnSig<'hir>> {
        match self {
            Node::TraitItem(TraitItem { kind: TraitItemKind::Fn(fn_sig, _), .. })
            | Node::ImplItem(ImplItem { kind: ImplItemKind::Fn(fn_sig, _), .. })
            | Node::Item(Item { kind: ItemKind::Fn { sig: fn_sig, .. }, .. })
            | Node::ForeignItem(ForeignItem { kind: ForeignItemKind::Fn(fn_sig, _, _), .. }) => {
                Some(fn_sig)
            }
            _ => None,
        }
    }

    /// Get the type for constants, assoc types, type aliases and statics.
    pub fn ty(self) -> Option<&'hir Ty<'hir>> {
        match self {
            Node::Item(it) => match it.kind {
                ItemKind::TyAlias(_, _, ty)
                | ItemKind::Static(_, _, ty, _)
                | ItemKind::Const(_, _, ty, _) => Some(ty),
                ItemKind::Impl(impl_item) => Some(&impl_item.self_ty),
                _ => None,
            },
            Node::TraitItem(it) => match it.kind {
                TraitItemKind::Const(ty, _, _) => Some(ty),
                TraitItemKind::Type(_, ty) => ty,
                _ => None,
            },
            Node::ImplItem(it) => match it.kind {
                ImplItemKind::Const(ty, _) => Some(ty),
                ImplItemKind::Type(ty) => Some(ty),
                _ => None,
            },
            Node::ForeignItem(it) => match it.kind {
                ForeignItemKind::Static(ty, ..) => Some(ty),
                _ => None,
            },
            Node::GenericParam(param) => match param.kind {
                GenericParamKind::Lifetime { .. } => None,
                GenericParamKind::Type { default, .. } => default,
                GenericParamKind::Const { ty, .. } => Some(ty),
            },
            _ => None,
        }
    }

    pub fn alias_ty(self) -> Option<&'hir Ty<'hir>> {
        match self {
            Node::Item(Item { kind: ItemKind::TyAlias(_, _, ty), .. }) => Some(ty),
            _ => None,
        }
    }

    #[inline]
    pub fn associated_body(&self) -> Option<(LocalDefId, BodyId)> {
        match self {
            Node::Item(Item {
                owner_id,
                kind:
                    ItemKind::Const(.., ConstItemRhs::Body(body))
                    | ItemKind::Static(.., body)
                    | ItemKind::Fn { body, .. },
                ..
            })
            | Node::TraitItem(TraitItem {
                owner_id,
                kind:
                    TraitItemKind::Const(_, Some(ConstItemRhs::Body(body)), _)
                    | TraitItemKind::Fn(_, TraitFn::Provided(body)),
                ..
            })
            | Node::ImplItem(ImplItem {
                owner_id,
                kind: ImplItemKind::Const(.., ConstItemRhs::Body(body)) | ImplItemKind::Fn(_, body),
                ..
            }) => Some((owner_id.def_id, *body)),

            Node::Item(Item {
                owner_id, kind: ItemKind::GlobalAsm { asm: _, fake_body }, ..
            }) => Some((owner_id.def_id, *fake_body)),

            Node::Expr(Expr { kind: ExprKind::Closure(Closure { def_id, body, .. }), .. }) => {
                Some((*def_id, *body))
            }

            Node::AnonConst(constant) => Some((constant.def_id, constant.body)),
            Node::ConstBlock(constant) => Some((constant.def_id, constant.body)),

            _ => None,
        }
    }

    pub fn body_id(&self) -> Option<BodyId> {
        Some(self.associated_body()?.1)
    }

    pub fn generics(self) -> Option<&'hir Generics<'hir>> {
        match self {
            Node::ForeignItem(ForeignItem {
                kind: ForeignItemKind::Fn(_, _, generics), ..
            })
            | Node::TraitItem(TraitItem { generics, .. })
            | Node::ImplItem(ImplItem { generics, .. }) => Some(generics),
            Node::Item(item) => item.kind.generics(),
            _ => None,
        }
    }

    pub fn as_owner(self) -> Option<OwnerNode<'hir>> {
        match self {
            Node::Item(i) => Some(OwnerNode::Item(i)),
            Node::ForeignItem(i) => Some(OwnerNode::ForeignItem(i)),
            Node::TraitItem(i) => Some(OwnerNode::TraitItem(i)),
            Node::ImplItem(i) => Some(OwnerNode::ImplItem(i)),
            Node::Crate(i) => Some(OwnerNode::Crate(i)),
            Node::Synthetic => Some(OwnerNode::Synthetic),
            _ => None,
        }
    }

    pub fn fn_kind(self) -> Option<FnKind<'hir>> {
        match self {
            Node::Item(i) => match i.kind {
                ItemKind::Fn { ident, sig, generics, .. } => {
                    Some(FnKind::ItemFn(ident, generics, sig.header))
                }
                _ => None,
            },
            Node::TraitItem(ti) => match ti.kind {
                TraitItemKind::Fn(ref sig, _) => Some(FnKind::Method(ti.ident, sig)),
                _ => None,
            },
            Node::ImplItem(ii) => match ii.kind {
                ImplItemKind::Fn(ref sig, _) => Some(FnKind::Method(ii.ident, sig)),
                _ => None,
            },
            Node::Expr(e) => match e.kind {
                ExprKind::Closure { .. } => Some(FnKind::Closure),
                _ => None,
            },
            _ => None,
        }
    }

    expect_methods_self! {
        expect_param,         &'hir Param<'hir>,        Node::Param(n),        n;
        expect_item,          &'hir Item<'hir>,         Node::Item(n),         n;
        expect_foreign_item,  &'hir ForeignItem<'hir>,  Node::ForeignItem(n),  n;
        expect_trait_item,    &'hir TraitItem<'hir>,    Node::TraitItem(n),    n;
        expect_impl_item,     &'hir ImplItem<'hir>,     Node::ImplItem(n),     n;
        expect_variant,       &'hir Variant<'hir>,      Node::Variant(n),      n;
        expect_field,         &'hir FieldDef<'hir>,     Node::Field(n),        n;
        expect_anon_const,    &'hir AnonConst,          Node::AnonConst(n),    n;
        expect_inline_const,  &'hir ConstBlock,         Node::ConstBlock(n),   n;
        expect_expr,          &'hir Expr<'hir>,         Node::Expr(n),         n;
        expect_expr_field,    &'hir ExprField<'hir>,    Node::ExprField(n),    n;
        expect_stmt,          &'hir Stmt<'hir>,         Node::Stmt(n),         n;
        expect_path_segment,  &'hir PathSegment<'hir>,  Node::PathSegment(n),  n;
        expect_ty,            &'hir Ty<'hir>,           Node::Ty(n),           n;
        expect_assoc_item_constraint,  &'hir AssocItemConstraint<'hir>,  Node::AssocItemConstraint(n),  n;
        expect_trait_ref,     &'hir TraitRef<'hir>,     Node::TraitRef(n),     n;
        expect_opaque_ty,     &'hir OpaqueTy<'hir>,     Node::OpaqueTy(n),     n;
        expect_pat,           &'hir Pat<'hir>,          Node::Pat(n),          n;
        expect_pat_field,     &'hir PatField<'hir>,     Node::PatField(n),     n;
        expect_arm,           &'hir Arm<'hir>,          Node::Arm(n),          n;
        expect_block,         &'hir Block<'hir>,        Node::Block(n),        n;
        expect_let_stmt,      &'hir LetStmt<'hir>,      Node::LetStmt(n),      n;
        expect_ctor,          &'hir VariantData<'hir>,  Node::Ctor(n),         n;
        expect_lifetime,      &'hir Lifetime,           Node::Lifetime(n),     n;
        expect_generic_param, &'hir GenericParam<'hir>, Node::GenericParam(n), n;
        expect_crate,         &'hir Mod<'hir>,          Node::Crate(n),        n;
        expect_infer,         &'hir InferArg,           Node::Infer(n),        n;
        expect_closure,       &'hir Closure<'hir>, Node::Expr(Expr { kind: ExprKind::Closure(n), .. }), n;
    }
}
