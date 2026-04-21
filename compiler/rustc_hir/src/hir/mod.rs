// ignore-tidy-filelength
use std::borrow::Cow;
use std::fmt;
use std::ops::Not;

use rustc_abi::ExternAbi;
use rustc_ast::attr::AttributeExt;
use rustc_ast::token::DocFragmentKind;
use rustc_ast::util::parser::ExprPrecedence;
use rustc_ast::{
    self as ast, FloatTy, InlineAsmOptions, InlineAsmTemplatePiece, IntTy, Label, LitIntType,
    LitKind, TraitObjectSyntax, UintTy, UnsafeBinderCastKind, join_path_idents,
};
pub use rustc_ast::{
    AssignOp, AssignOpKind, AttrId, AttrStyle, BinOp, BinOpKind, BindingMode, BorrowKind,
    BoundConstness, BoundPolarity, ByRef, CaptureBy, DelimArgs, ImplPolarity, IsAuto,
    MetaItemInner, MetaItemLit, Movability, Mutability, Pinnedness, UnOp,
};
use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::sorted_map::SortedMap;
use rustc_data_structures::tagged_ptr::TaggedRef;
use rustc_error_messages::{DiagArgValue, IntoDiagArg};
use rustc_index::IndexVec;
use rustc_macros::{Decodable, Encodable, HashStable_Generic};
use rustc_span::def_id::LocalDefId;
use rustc_span::{
    BytePos, DUMMY_SP, DesugaringKind, ErrorGuaranteed, Ident, Span, Spanned, Symbol, kw, sym,
};
use rustc_target::asm::InlineAsmRegOrRegClass;
use smallvec::SmallVec;
use thin_vec::ThinVec;
use tracing::debug;

use crate::attrs::AttributeKind;
use crate::def::{CtorKind, DefKind, MacroKinds, PerNS, Res};
use crate::def_id::{DefId, LocalDefIdMap};
pub(crate) use crate::hir_id::{HirId, ItemLocalId, ItemLocalMap, OwnerId};
use crate::intravisit::{FnKind, VisitorExt};
use crate::lints::DelayedLints;


// tRust: Submodules split from the original monolithic hir.rs for maintainability.
// Each submodule contains a logical grouping of HIR types and their implementations.

// Macros used across multiple submodules (item.rs and node.rs).
// Defined here before submodule declarations so they are visible by textual scope.
macro_rules! expect_methods_self_kind {
    ( $( $name:ident, $ret_ty:ty, $pat:pat, $ret_val:expr; )* ) => {
        $(
            #[track_caller]
            pub fn $name(&self) -> $ret_ty {
                let $pat = &self.kind else { expect_failed(stringify!($name), self) };
                $ret_val
            }
        )*
    }
}

macro_rules! expect_methods_self {
    ( $( $name:ident, $ret_ty:ty, $pat:pat, $ret_val:expr; )* ) => {
        $(
            #[track_caller]
            pub fn $name(&self) -> $ret_ty {
                let $pat = self else { expect_failed(stringify!($name), self) };
                $ret_val
            }
        )*
    }
}

#[track_caller]
fn expect_failed<T: fmt::Debug>(ident: &'static str, found: T) -> ! {
    panic!("{ident}: found {found:?}")
}

mod lifetime;
pub use lifetime::*;

mod path;
pub use path::*;

mod generics;
pub use generics::*;

mod attr;
pub use attr::*;

mod owner;
pub use owner::*;

mod pat;
pub use pat::*;

mod stmt;
pub use stmt::*;

mod expr;
pub use expr::*;

mod item;
pub use item::*;

mod ty;
pub use ty::*;

mod defs;
pub use defs::*;

mod node;
pub use node::*;

// Some nodes are used a lot. Make sure they don't unintentionally get bigger.
#[cfg(target_pointer_width = "64")]
mod size_asserts {
    use rustc_data_structures::static_assert_size;

    use super::*;
    // tidy-alphabetical-start
    static_assert_size!(Block<'_>, 48);
    static_assert_size!(Body<'_>, 24);
    static_assert_size!(Expr<'_>, 64);
    static_assert_size!(ExprKind<'_>, 48);
    static_assert_size!(FnDecl<'_>, 40);
    static_assert_size!(ForeignItem<'_>, 96);
    static_assert_size!(ForeignItemKind<'_>, 56);
    static_assert_size!(GenericArg<'_>, 16);
    static_assert_size!(GenericBound<'_>, 64);
    static_assert_size!(Generics<'_>, 56);
    static_assert_size!(Impl<'_>, 48);
    static_assert_size!(ImplItem<'_>, 88);
    static_assert_size!(ImplItemKind<'_>, 40);
    static_assert_size!(Item<'_>, 88);
    static_assert_size!(ItemKind<'_>, 64);
    static_assert_size!(LetStmt<'_>, 64);
    static_assert_size!(Param<'_>, 32);
    static_assert_size!(Pat<'_>, 80);
    static_assert_size!(PatKind<'_>, 56);
    static_assert_size!(Path<'_>, 40);
    static_assert_size!(PathSegment<'_>, 48);
    static_assert_size!(QPath<'_>, 24);
    static_assert_size!(Res, 12);
    static_assert_size!(Stmt<'_>, 32);
    static_assert_size!(StmtKind<'_>, 16);
    static_assert_size!(TraitImplHeader<'_>, 48);
    static_assert_size!(TraitItem<'_>, 88);
    static_assert_size!(TraitItemKind<'_>, 48);
    static_assert_size!(Ty<'_>, 48);
    static_assert_size!(TyKind<'_>, 32);
    // tidy-alphabetical-end
}

#[cfg(test)]
mod tests;

