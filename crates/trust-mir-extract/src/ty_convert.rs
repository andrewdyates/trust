// trust-mir-extract/ty_convert.rs: Convert rustc Ty to trust-types Ty
//
// Maps rustc's rich type system to our simplified verification types.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_middle::ty::{self, TyCtxt, TyKind};
use trust_types::Ty as TrustTy;

/// Convert a rustc Ty to our simplified Ty.
pub(crate) fn convert_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> TrustTy {
    match ty.kind() {
        TyKind::Bool => TrustTy::Bool,

        TyKind::Int(int_ty) => {
            let width = int_width_from_int_ty(int_ty, tcx);
            TrustTy::Int { width, signed: true }
        }

        TyKind::Uint(uint_ty) => {
            let width = uint_width_from_uint_ty(uint_ty, tcx);
            TrustTy::Int { width, signed: false }
        }

        TyKind::Float(float_ty) => {
            let width = match float_ty {
                rustc_ast_ir::FloatTy::F16 => 16,
                rustc_ast_ir::FloatTy::F32 => 32,
                rustc_ast_ir::FloatTy::F64 => 64,
                rustc_ast_ir::FloatTy::F128 => 128,
            };
            TrustTy::Float { width }
        }

        TyKind::Ref(_, inner_ty, mutability) => TrustTy::Ref {
            mutable: mutability.is_mut(),
            inner: Box::new(convert_ty(tcx, *inner_ty)),
        },

        TyKind::Slice(elem_ty) => TrustTy::Slice { elem: Box::new(convert_ty(tcx, *elem_ty)) },

        TyKind::Array(elem_ty, len_const) => {
            let len = len_const.try_to_target_usize(tcx).unwrap_or(0);
            TrustTy::Array { elem: Box::new(convert_ty(tcx, *elem_ty)), len }
        }

        TyKind::Tuple(fields) => {
            let field_tys: Vec<TrustTy> = fields.iter().map(|f| convert_ty(tcx, f)).collect();
            TrustTy::Tuple(field_tys)
        }

        TyKind::Adt(adt_def, args) => {
            let name = crate::safe_def_path_str(tcx, adt_def.did());
            let fields: Vec<(String, TrustTy)> = if adt_def.is_struct() {
                adt_def
                    .all_fields()
                    .map(|f| {
                        let field_name = f.name.to_string();
                        let field_ty = convert_ty(tcx, f.ty(tcx, args));
                        (field_name, field_ty)
                    })
                    .collect()
            } else {
                vec![]
            };
            TrustTy::Adt { name, fields }
        }

        TyKind::Never => TrustTy::Never,

        _ if ty.is_unit() => TrustTy::Unit,

        // Char: map to u32 for verification
        TyKind::Char => TrustTy::Int { width: 32, signed: false },

        // Raw pointers: treat as usize
        TyKind::RawPtr(_, _) => TrustTy::Int { width: pointer_width(tcx), signed: false },

        // Fallback
        _ => TrustTy::Unit,
    }
}

/// Get bit width of an IntTy.
pub(crate) fn int_width_from_int_ty(int_ty: &rustc_ast_ir::IntTy, tcx: TyCtxt<'_>) -> u32 {
    match int_ty {
        rustc_ast_ir::IntTy::Isize => pointer_width(tcx),
        rustc_ast_ir::IntTy::I8 => 8,
        rustc_ast_ir::IntTy::I16 => 16,
        rustc_ast_ir::IntTy::I32 => 32,
        rustc_ast_ir::IntTy::I64 => 64,
        rustc_ast_ir::IntTy::I128 => 128,
    }
}

/// Get bit width of a UintTy.
pub(crate) fn uint_width_from_uint_ty(uint_ty: &rustc_ast_ir::UintTy, tcx: TyCtxt<'_>) -> u32 {
    match uint_ty {
        rustc_ast_ir::UintTy::Usize => pointer_width(tcx),
        rustc_ast_ir::UintTy::U8 => 8,
        rustc_ast_ir::UintTy::U16 => 16,
        rustc_ast_ir::UintTy::U32 => 32,
        rustc_ast_ir::UintTy::U64 => 64,
        rustc_ast_ir::UintTy::U128 => 128,
    }
}

/// Get the pointer width in bits for the target.
fn pointer_width(tcx: TyCtxt<'_>) -> u32 {
    tcx.data_layout.pointer_size().bits() as u32
}
