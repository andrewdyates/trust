// tRust: MIR lint that warns when float/vector arguments cross target-feature
// tRust: boundaries where the ABI might differ (rust-lang#116344, rust-lang#116573).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_middle::middle::codegen_fn_attrs::TargetFeatureKind;
use rustc_middle::mir::{Body, Operand, TerminatorKind};
use rustc_middle::ty::{self, Ty, TyCtxt};

use crate::pass_manager::MirLint;

pub(super) struct CheckTargetFeatureAbi;

impl<'tcx> MirLint<'tcx> for CheckTargetFeatureAbi {
    fn run_lint(&self, tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
        check_target_feature_abi(tcx, body);
    }
}

/// Target features that affect the ABI of floating-point types on x86/x86_64.
/// When these differ between caller and callee, float arguments may be passed
/// via different registers (x87 vs SSE/AVX), causing silent miscompilation.
// tRust: soundness — these features change how floats are passed in registers
const X86_FLOAT_ABI_FEATURES: &[&str] = &["sse", "sse2", "avx", "avx512f"];

/// Target features that affect float ABI on AArch64 (neon/softfloat).
const AARCH64_FLOAT_ABI_FEATURES: &[&str] = &["neon", "fp-armv8"];

/// Check whether a type contains floating-point components that could be
/// affected by ABI differences when target features differ.
fn type_has_float_component<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::Float(_) => true,
        ty::Tuple(fields) => fields.iter().any(|f| type_has_float_component(tcx, f)),
        ty::Adt(adt_def, args) if adt_def.is_struct() => {
            adt_def
                .all_fields()
                .any(|field| type_has_float_component(tcx, field.ty(tcx, args)))
        }
        ty::Array(elem, _) => type_has_float_component(tcx, *elem),
        _ => false,
    }
}

/// Returns the set of float-ABI-relevant features enabled for a function,
/// considering both explicit `#[target_feature]` and session-level features.
fn get_float_abi_features<'tcx>(
    tcx: TyCtxt<'tcx>,
    features: &[rustc_middle::middle::codegen_fn_attrs::TargetFeature],
    arch: &str,
) -> Vec<&'static str> {
    let relevant = match arch {
        "x86" | "x86_64" => X86_FLOAT_ABI_FEATURES,
        "aarch64" | "arm64ec" => AARCH64_FLOAT_ABI_FEATURES,
        _ => return Vec::new(),
    };

    let session_features: Vec<_> = tcx
        .sess
        .target_features
        .iter()
        .filter_map(|f| {
            let name = f.as_str();
            relevant.iter().find(|&&r| r == name).copied()
        })
        .collect();

    let fn_features: Vec<_> = features
        .iter()
        .filter_map(|f| {
            let name = f.name.as_str();
            relevant.iter().find(|&&r| r == name).copied()
        })
        .collect();

    // Combine session + function-level features (dedup)
    let mut all = session_features;
    for f in fn_features {
        if !all.contains(&f) {
            all.push(f);
        }
    }
    all
}

/// Main lint: detect calls where caller and callee have different float-ABI-relevant
/// target features AND the call passes float arguments.
#[inline]
fn check_target_feature_abi<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
    let caller_def_id = body.source.def_id().expect_local();
    if !tcx.def_kind(caller_def_id).has_codegen_attrs() {
        return;
    }

    let arch = tcx.sess.target.arch.as_ref();
    // tRust: only check architectures where target features affect float ABI
    if !matches!(arch, "x86" | "x86_64" | "aarch64" | "arm64ec") {
        return;
    }

    let caller_attrs = tcx.codegen_fn_attrs(caller_def_id);
    let caller_float_features =
        get_float_abi_features(tcx, &caller_attrs.target_features, arch);

    for bb in body.basic_blocks.iter() {
        let terminator = bb.terminator();
        let (func, args) = match &terminator.kind {
            TerminatorKind::Call { func, args, .. } => (func, args),
            TerminatorKind::TailCall { func, args, .. } => (func, args),
            _ => continue,
        };

        let fn_ty = func.ty(body, tcx);
        let ty::FnDef(callee_def_id, _) = *fn_ty.kind() else {
            continue;
        };

        if !tcx.def_kind(callee_def_id).has_codegen_attrs() {
            continue;
        }

        let callee_attrs = tcx.codegen_fn_attrs(callee_def_id);
        let callee_float_features =
            get_float_abi_features(tcx, &callee_attrs.target_features, arch);

        // tRust: if float-ABI features match, no issue
        if caller_float_features == callee_float_features {
            continue;
        }

        // tRust: check if any argument or the return type contains floats
        let has_float_args = args.iter().any(|arg| {
            let ty = match arg {
                Operand::Copy(place) | Operand::Move(place) => place.ty(body, tcx).ty,
                Operand::Constant(c) => c.ty(),
            };
            type_has_float_component(tcx, ty)
        });

        let fn_sig = fn_ty.fn_sig(tcx).skip_binder();
        let has_float_return = type_has_float_component(tcx, fn_sig.output());

        if !has_float_args && !has_float_return {
            continue;
        }

        // tRust: emit diagnostic — this call may have ABI mismatch
        let caller_only: Vec<_> = caller_float_features
            .iter()
            .filter(|f| !callee_float_features.contains(f))
            .copied()
            .collect();
        let callee_only: Vec<_> = callee_float_features
            .iter()
            .filter(|f| !caller_float_features.contains(f))
            .copied()
            .collect();

        // tRust: only warn about user-specified target feature mismatches
        let callee_has_explicit_features = callee_attrs
            .target_features
            .iter()
            .any(|f| matches!(f.kind, TargetFeatureKind::Enabled));
        let caller_has_explicit_features = caller_attrs
            .target_features
            .iter()
            .any(|f| matches!(f.kind, TargetFeatureKind::Enabled));

        if !callee_has_explicit_features && !caller_has_explicit_features {
            continue;
        }

        crate::errors::emit_target_feature_float_abi_diagnostic(
            tcx,
            terminator.source_info.span,
            callee_def_id,
            caller_def_id.into(),
            &caller_only,
            &callee_only,
        );
    }
}
