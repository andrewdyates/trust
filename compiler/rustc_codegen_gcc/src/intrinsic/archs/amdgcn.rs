// tRust: split from archs.rs — amdgcn architecture intrinsics
fn amdgcn(name: &str, full_name: &str) -> &'static str {
    match name {
        // amdgcn
        "add.max.i32" => "__builtin_amdgcn_add_max_i32",
        "add.max.u32" => "__builtin_amdgcn_add_max_u32",
        "add.min.i32" => "__builtin_amdgcn_add_min_i32",
        "add.min.u32" => "__builtin_amdgcn_add_min_u32",
        "alignbyte" => "__builtin_amdgcn_alignbyte",
        "ashr.pk.i8.i32" => "__builtin_amdgcn_ashr_pk_i8_i32",
        "ashr.pk.u8.i32" => "__builtin_amdgcn_ashr_pk_u8_i32",
        "buffer.wbinvl1" => "__builtin_amdgcn_buffer_wbinvl1",
        "buffer.wbinvl1.sc" => "__builtin_amdgcn_buffer_wbinvl1_sc",
        "buffer.wbinvl1.vol" => "__builtin_amdgcn_buffer_wbinvl1_vol",
        "cluster.id.x" => "__builtin_amdgcn_cluster_id_x",
        "cluster.id.y" => "__builtin_amdgcn_cluster_id_y",
        "cluster.id.z" => "__builtin_amdgcn_cluster_id_z",
        "cluster.load.async.to.lds.b128" => {
            "__builtin_amdgcn_cluster_load_async_to_lds_b128"
        }
        "cluster.load.async.to.lds.b32" => {
            "__builtin_amdgcn_cluster_load_async_to_lds_b32"
        }
        "cluster.load.async.to.lds.b64" => {
            "__builtin_amdgcn_cluster_load_async_to_lds_b64"
        }
        "cluster.load.async.to.lds.b8" => {
            "__builtin_amdgcn_cluster_load_async_to_lds_b8"
        }
        "cluster.workgroup.flat.id" => "__builtin_amdgcn_cluster_workgroup_flat_id",
        "cluster.workgroup.id.x" => "__builtin_amdgcn_cluster_workgroup_id_x",
        "cluster.workgroup.id.y" => "__builtin_amdgcn_cluster_workgroup_id_y",
        "cluster.workgroup.id.z" => "__builtin_amdgcn_cluster_workgroup_id_z",
        "cluster.workgroup.max.flat.id" => {
            "__builtin_amdgcn_cluster_workgroup_max_flat_id"
        }
        "cluster.workgroup.max.id.x" => "__builtin_amdgcn_cluster_workgroup_max_id_x",
        "cluster.workgroup.max.id.y" => "__builtin_amdgcn_cluster_workgroup_max_id_y",
        "cluster.workgroup.max.id.z" => "__builtin_amdgcn_cluster_workgroup_max_id_z",
        "cubeid" => "__builtin_amdgcn_cubeid",
        "cubema" => "__builtin_amdgcn_cubema",
        "cubesc" => "__builtin_amdgcn_cubesc",
        "cubetc" => "__builtin_amdgcn_cubetc",
        "cvt.f16.bf8" => "__builtin_amdgcn_cvt_f16_bf8",
        "cvt.f16.fp8" => "__builtin_amdgcn_cvt_f16_fp8",
        "cvt.f32.bf8" => "__builtin_amdgcn_cvt_f32_bf8",
        "cvt.f32.fp8" => "__builtin_amdgcn_cvt_f32_fp8",
        "cvt.f32.fp8.e5m3" => "__builtin_amdgcn_cvt_f32_fp8_e5m3",
        "cvt.off.f32.i4" => "__builtin_amdgcn_cvt_off_f32_i4",
        "cvt.pk.bf8.f16" => "__builtin_amdgcn_cvt_pk_bf8_f16",
        "cvt.pk.bf8.f32" => "__builtin_amdgcn_cvt_pk_bf8_f32",
        "cvt.pk.f16.bf8" => "__builtin_amdgcn_cvt_pk_f16_bf8",
        "cvt.pk.f16.fp8" => "__builtin_amdgcn_cvt_pk_f16_fp8",
        "cvt.pk.f32.bf8" => "__builtin_amdgcn_cvt_pk_f32_bf8",
        "cvt.pk.f32.fp8" => "__builtin_amdgcn_cvt_pk_f32_fp8",
        "cvt.pk.fp8.f16" => "__builtin_amdgcn_cvt_pk_fp8_f16",
        "cvt.pk.fp8.f32" => "__builtin_amdgcn_cvt_pk_fp8_f32",
        "cvt.pk.fp8.f32.e5m3" => "__builtin_amdgcn_cvt_pk_fp8_f32_e5m3",
        "cvt.pk.i16" => "__builtin_amdgcn_cvt_pk_i16",
        "cvt.pk.u16" => "__builtin_amdgcn_cvt_pk_u16",
        "cvt.pk.u8.f32" => "__builtin_amdgcn_cvt_pk_u8_f32",
        "cvt.pknorm.i16" => "__builtin_amdgcn_cvt_pknorm_i16",
        "cvt.pknorm.u16" => "__builtin_amdgcn_cvt_pknorm_u16",
        "cvt.pkrtz" => "__builtin_amdgcn_cvt_pkrtz",
        "cvt.scale.pk16.bf16.bf6" => "__builtin_amdgcn_cvt_scale_pk16_bf16_bf6",
        "cvt.scale.pk16.bf16.fp6" => "__builtin_amdgcn_cvt_scale_pk16_bf16_fp6",
        "cvt.scale.pk16.f16.bf6" => "__builtin_amdgcn_cvt_scale_pk16_f16_bf6",
        "cvt.scale.pk16.f16.fp6" => "__builtin_amdgcn_cvt_scale_pk16_f16_fp6",
        "cvt.scale.pk16.f32.bf6" => "__builtin_amdgcn_cvt_scale_pk16_f32_bf6",
        "cvt.scale.pk16.f32.fp6" => "__builtin_amdgcn_cvt_scale_pk16_f32_fp6",
        "cvt.scale.pk8.bf16.bf8" => "__builtin_amdgcn_cvt_scale_pk8_bf16_bf8",
        "cvt.scale.pk8.bf16.fp4" => "__builtin_amdgcn_cvt_scale_pk8_bf16_fp4",
        "cvt.scale.pk8.bf16.fp8" => "__builtin_amdgcn_cvt_scale_pk8_bf16_fp8",
        "cvt.scale.pk8.f16.bf8" => "__builtin_amdgcn_cvt_scale_pk8_f16_bf8",
        "cvt.scale.pk8.f16.fp4" => "__builtin_amdgcn_cvt_scale_pk8_f16_fp4",
        "cvt.scale.pk8.f16.fp8" => "__builtin_amdgcn_cvt_scale_pk8_f16_fp8",
        "cvt.scale.pk8.f32.bf8" => "__builtin_amdgcn_cvt_scale_pk8_f32_bf8",
        "cvt.scale.pk8.f32.fp4" => "__builtin_amdgcn_cvt_scale_pk8_f32_fp4",
        "cvt.scale.pk8.f32.fp8" => "__builtin_amdgcn_cvt_scale_pk8_f32_fp8",
        "cvt.scalef32.2xpk16.bf6.f32" => "__builtin_amdgcn_cvt_scalef32_2xpk16_bf6_f32",
        "cvt.scalef32.2xpk16.fp6.f32" => "__builtin_amdgcn_cvt_scalef32_2xpk16_fp6_f32",
        "cvt.scalef32.f16.bf8" => "__builtin_amdgcn_cvt_scalef32_f16_bf8",
        "cvt.scalef32.f16.fp8" => "__builtin_amdgcn_cvt_scalef32_f16_fp8",
        "cvt.scalef32.f32.bf8" => "__builtin_amdgcn_cvt_scalef32_f32_bf8",
        "cvt.scalef32.f32.fp8" => "__builtin_amdgcn_cvt_scalef32_f32_fp8",
        "cvt.scalef32.pk.bf16.bf8" => "__builtin_amdgcn_cvt_scalef32_pk_bf16_bf8",
        "cvt.scalef32.pk.bf16.fp4" => "__builtin_amdgcn_cvt_scalef32_pk_bf16_fp4",
        "cvt.scalef32.pk.bf16.fp8" => "__builtin_amdgcn_cvt_scalef32_pk_bf16_fp8",
        "cvt.scalef32.pk.bf8.bf16" => "__builtin_amdgcn_cvt_scalef32_pk_bf8_bf16",
        "cvt.scalef32.pk.bf8.f16" => "__builtin_amdgcn_cvt_scalef32_pk_bf8_f16",
        "cvt.scalef32.pk.bf8.f32" => "__builtin_amdgcn_cvt_scalef32_pk_bf8_f32",
        "cvt.scalef32.pk.f16.bf8" => "__builtin_amdgcn_cvt_scalef32_pk_f16_bf8",
        "cvt.scalef32.pk.f16.fp4" => "__builtin_amdgcn_cvt_scalef32_pk_f16_fp4",
        "cvt.scalef32.pk.f16.fp8" => "__builtin_amdgcn_cvt_scalef32_pk_f16_fp8",
        "cvt.scalef32.pk.f32.bf8" => "__builtin_amdgcn_cvt_scalef32_pk_f32_bf8",
        "cvt.scalef32.pk.f32.fp4" => "__builtin_amdgcn_cvt_scalef32_pk_f32_fp4",
        "cvt.scalef32.pk.f32.fp8" => "__builtin_amdgcn_cvt_scalef32_pk_f32_fp8",
        "cvt.scalef32.pk.fp4.bf16" => "__builtin_amdgcn_cvt_scalef32_pk_fp4_bf16",
        "cvt.scalef32.pk.fp4.f16" => "__builtin_amdgcn_cvt_scalef32_pk_fp4_f16",
        "cvt.scalef32.pk.fp4.f32" => "__builtin_amdgcn_cvt_scalef32_pk_fp4_f32",
        "cvt.scalef32.pk.fp8.bf16" => "__builtin_amdgcn_cvt_scalef32_pk_fp8_bf16",
        "cvt.scalef32.pk.fp8.f16" => "__builtin_amdgcn_cvt_scalef32_pk_fp8_f16",
        "cvt.scalef32.pk.fp8.f32" => "__builtin_amdgcn_cvt_scalef32_pk_fp8_f32",
        "cvt.scalef32.pk16.bf6.bf16" => "__builtin_amdgcn_cvt_scalef32_pk16_bf6_bf16",
        "cvt.scalef32.pk16.bf6.f16" => "__builtin_amdgcn_cvt_scalef32_pk16_bf6_f16",
        "cvt.scalef32.pk16.bf6.f32" => "__builtin_amdgcn_cvt_scalef32_pk16_bf6_f32",
        "cvt.scalef32.pk16.fp6.bf16" => "__builtin_amdgcn_cvt_scalef32_pk16_fp6_bf16",
        "cvt.scalef32.pk16.fp6.f16" => "__builtin_amdgcn_cvt_scalef32_pk16_fp6_f16",
        "cvt.scalef32.pk16.fp6.f32" => "__builtin_amdgcn_cvt_scalef32_pk16_fp6_f32",
        "cvt.scalef32.pk32.bf16.bf6" => "__builtin_amdgcn_cvt_scalef32_pk32_bf16_bf6",
        "cvt.scalef32.pk32.bf16.fp6" => "__builtin_amdgcn_cvt_scalef32_pk32_bf16_fp6",
        "cvt.scalef32.pk32.bf6.bf16" => "__builtin_amdgcn_cvt_scalef32_pk32_bf6_bf16",
        "cvt.scalef32.pk32.bf6.f16" => "__builtin_amdgcn_cvt_scalef32_pk32_bf6_f16",
        "cvt.scalef32.pk32.f16.bf6" => "__builtin_amdgcn_cvt_scalef32_pk32_f16_bf6",
        "cvt.scalef32.pk32.f16.fp6" => "__builtin_amdgcn_cvt_scalef32_pk32_f16_fp6",
        "cvt.scalef32.pk32.f32.bf6" => "__builtin_amdgcn_cvt_scalef32_pk32_f32_bf6",
        "cvt.scalef32.pk32.f32.fp6" => "__builtin_amdgcn_cvt_scalef32_pk32_f32_fp6",
        "cvt.scalef32.pk32.fp6.bf16" => "__builtin_amdgcn_cvt_scalef32_pk32_fp6_bf16",
        "cvt.scalef32.pk32.fp6.f16" => "__builtin_amdgcn_cvt_scalef32_pk32_fp6_f16",
        "cvt.scalef32.pk8.bf8.bf16" => "__builtin_amdgcn_cvt_scalef32_pk8_bf8_bf16",
        "cvt.scalef32.pk8.bf8.f16" => "__builtin_amdgcn_cvt_scalef32_pk8_bf8_f16",
        "cvt.scalef32.pk8.bf8.f32" => "__builtin_amdgcn_cvt_scalef32_pk8_bf8_f32",
        "cvt.scalef32.pk8.fp4.bf16" => "__builtin_amdgcn_cvt_scalef32_pk8_fp4_bf16",
        "cvt.scalef32.pk8.fp4.f16" => "__builtin_amdgcn_cvt_scalef32_pk8_fp4_f16",
        "cvt.scalef32.pk8.fp4.f32" => "__builtin_amdgcn_cvt_scalef32_pk8_fp4_f32",
        "cvt.scalef32.pk8.fp8.bf16" => "__builtin_amdgcn_cvt_scalef32_pk8_fp8_bf16",
        "cvt.scalef32.pk8.fp8.f16" => "__builtin_amdgcn_cvt_scalef32_pk8_fp8_f16",
        "cvt.scalef32.pk8.fp8.f32" => "__builtin_amdgcn_cvt_scalef32_pk8_fp8_f32",
        "cvt.scalef32.sr.bf8.bf16" => "__builtin_amdgcn_cvt_scalef32_sr_bf8_bf16",
        "cvt.scalef32.sr.bf8.f16" => "__builtin_amdgcn_cvt_scalef32_sr_bf8_f16",
        "cvt.scalef32.sr.bf8.f32" => "__builtin_amdgcn_cvt_scalef32_sr_bf8_f32",
        "cvt.scalef32.sr.fp8.bf16" => "__builtin_amdgcn_cvt_scalef32_sr_fp8_bf16",
        "cvt.scalef32.sr.fp8.f16" => "__builtin_amdgcn_cvt_scalef32_sr_fp8_f16",
        "cvt.scalef32.sr.fp8.f32" => "__builtin_amdgcn_cvt_scalef32_sr_fp8_f32",
        "cvt.scalef32.sr.pk.fp4.bf16" => "__builtin_amdgcn_cvt_scalef32_sr_pk_fp4_bf16",
        "cvt.scalef32.sr.pk.fp4.f16" => "__builtin_amdgcn_cvt_scalef32_sr_pk_fp4_f16",
        "cvt.scalef32.sr.pk.fp4.f32" => "__builtin_amdgcn_cvt_scalef32_sr_pk_fp4_f32",
        "cvt.scalef32.sr.pk16.bf6.bf16" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk16_bf6_bf16"
        }
        "cvt.scalef32.sr.pk16.bf6.f16" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk16_bf6_f16"
        }
        "cvt.scalef32.sr.pk16.bf6.f32" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk16_bf6_f32"
        }
        "cvt.scalef32.sr.pk16.fp6.bf16" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk16_fp6_bf16"
        }
        "cvt.scalef32.sr.pk16.fp6.f16" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk16_fp6_f16"
        }
        "cvt.scalef32.sr.pk16.fp6.f32" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk16_fp6_f32"
        }
        "cvt.scalef32.sr.pk32.bf6.bf16" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk32_bf6_bf16"
        }
        "cvt.scalef32.sr.pk32.bf6.f16" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk32_bf6_f16"
        }
        "cvt.scalef32.sr.pk32.bf6.f32" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk32_bf6_f32"
        }
        "cvt.scalef32.sr.pk32.fp6.bf16" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk32_fp6_bf16"
        }
        "cvt.scalef32.sr.pk32.fp6.f16" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk32_fp6_f16"
        }
        "cvt.scalef32.sr.pk32.fp6.f32" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk32_fp6_f32"
        }
        "cvt.scalef32.sr.pk8.bf8.bf16" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk8_bf8_bf16"
        }
        "cvt.scalef32.sr.pk8.bf8.f16" => "__builtin_amdgcn_cvt_scalef32_sr_pk8_bf8_f16",
        "cvt.scalef32.sr.pk8.bf8.f32" => "__builtin_amdgcn_cvt_scalef32_sr_pk8_bf8_f32",
        "cvt.scalef32.sr.pk8.fp4.bf16" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk8_fp4_bf16"
        }
        "cvt.scalef32.sr.pk8.fp4.f16" => "__builtin_amdgcn_cvt_scalef32_sr_pk8_fp4_f16",
        "cvt.scalef32.sr.pk8.fp4.f32" => "__builtin_amdgcn_cvt_scalef32_sr_pk8_fp4_f32",
        "cvt.scalef32.sr.pk8.fp8.bf16" => {
            "__builtin_amdgcn_cvt_scalef32_sr_pk8_fp8_bf16"
        }
        "cvt.scalef32.sr.pk8.fp8.f16" => "__builtin_amdgcn_cvt_scalef32_sr_pk8_fp8_f16",
        "cvt.scalef32.sr.pk8.fp8.f32" => "__builtin_amdgcn_cvt_scalef32_sr_pk8_fp8_f32",
        "cvt.sr.bf16.f32" => "__builtin_amdgcn_cvt_sr_bf16_f32",
        "cvt.sr.bf8.f16" => "__builtin_amdgcn_cvt_sr_bf8_f16",
        "cvt.sr.bf8.f32" => "__builtin_amdgcn_cvt_sr_bf8_f32",
        "cvt.sr.f16.f32" => "__builtin_amdgcn_cvt_sr_f16_f32",
        "cvt.sr.fp8.f16" => "__builtin_amdgcn_cvt_sr_fp8_f16",
        "cvt.sr.fp8.f32" => "__builtin_amdgcn_cvt_sr_fp8_f32",
        "cvt.sr.fp8.f32.e5m3" => "__builtin_amdgcn_cvt_sr_fp8_f32_e5m3",
        "cvt.sr.pk.bf16.f32" => "__builtin_amdgcn_cvt_sr_pk_bf16_f32",
        "cvt.sr.pk.f16.f32" => "__builtin_amdgcn_cvt_sr_pk_f16_f32",
        "dispatch.id" => "__builtin_amdgcn_dispatch_id",
        "dot4.f32.bf8.bf8" => "__builtin_amdgcn_dot4_f32_bf8_bf8",
        "dot4.f32.bf8.fp8" => "__builtin_amdgcn_dot4_f32_bf8_fp8",
        "dot4.f32.fp8.bf8" => "__builtin_amdgcn_dot4_f32_fp8_bf8",
        "dot4.f32.fp8.fp8" => "__builtin_amdgcn_dot4_f32_fp8_fp8",
        "ds.add.gs.reg.rtn" => "__builtin_amdgcn_ds_add_gs_reg_rtn",
        "ds.atomic.async.barrier.arrive.b64" => {
            "__builtin_amdgcn_ds_atomic_async_barrier_arrive_b64"
        }
        "ds.atomic.barrier.arrive.rtn.b64" => {
            "__builtin_amdgcn_ds_atomic_barrier_arrive_rtn_b64"
        }
        "ds.bpermute" => "__builtin_amdgcn_ds_bpermute",
        "ds.bpermute.fi.b32" => "__builtin_amdgcn_ds_bpermute_fi_b32",
        "ds.gws.barrier" => "__builtin_amdgcn_ds_gws_barrier",
        "ds.gws.init" => "__builtin_amdgcn_ds_gws_init",
        "ds.gws.sema.br" => "__builtin_amdgcn_ds_gws_sema_br",
        "ds.gws.sema.p" => "__builtin_amdgcn_ds_gws_sema_p",
        "ds.gws.sema.release.all" => "__builtin_amdgcn_ds_gws_sema_release_all",
        "ds.gws.sema.v" => "__builtin_amdgcn_ds_gws_sema_v",
        "ds.permute" => "__builtin_amdgcn_ds_permute",
        "ds.sub.gs.reg.rtn" => "__builtin_amdgcn_ds_sub_gs_reg_rtn",
        "ds.swizzle" => "__builtin_amdgcn_ds_swizzle",
        "endpgm" => "__builtin_amdgcn_endpgm",
        "fdot2" => "__builtin_amdgcn_fdot2",
        "fdot2.bf16.bf16" => "__builtin_amdgcn_fdot2_bf16_bf16",
        "fdot2.f16.f16" => "__builtin_amdgcn_fdot2_f16_f16",
        "fdot2.f32.bf16" => "__builtin_amdgcn_fdot2_f32_bf16",
        "fdot2c.f32.bf16" => "__builtin_amdgcn_fdot2c_f32_bf16",
        "flat.prefetch" => "__builtin_amdgcn_flat_prefetch",
        "fmul.legacy" => "__builtin_amdgcn_fmul_legacy",
        "global.load.async.to.lds.b128" => {
            "__builtin_amdgcn_global_load_async_to_lds_b128"
        }
        "global.load.async.to.lds.b32" => {
            "__builtin_amdgcn_global_load_async_to_lds_b32"
        }
        "global.load.async.to.lds.b64" => {
            "__builtin_amdgcn_global_load_async_to_lds_b64"
        }
        "global.load.async.to.lds.b8" => "__builtin_amdgcn_global_load_async_to_lds_b8",
        "global.load.lds" => "__builtin_amdgcn_global_load_lds",
        "global.prefetch" => "__builtin_amdgcn_global_prefetch",
        "global.store.async.from.lds.b128" => {
            "__builtin_amdgcn_global_store_async_from_lds_b128"
        }
        "global.store.async.from.lds.b32" => {
            "__builtin_amdgcn_global_store_async_from_lds_b32"
        }
        "global.store.async.from.lds.b64" => {
            "__builtin_amdgcn_global_store_async_from_lds_b64"
        }
        "global.store.async.from.lds.b8" => {
            "__builtin_amdgcn_global_store_async_from_lds_b8"
        }
        "groupstaticsize" => "__builtin_amdgcn_groupstaticsize",
        "iglp.opt" => "__builtin_amdgcn_iglp_opt",
        "implicit.buffer.ptr" => "__builtin_amdgcn_implicit_buffer_ptr",
        "implicitarg.ptr" => "__builtin_amdgcn_implicitarg_ptr",
        "interp.mov" => "__builtin_amdgcn_interp_mov",
        "interp.p1" => "__builtin_amdgcn_interp_p1",
        "interp.p1.f16" => "__builtin_amdgcn_interp_p1_f16",
        "interp.p2" => "__builtin_amdgcn_interp_p2",
        "interp.p2.f16" => "__builtin_amdgcn_interp_p2_f16",
        "is.private" => "__builtin_amdgcn_is_private",
        "is.shared" => "__builtin_amdgcn_is_shared",
        "kernarg.segment.ptr" => "__builtin_amdgcn_kernarg_segment_ptr",
        "lerp" => "__builtin_amdgcn_lerp",
        "mbcnt.hi" => "__builtin_amdgcn_mbcnt_hi",
        "mbcnt.lo" => "__builtin_amdgcn_mbcnt_lo",
        "mfma.f32.16x16x16bf16.1k" => "__builtin_amdgcn_mfma_f32_16x16x16bf16_1k",
        "mfma.f32.16x16x16f16" => "__builtin_amdgcn_mfma_f32_16x16x16f16",
        "mfma.f32.16x16x1f32" => "__builtin_amdgcn_mfma_f32_16x16x1f32",
        "mfma.f32.16x16x2bf16" => "__builtin_amdgcn_mfma_f32_16x16x2bf16",
        "mfma.f32.16x16x32.bf16" => "__builtin_amdgcn_mfma_f32_16x16x32_bf16",
        "mfma.f32.16x16x32.bf8.bf8" => "__builtin_amdgcn_mfma_f32_16x16x32_bf8_bf8",
        "mfma.f32.16x16x32.bf8.fp8" => "__builtin_amdgcn_mfma_f32_16x16x32_bf8_fp8",
        "mfma.f32.16x16x32.f16" => "__builtin_amdgcn_mfma_f32_16x16x32_f16",
        "mfma.f32.16x16x32.fp8.bf8" => "__builtin_amdgcn_mfma_f32_16x16x32_fp8_bf8",
        "mfma.f32.16x16x32.fp8.fp8" => "__builtin_amdgcn_mfma_f32_16x16x32_fp8_fp8",
        "mfma.f32.16x16x4bf16.1k" => "__builtin_amdgcn_mfma_f32_16x16x4bf16_1k",
        "mfma.f32.16x16x4f16" => "__builtin_amdgcn_mfma_f32_16x16x4f16",
        "mfma.f32.16x16x4f32" => "__builtin_amdgcn_mfma_f32_16x16x4f32",
        "mfma.f32.16x16x8.xf32" => "__builtin_amdgcn_mfma_f32_16x16x8_xf32",
        "mfma.f32.16x16x8bf16" => "__builtin_amdgcn_mfma_f32_16x16x8bf16",
        "mfma.f32.32x32x16.bf16" => "__builtin_amdgcn_mfma_f32_32x32x16_bf16",
        "mfma.f32.32x32x16.bf8.bf8" => "__builtin_amdgcn_mfma_f32_32x32x16_bf8_bf8",
        "mfma.f32.32x32x16.bf8.fp8" => "__builtin_amdgcn_mfma_f32_32x32x16_bf8_fp8",
        "mfma.f32.32x32x16.f16" => "__builtin_amdgcn_mfma_f32_32x32x16_f16",
        "mfma.f32.32x32x16.fp8.bf8" => "__builtin_amdgcn_mfma_f32_32x32x16_fp8_bf8",
        "mfma.f32.32x32x16.fp8.fp8" => "__builtin_amdgcn_mfma_f32_32x32x16_fp8_fp8",
        "mfma.f32.32x32x1f32" => "__builtin_amdgcn_mfma_f32_32x32x1f32",
        "mfma.f32.32x32x2bf16" => "__builtin_amdgcn_mfma_f32_32x32x2bf16",
        "mfma.f32.32x32x2f32" => "__builtin_amdgcn_mfma_f32_32x32x2f32",
        "mfma.f32.32x32x4.xf32" => "__builtin_amdgcn_mfma_f32_32x32x4_xf32",
        "mfma.f32.32x32x4bf16" => "__builtin_amdgcn_mfma_f32_32x32x4bf16",
        "mfma.f32.32x32x4bf16.1k" => "__builtin_amdgcn_mfma_f32_32x32x4bf16_1k",
        "mfma.f32.32x32x4f16" => "__builtin_amdgcn_mfma_f32_32x32x4f16",
        "mfma.f32.32x32x8bf16.1k" => "__builtin_amdgcn_mfma_f32_32x32x8bf16_1k",
        "mfma.f32.32x32x8f16" => "__builtin_amdgcn_mfma_f32_32x32x8f16",
        "mfma.f32.4x4x1f32" => "__builtin_amdgcn_mfma_f32_4x4x1f32",
        "mfma.f32.4x4x2bf16" => "__builtin_amdgcn_mfma_f32_4x4x2bf16",
        "mfma.f32.4x4x4bf16.1k" => "__builtin_amdgcn_mfma_f32_4x4x4bf16_1k",
        "mfma.f32.4x4x4f16" => "__builtin_amdgcn_mfma_f32_4x4x4f16",
        "mfma.f64.16x16x4f64" => "__builtin_amdgcn_mfma_f64_16x16x4f64",
        "mfma.f64.4x4x4f64" => "__builtin_amdgcn_mfma_f64_4x4x4f64",
        "mfma.i32.16x16x16i8" => "__builtin_amdgcn_mfma_i32_16x16x16i8",
        "mfma.i32.16x16x32.i8" => "__builtin_amdgcn_mfma_i32_16x16x32_i8",
        "mfma.i32.16x16x4i8" => "__builtin_amdgcn_mfma_i32_16x16x4i8",
        "mfma.i32.16x16x64.i8" => "__builtin_amdgcn_mfma_i32_16x16x64_i8",
        "mfma.i32.32x32x16.i8" => "__builtin_amdgcn_mfma_i32_32x32x16_i8",
        "mfma.i32.32x32x32.i8" => "__builtin_amdgcn_mfma_i32_32x32x32_i8",
        "mfma.i32.32x32x4i8" => "__builtin_amdgcn_mfma_i32_32x32x4i8",
        "mfma.i32.32x32x8i8" => "__builtin_amdgcn_mfma_i32_32x32x8i8",
        "mfma.i32.4x4x4i8" => "__builtin_amdgcn_mfma_i32_4x4x4i8",
        "mqsad.pk.u16.u8" => "__builtin_amdgcn_mqsad_pk_u16_u8",
        "mqsad.u32.u8" => "__builtin_amdgcn_mqsad_u32_u8",
        "msad.u8" => "__builtin_amdgcn_msad_u8",
        "perm" => "__builtin_amdgcn_perm",
        "perm.pk16.b4.u4" => "__builtin_amdgcn_perm_pk16_b4_u4",
        "perm.pk16.b6.u4" => "__builtin_amdgcn_perm_pk16_b6_u4",
        "perm.pk16.b8.u4" => "__builtin_amdgcn_perm_pk16_b8_u4",
        "permlane.bcast" => "__builtin_amdgcn_permlane_bcast",
        "permlane.down" => "__builtin_amdgcn_permlane_down",
        "permlane.idx.gen" => "__builtin_amdgcn_permlane_idx_gen",
        "permlane.up" => "__builtin_amdgcn_permlane_up",
        "permlane.xor" => "__builtin_amdgcn_permlane_xor",
        "permlane16.var" => "__builtin_amdgcn_permlane16_var",
        "permlanex16.var" => "__builtin_amdgcn_permlanex16_var",
        "pk.add.max.i16" => "__builtin_amdgcn_pk_add_max_i16",
        "pk.add.max.u16" => "__builtin_amdgcn_pk_add_max_u16",
        "pk.add.min.i16" => "__builtin_amdgcn_pk_add_min_i16",
        "pk.add.min.u16" => "__builtin_amdgcn_pk_add_min_u16",
        "prng.b32" => "__builtin_amdgcn_prng_b32",
        "qsad.pk.u16.u8" => "__builtin_amdgcn_qsad_pk_u16_u8",
        "queue.ptr" => "__builtin_amdgcn_queue_ptr",
        "raw.ptr.buffer.load.lds" => "__builtin_amdgcn_raw_ptr_buffer_load_lds",
        "rcp.legacy" => "__builtin_amdgcn_rcp_legacy",
        "rsq.legacy" => "__builtin_amdgcn_rsq_legacy",
        "s.barrier" => "__builtin_amdgcn_s_barrier",
        "s.barrier.init" => "__builtin_amdgcn_s_barrier_init",
        "s.barrier.join" => "__builtin_amdgcn_s_barrier_join",
        "s.barrier.leave" => "__builtin_amdgcn_s_barrier_leave",
        "s.barrier.signal" => "__builtin_amdgcn_s_barrier_signal",
        "s.barrier.signal.isfirst" => "__builtin_amdgcn_s_barrier_signal_isfirst",
        "s.barrier.signal.var" => "__builtin_amdgcn_s_barrier_signal_var",
        "s.barrier.wait" => "__builtin_amdgcn_s_barrier_wait",
        "s.buffer.prefetch.data" => "__builtin_amdgcn_s_buffer_prefetch_data",
        "s.cluster.barrier" => "__builtin_amdgcn_s_cluster_barrier",
        "s.dcache.inv" => "__builtin_amdgcn_s_dcache_inv",
        "s.dcache.inv.vol" => "__builtin_amdgcn_s_dcache_inv_vol",
        "s.dcache.wb" => "__builtin_amdgcn_s_dcache_wb",
        "s.dcache.wb.vol" => "__builtin_amdgcn_s_dcache_wb_vol",
        "s.decperflevel" => "__builtin_amdgcn_s_decperflevel",
        "s.get.barrier.state" => "__builtin_amdgcn_s_get_barrier_state",
        "s.get.named.barrier.state" => "__builtin_amdgcn_s_get_named_barrier_state",
        "s.get.waveid.in.workgroup" => "__builtin_amdgcn_s_get_waveid_in_workgroup",
        "s.getpc" => "__builtin_amdgcn_s_getpc",
        "s.getreg" => "__builtin_amdgcn_s_getreg",
        "s.incperflevel" => "__builtin_amdgcn_s_incperflevel",
        "s.memrealtime" => "__builtin_amdgcn_s_memrealtime",
        "s.memtime" => "__builtin_amdgcn_s_memtime",
        "s.monitor.sleep" => "__builtin_amdgcn_s_monitor_sleep",
        "s.sendmsg" => "__builtin_amdgcn_s_sendmsg",
        "s.sendmsghalt" => "__builtin_amdgcn_s_sendmsghalt",
        "s.setprio" => "__builtin_amdgcn_s_setprio",
        "s.setprio.inc.wg" => "__builtin_amdgcn_s_setprio_inc_wg",
        "s.setreg" => "__builtin_amdgcn_s_setreg",
        "s.sleep" => "__builtin_amdgcn_s_sleep",
        "s.sleep.var" => "__builtin_amdgcn_s_sleep_var",
        "s.ttracedata" => "__builtin_amdgcn_s_ttracedata",
        "s.ttracedata.imm" => "__builtin_amdgcn_s_ttracedata_imm",
        "s.wait.asynccnt" => "__builtin_amdgcn_s_wait_asynccnt",
        "s.wait.event.export.ready" => "__builtin_amdgcn_s_wait_event_export_ready",
        "s.wait.tensorcnt" => "__builtin_amdgcn_s_wait_tensorcnt",
        "s.waitcnt" => "__builtin_amdgcn_s_waitcnt",
        "s.wakeup.barrier" => "__builtin_amdgcn_s_wakeup_barrier",
        "sad.hi.u8" => "__builtin_amdgcn_sad_hi_u8",
        "sad.u16" => "__builtin_amdgcn_sad_u16",
        "sad.u8" => "__builtin_amdgcn_sad_u8",
        "sat.pk4.i4.i8" => "__builtin_amdgcn_sat_pk4_i4_i8",
        "sat.pk4.u4.u8" => "__builtin_amdgcn_sat_pk4_u4_u8",
        "sched.barrier" => "__builtin_amdgcn_sched_barrier",
        "sched.group.barrier" => "__builtin_amdgcn_sched_group_barrier",
        "sdot2" => "__builtin_amdgcn_sdot2",
        "sdot4" => "__builtin_amdgcn_sdot4",
        "sdot8" => "__builtin_amdgcn_sdot8",
        "smfmac.f32.16x16x128.bf8.bf8" => {
            "__builtin_amdgcn_smfmac_f32_16x16x128_bf8_bf8"
        }
        "smfmac.f32.16x16x128.bf8.fp8" => {
            "__builtin_amdgcn_smfmac_f32_16x16x128_bf8_fp8"
        }
        "smfmac.f32.16x16x128.fp8.bf8" => {
            "__builtin_amdgcn_smfmac_f32_16x16x128_fp8_bf8"
        }
        "smfmac.f32.16x16x128.fp8.fp8" => {
            "__builtin_amdgcn_smfmac_f32_16x16x128_fp8_fp8"
        }
        "smfmac.f32.16x16x32.bf16" => "__builtin_amdgcn_smfmac_f32_16x16x32_bf16",
        "smfmac.f32.16x16x32.f16" => "__builtin_amdgcn_smfmac_f32_16x16x32_f16",
        "smfmac.f32.16x16x64.bf16" => "__builtin_amdgcn_smfmac_f32_16x16x64_bf16",
        "smfmac.f32.16x16x64.bf8.bf8" => "__builtin_amdgcn_smfmac_f32_16x16x64_bf8_bf8",
        "smfmac.f32.16x16x64.bf8.fp8" => "__builtin_amdgcn_smfmac_f32_16x16x64_bf8_fp8",
        "smfmac.f32.16x16x64.f16" => "__builtin_amdgcn_smfmac_f32_16x16x64_f16",
        "smfmac.f32.16x16x64.fp8.bf8" => "__builtin_amdgcn_smfmac_f32_16x16x64_fp8_bf8",
        "smfmac.f32.16x16x64.fp8.fp8" => "__builtin_amdgcn_smfmac_f32_16x16x64_fp8_fp8",
        "smfmac.f32.32x32x16.bf16" => "__builtin_amdgcn_smfmac_f32_32x32x16_bf16",
        "smfmac.f32.32x32x16.f16" => "__builtin_amdgcn_smfmac_f32_32x32x16_f16",
        "smfmac.f32.32x32x32.bf16" => "__builtin_amdgcn_smfmac_f32_32x32x32_bf16",
        "smfmac.f32.32x32x32.bf8.bf8" => "__builtin_amdgcn_smfmac_f32_32x32x32_bf8_bf8",
        "smfmac.f32.32x32x32.bf8.fp8" => "__builtin_amdgcn_smfmac_f32_32x32x32_bf8_fp8",
        "smfmac.f32.32x32x32.f16" => "__builtin_amdgcn_smfmac_f32_32x32x32_f16",
        "smfmac.f32.32x32x32.fp8.bf8" => "__builtin_amdgcn_smfmac_f32_32x32x32_fp8_bf8",
        "smfmac.f32.32x32x32.fp8.fp8" => "__builtin_amdgcn_smfmac_f32_32x32x32_fp8_fp8",
        "smfmac.f32.32x32x64.bf8.bf8" => "__builtin_amdgcn_smfmac_f32_32x32x64_bf8_bf8",
        "smfmac.f32.32x32x64.bf8.fp8" => "__builtin_amdgcn_smfmac_f32_32x32x64_bf8_fp8",
        "smfmac.f32.32x32x64.fp8.bf8" => "__builtin_amdgcn_smfmac_f32_32x32x64_fp8_bf8",
        "smfmac.f32.32x32x64.fp8.fp8" => "__builtin_amdgcn_smfmac_f32_32x32x64_fp8_fp8",
        "smfmac.i32.16x16x128.i8" => "__builtin_amdgcn_smfmac_i32_16x16x128_i8",
        "smfmac.i32.16x16x64.i8" => "__builtin_amdgcn_smfmac_i32_16x16x64_i8",
        "smfmac.i32.32x32x32.i8" => "__builtin_amdgcn_smfmac_i32_32x32x32_i8",
        "smfmac.i32.32x32x64.i8" => "__builtin_amdgcn_smfmac_i32_32x32x64_i8",
        "struct.ptr.buffer.load.lds" => "__builtin_amdgcn_struct_ptr_buffer_load_lds",
        "sudot4" => "__builtin_amdgcn_sudot4",
        "sudot8" => "__builtin_amdgcn_sudot8",
        "tensor.load.to.lds" => "__builtin_amdgcn_tensor_load_to_lds",
        "tensor.load.to.lds.d2" => "__builtin_amdgcn_tensor_load_to_lds_d2",
        "tensor.store.from.lds" => "__builtin_amdgcn_tensor_store_from_lds",
        "tensor.store.from.lds.d2" => "__builtin_amdgcn_tensor_store_from_lds_d2",
        "udot2" => "__builtin_amdgcn_udot2",
        "udot4" => "__builtin_amdgcn_udot4",
        "udot8" => "__builtin_amdgcn_udot8",
        "wave.barrier" => "__builtin_amdgcn_wave_barrier",
        "wavefrontsize" => "__builtin_amdgcn_wavefrontsize",
        "workgroup.id.x" => "__builtin_amdgcn_workgroup_id_x",
        "workgroup.id.y" => "__builtin_amdgcn_workgroup_id_y",
        "workgroup.id.z" => "__builtin_amdgcn_workgroup_id_z",
        "workitem.id.x" => "__builtin_amdgcn_workitem_id_x",
        "workitem.id.y" => "__builtin_amdgcn_workitem_id_y",
        "workitem.id.z" => "__builtin_amdgcn_workitem_id_z",
        _ => unimplemented!("***** unsupported LLVM intrinsic {full_name}"),
    }
}
