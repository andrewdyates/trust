// tRust: split from archs.rs — aarch64 architecture intrinsics
fn aarch64(name: &str, full_name: &str) -> &'static str {
    match name {
        // aarch64
        "chkfeat" => "__builtin_arm_chkfeat",
        "dmb" => "__builtin_arm_dmb",
        "dsb" => "__builtin_arm_dsb",
        "gcspopm" => "__builtin_arm_gcspopm",
        "gcsss" => "__builtin_arm_gcsss",
        "isb" => "__builtin_arm_isb",
        "prefetch" => "__builtin_arm_prefetch",
        "range.prefetch" => "__builtin_arm_range_prefetch",
        "sme.in.streaming.mode" => "__builtin_arm_in_streaming_mode",
        "sve.aesd" => "__builtin_sve_svaesd_u8",
        "sve.aese" => "__builtin_sve_svaese_u8",
        "sve.aesimc" => "__builtin_sve_svaesimc_u8",
        "sve.aesmc" => "__builtin_sve_svaesmc_u8",
        "sve.rax1" => "__builtin_sve_svrax1_u64",
        "sve.rdffr" => "__builtin_sve_svrdffr",
        "sve.rdffr.z" => "__builtin_sve_svrdffr_z",
        "sve.setffr" => "__builtin_sve_svsetffr",
        "sve.sm4e" => "__builtin_sve_svsm4e_u32",
        "sve.sm4ekey" => "__builtin_sve_svsm4ekey_u32",
        "sve.wrffr" => "__builtin_sve_svwrffr",
        _ => unimplemented!("***** unsupported LLVM intrinsic {full_name}"),
    }
}
