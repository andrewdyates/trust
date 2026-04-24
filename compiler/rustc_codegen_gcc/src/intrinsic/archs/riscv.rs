// tRust: split from archs.rs — riscv architecture intrinsics
fn riscv(name: &str, full_name: &str) -> &'static str {
    match name {
        // riscv
        "aes32dsi" => "__builtin_riscv_aes32dsi",
        "aes32dsmi" => "__builtin_riscv_aes32dsmi",
        "aes32esi" => "__builtin_riscv_aes32esi",
        "aes32esmi" => "__builtin_riscv_aes32esmi",
        "aes64ds" => "__builtin_riscv_aes64ds",
        "aes64dsm" => "__builtin_riscv_aes64dsm",
        "aes64es" => "__builtin_riscv_aes64es",
        "aes64esm" => "__builtin_riscv_aes64esm",
        "aes64im" => "__builtin_riscv_aes64im",
        "aes64ks1i" => "__builtin_riscv_aes64ks1i",
        "aes64ks2" => "__builtin_riscv_aes64ks2",
        "mips.ehb" => "__builtin_riscv_mips_ehb",
        "mips.ihb" => "__builtin_riscv_mips_ihb",
        "mips.pause" => "__builtin_riscv_mips_pause",
        "sha512sig0" => "__builtin_riscv_sha512sig0",
        "sha512sig0h" => "__builtin_riscv_sha512sig0h",
        "sha512sig0l" => "__builtin_riscv_sha512sig0l",
        "sha512sig1" => "__builtin_riscv_sha512sig1",
        "sha512sig1h" => "__builtin_riscv_sha512sig1h",
        "sha512sig1l" => "__builtin_riscv_sha512sig1l",
        "sha512sum0" => "__builtin_riscv_sha512sum0",
        "sha512sum0r" => "__builtin_riscv_sha512sum0r",
        "sha512sum1" => "__builtin_riscv_sha512sum1",
        "sha512sum1r" => "__builtin_riscv_sha512sum1r",
        _ => unimplemented!("***** unsupported LLVM intrinsic {full_name}"),
    }
}
