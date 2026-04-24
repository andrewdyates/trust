// tRust: split from archs.rs — xcore architecture intrinsics
fn xcore(name: &str, full_name: &str) -> &'static str {
    match name {
        // xcore
        "bitrev" => "__builtin_bitrev",
        "getid" => "__builtin_getid",
        "getps" => "__builtin_getps",
        "setps" => "__builtin_setps",
        _ => unimplemented!("***** unsupported LLVM intrinsic {full_name}"),
    }
}
