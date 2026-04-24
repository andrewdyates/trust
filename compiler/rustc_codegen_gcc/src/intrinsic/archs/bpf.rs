// tRust: split from archs.rs — bpf architecture intrinsics
fn bpf(name: &str, full_name: &str) -> &'static str {
    match name {
        // bpf
        "btf.type.id" => "__builtin_bpf_btf_type_id",
        "compare" => "__builtin_bpf_compare",
        "getelementptr.and.load" => "__builtin_bpf_getelementptr_and_load",
        "getelementptr.and.store" => "__builtin_bpf_getelementptr_and_store",
        "load.byte" => "__builtin_bpf_load_byte",
        "load.half" => "__builtin_bpf_load_half",
        "load.word" => "__builtin_bpf_load_word",
        "passthrough" => "__builtin_bpf_passthrough",
        "preserve.enum.value" => "__builtin_bpf_preserve_enum_value",
        "preserve.field.info" => "__builtin_bpf_preserve_field_info",
        "preserve.type.info" => "__builtin_bpf_preserve_type_info",
        "pseudo" => "__builtin_bpf_pseudo",
        _ => unimplemented!("***** unsupported LLVM intrinsic {full_name}"),
    }
}
