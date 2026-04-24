// tRust: split from archs.rs — r600 architecture intrinsics
fn r600(name: &str, full_name: &str) -> &'static str {
    match name {
        // r600
        "group.barrier" => "__builtin_r600_group_barrier",
        "implicitarg.ptr" => "__builtin_r600_implicitarg_ptr",
        "rat.store.typed" => "__builtin_r600_rat_store_typed",
        "read.global.size.x" => "__builtin_r600_read_global_size_x",
        "read.global.size.y" => "__builtin_r600_read_global_size_y",
        "read.global.size.z" => "__builtin_r600_read_global_size_z",
        "read.ngroups.x" => "__builtin_r600_read_ngroups_x",
        "read.ngroups.y" => "__builtin_r600_read_ngroups_y",
        "read.ngroups.z" => "__builtin_r600_read_ngroups_z",
        "read.tgid.x" => "__builtin_r600_read_tgid_x",
        "read.tgid.y" => "__builtin_r600_read_tgid_y",
        "read.tgid.z" => "__builtin_r600_read_tgid_z",
        "read.tidig.x" => "__builtin_r600_read_tidig_x",
        "read.tidig.y" => "__builtin_r600_read_tidig_y",
        "read.tidig.z" => "__builtin_r600_read_tidig_z",
        _ => unimplemented!("***** unsupported LLVM intrinsic {full_name}"),
    }
}
