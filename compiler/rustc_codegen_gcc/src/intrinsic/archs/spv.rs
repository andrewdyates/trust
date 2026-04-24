// tRust: split from archs.rs — spv architecture intrinsics
fn spv(name: &str, full_name: &str) -> &'static str {
    match name {
        // spv
        "group.memory.barrier.with.group.sync" => "__builtin_spirv_group_barrier",
        "num.subgroups" => "__builtin_spirv_num_subgroups",
        "subgroup.id" => "__builtin_spirv_subgroup_id",
        "subgroup.local.invocation.id" => {
            "__builtin_spirv_subgroup_local_invocation_id"
        }
        "subgroup.max.size" => "__builtin_spirv_subgroup_max_size",
        "subgroup.size" => "__builtin_spirv_subgroup_size",
        "wave.ballot" => "__builtin_spirv_subgroup_ballot",
        _ => unimplemented!("***** unsupported LLVM intrinsic {full_name}"),
    }
}
