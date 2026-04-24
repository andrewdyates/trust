# tRust Correctness Ledger

> **Snapshot - decays fast.**
>
> **Inventory refreshed:** 2026-04-23
>
> **Most recent compiler-touching commit on `main`:**
> `eb382dd62183bd41e4a521fcc963a472ec226c2b` (`2026-04-23T08:15:01-07:00`)
>
> **Inventory command:**
> `grep -rn '// tRust:' compiler/ --include="*.rs" | grep -v '/tests/'`

This file is a current inventory of annotated compiler divergence from upstream
`rust-lang/rust`.

It is intentionally narrower than a full validation report: the numbers below
reflect the current in-tree `// tRust:` annotation inventory, not a claim that
the entire compiler test matrix was rerun on the refresh date.

## Summary

| Metric | Value |
|--------|-------|
| Total `// tRust:` annotations in `compiler/` | 258 |
| Files with `// tRust:` annotations | 34 |
| Compiler crates touched | 8 |
| Full-matrix validation status | Not rerun as part of this refresh |

## Per-Crate Counts

| Crate | Annotation lines | Files |
|-------|------------------|-------|
| `rustc_middle` | 99 | 1 |
| `rustc_mir_transform` | 88 | 5 |
| `rustc_codegen_ssa` | 26 | 7 |
| `rustc_codegen_gcc` | 17 | 17 |
| `rustc_trait_selection` | 17 | 1 |
| `rustc_codegen_llvm2` | 9 | 1 |
| `rustc_interface` | 1 | 1 |
| `rustc_monomorphize` | 1 | 1 |

## Annotated Files

- `compiler/rustc_codegen_gcc/src/intrinsic/archs/aarch64.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/amdgcn.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/arm.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/bpf.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/dispatch.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/hexagon.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/loongarch.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/mips.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/nvvm.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/ppc.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/r600.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/riscv.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/s390.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/spv.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/ve.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/x86.rs`
- `compiler/rustc_codegen_gcc/src/intrinsic/archs/xcore.rs`
- `compiler/rustc_codegen_llvm2/src/lib.rs`
- `compiler/rustc_codegen_ssa/src/back/link/apple_link.rs`
- `compiler/rustc_codegen_ssa/src/back/link/archive_ops.rs`
- `compiler/rustc_codegen_ssa/src/back/link/linker_args.rs`
- `compiler/rustc_codegen_ssa/src/back/link/linker_config.rs`
- `compiler/rustc_codegen_ssa/src/back/link/linker_exec.rs`
- `compiler/rustc_codegen_ssa/src/back/link/lld.rs`
- `compiler/rustc_codegen_ssa/src/back/link/native_libs.rs`
- `compiler/rustc_interface/src/util.rs`
- `compiler/rustc_middle/src/mir/trust_proof.rs`
- `compiler/rustc_mir_transform/src/check_target_feature_abi.rs`
- `compiler/rustc_mir_transform/src/lib.rs`
- `compiler/rustc_mir_transform/src/redundant_bounds_check.rs`
- `compiler/rustc_mir_transform/src/trust_proof_query.rs`
- `compiler/rustc_mir_transform/src/trust_verify.rs`
- `compiler/rustc_monomorphize/src/mono_checks/stack_check.rs`
- `compiler/rustc_trait_selection/src/traits/select/mod.rs`

## Regeneration Notes

- Refresh the inventory with the command above whenever annotated compiler
  divergence changes.
- If compiler changes land without corresponding `// tRust:` annotations, this
  ledger is incomplete by definition.
- Full validation claims should live in dedicated build/test reports, not in
  this inventory snapshot.
