# `trust-verify`

The tracking issue for this feature is internal to tRust.

------------------------

Enables tRust's native MIR verification transport in the compiler.

For normal verifier use, start with the public `cargo trust` front door:

```text
cargo trust check
cargo trust check --format json
```

`rustc -Z trust-verify ...` is the lower-level compiler transport used by
`cargo-trust` and by compiler-facing tests. It is useful for compiler work and
transport debugging, not as the primary user-facing verifier command.

```text
rustc -Z trust-verify your_file.rs
```

When enabled on a built tRust compiler that exposes the flag, the compiler runs
the tRust verification pipeline over optimized MIR and emits verification
diagnostics and structured transport output. This is additive today:
verification reports findings but does not block compilation.

Availability of this native/stage1 path is still tracked work in tRust's
current from-source flow, so this flag should not be treated as a universally
shipped guarantee across all builds or environments.

Use `-Z trust-verify-level` to control how deep verification should go.

For most users and automation, prefer `cargo trust check` and
`cargo trust check --format json`.
