# cargo-trust

**Author:** Andrew Yates <andrew@andrewdyates.com>
**Version:** 0.1.0
**License:** MIT OR Apache-2.0

<!--
cite:
- Cargo.toml
- Cargo.lock
- ../Cargo.toml
-->

`cargo trust` is the canonical verifier interface for tRust.

The public commands to optimize around today are:

- `cargo trust check`
- `cargo trust check --format json`

Everything else in this package is secondary to that front door.

## Install From This Checkout

Use the root README quick start for the full build flow. The short version is:

```bash
./x.py build --stage 1
rustup toolchain link trust ./build/host/stage1
cargo install --path cargo-trust --force
```

That explicit `cargo install --path cargo-trust --force` step is still needed because `cargo-trust` is not yet part of the finished default install/dist tool list.

If `cargo trust` cannot find the built compiler automatically, set:

```bash
export TRUST_RUSTC=/abs/path/to/tRust/build/host/stage1/bin/rustc
```

Native compiler discovery order is:

1. `TRUST_RUSTC`
2. sibling `rustc` next to the running `cargo-trust`
3. linked `rustup` toolchain `trust`
4. repo-local `build/.../stage{2,1}` rustc candidates

## Canonical Usage

Current crate:

```bash
cargo trust check
cargo trust check --format json
```

Single file:

```bash
cargo trust check path/to/file.rs
cargo trust check --format json path/to/file.rs
```

From the tRust repo root, the checked example path is:

```bash
cargo trust check examples/midpoint.rs
cargo trust check --format json examples/midpoint.rs
```

## Current Contract

- `cargo trust check` is the canonical human-readable report surface.
- `cargo trust check --format json` is the canonical machine-readable report surface.
- Default configuration is `L1`, so a first run produces real obligations instead of an empty report.
- Exit code `0` means the compiler succeeded and every obligation was proved.
- Exit code `1` means at least one obligation failed, was runtime-checked, was inconclusive, or the compiler itself failed.
- Exit code `2` means `cargo-trust` hit an internal setup or argument error.
- `cargo trust check` and `cargo trust report` prefer native verification when a discoverable tRust compiler supports `-Z trust-verify`.
- `--standalone` forces source analysis. `check` and `report` also fall back to standalone automatically when no native compiler is discoverable, or when the discovered compiler lacks `-Z trust-verify`.
- If the discovered compiler supports `-Z trust-verify` but not `-Z trust-verify-output=json`, `cargo-trust` still runs native verification and parses human-readable diagnostics.
- `build` and rewrite-loop flows do not use standalone fallback; they require a discoverable native tRust compiler.
- LLVM remains the default backend; LLVM2 is experimental and opt-in.

## LLVM2

LLVM2 is not the normal path. It is an experimental alternate backend tracked under `#829`.

- default: LLVM
- opt-in CLI: `cargo trust check --backend llvm2`
- opt-in config: `codegen_backend = "llvm2"` in `trust.toml`

## trust.toml

`cargo-trust` currently accepts only these `trust.toml` keys: `enabled`, `level`, `timeout_ms`, `skip_functions`, `verify_functions`, and `codegen_backend`.

Unsupported keys make the file invalid and `cargo-trust` falls back to defaults. `--backend` overrides `codegen_backend`.

## Developer Transport

These are useful while working on the repo, but they are not the public front door:

- `cargo run --manifest-path cargo-trust/Cargo.toml -- trust ...`
- raw compiler transport via `rustc -Z trust-verify ...`
- direct stage toolchain paths under `build/.../stage1/bin/*`

Packaged-release work for `cargo-trust` should build on the existing `x install` / `x dist` pipeline, but that productization path is not finished yet.
