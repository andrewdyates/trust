# tRust

> **Preview release (April 2026).** tRust is a practical local `trust` toolchain plus the canonical `cargo trust` verifier. As of 2026-04-24, the developer baseline is still the from-source linked `trust` rustup alias, while the replacement release bar is the installed/default-profile `trust` toolchain plus the no-flags `installed-default` proof gate. The public verifier surface is `cargo trust check` and `cargo trust check --format json`. Native verification currently requires a discoverable `trustc` compiler with `-Z trust-verify`; otherwise `cargo-trust` falls back to standalone source analysis for `check` and `report`. LLVM remains the default backend. LLVM2 is experimental and opt-in.

**Author:** Andrew Yates <andrew@andrewdyates.com>
**Version:** 0.1.0
**License:** MIT OR Apache-2.0
**Copyright:** The Rust Project Contributors and tRust contributors; see [COPYRIGHT](COPYRIGHT).

<!--
cite:
- Cargo.toml
- Cargo.lock
- COPYRIGHT
- cargo-trust/Cargo.toml
-->

tRust inherits the upstream compiler codebase and adds native verification without giving up a usable local toolchain. The shipped public surface today is:

- a locally built `trust` toolchain that you link into `rustup` as `trust`
- a canonical compiler binary: `trustc`
- a human-facing verifier command: `cargo trust check`
- a machine-facing verifier command: `cargo trust check --format json`

Packaged releases and update flows are active productization work built on existing `x install` and `x dist`. A public "switch 100%" claim requires fresh green logs for the replacement gates.

Today’s daily-driver contract is narrower than a finished packaged release:

- link a local tRust sysroot into `rustup` as `trust`
- use `cargo +trust ...` for ordinary `trust` toolchain work, or `rustup run trust cargo ...` if you want explicit rustup dispatch
- install `cargo-trust` from this checkout if you want the plain `cargo trust ...` verifier command

## Quick Start

```bash
git clone https://github.com/andrewdyates/tRust tRust
cd tRust

rustup toolchain install nightly
rustup component add rustc-dev --toolchain nightly

./x.py build --stage 1
rustup toolchain link trust ./build/host/stage1

cargo install --path cargo-trust --force

tests/e2e_trust_toolchain.sh
cargo +trust check --manifest-path cargo-trust/Cargo.toml
cargo trust check examples/midpoint.rs
cargo trust check --format json examples/midpoint.rs
```

If your build emitted a target-specific sysroot instead of `./build/host/stage1`, link that path instead. The linked `trust` alias is the supported install story and the simplest compiler-discovery path for `cargo-trust`. Native compiler discovery should prefer `TRUSTC`, sibling `trustc` next to `cargo-trust`, the linked `trust` toolchain, then repo-local `build/.../stage{2,1}`. Legacy compatibility `rustc` paths may still exist during the transition, but the tRust-owned product name is `trustc`.

## Glossary

| Name | Meaning |
|------|---------|
| `tRust` | The product and repository: a trust-first compiler fork plus verification tooling |
| `trust` | The local `rustup` toolchain alias you link to a built tRust sysroot |
| `trustc` | The canonical tRust compiler binary |
| legacy compatibility `rustc` | Alias/shim kept only where inherited tooling still requires that executable name |
| `cargo trust` | The public verifier command users run |
| `cargo-trust` | The package/binary that implements the `cargo trust` subcommand |
| `-Z trust-verify` | Low-level compiler transport used by `cargo-trust` and tests |
| `LLVM2` | Experimental alternate codegen backend; not the default path |

## What Works Today

- `./x.py build --stage 1` produces a local stage1 tRust toolchain that can be linked into `rustup` as `trust`
- The linked `trust` toolchain works as a practical local `trust` toolchain for `cargo +trust check/build/test/doc/fmt/clippy/miri`; see `tests/e2e_trust_toolchain.sh`
- `cargo trust check` produces the canonical human-readable verification report
- `cargo trust check --format json` produces the canonical machine-readable verification report
- `cargo-trust` uses a discoverable `trustc` compiler when one supports `-Z trust-verify`; for `check` and `report`, it falls back to standalone source analysis when that compiler is missing or lacks the flag
- `cargo-trust` uses LLVM by default and can opt into LLVM2 with `--backend llvm2` or `codegen_backend = "llvm2"` in `trust.toml`

## Packaging Status

- The current public install story is the linked/local flow shown in the quick start.
- The checked daily-driver contract is the linked `trust` alias plus `cargo +trust ...` or `rustup run trust cargo ...`, with `cargo-trust` installed separately from this checkout when you want `cargo trust ...`.
- Release-readiness evidence is tracked as separate gates: linked/local launch approximation, pre-publish dist rehearsal, installed-toolchain acceptance, installed default/no-flags acceptance, and stage0 lineage/self-host proof.
- Future packaged releases should build on the existing bootstrap packaging commands `./x install` and `./x dist`, not on a separate new installer.
- The default-profile replacement checklist requires the canonical `trustc` compiler, `cargo`, `cargo-trust`, formatter/linter/analyzer/source/docs/std/LLVM components under `trust` ownership, and any legacy compatibility shims still needed by inherited tooling.
- Until the replacement gates are freshly green for a release commit, treat the linked/local flow as the public baseline and the installed/default flow as release-candidate evidence.
- A future "no inherited upstream bootstrap" claim also requires `src/stage0` to target a tRust-owned local dist root or owned dist server/channel seeded by a previous tRust release.

## Canonical Interfaces

### Local `trust` toolchain

```bash
cargo +trust check --manifest-path cargo-trust/Cargo.toml
(cd examples/contracts/basic-contracts && cargo +trust test)
```

### Human-facing verification

```bash
cargo trust check
cargo trust check path/to/file.rs
```

### Machine-facing verification

```bash
cargo trust check --format json
cargo trust check --format json path/to/file.rs
```

LLVM is the default backend for all of the above. LLVM2 remains explicitly opt-in and experimental.

`cargo trust report` exists, but the public verifier surface to optimize docs, scripts, and automation around is still `cargo trust check` and `cargo trust check --format json`.

## Developer Transport

These are real interfaces, but they are not the blessed public front door:

- raw compiler transport: `trustc -Z trust-verify ...`
- running the subcommand from source without installing it: `cargo run --manifest-path cargo-trust/Cargo.toml -- trust ...`
- direct stage paths under `build/.../stage1/bin/*`

Use them for compiler work, transport debugging, or repo-local development. For regular users and automation, prefer `cargo trust check` and `cargo trust check --format json`.

## License

This repository is distributed under **MIT OR Apache-2.0**.

Why: `tRust` is a fork of `rust-lang/rust`, and the upstream `rustc`
compiler source and standard library are dual-licensed under MIT and
Apache-2.0 unless otherwise specified. `tRust`-owned top-level package
metadata in this repo follows that same dual-license model so the
repository-level license statement matches the distributed contents.

See [LICENSE-APACHE](LICENSE-APACHE), [LICENSE-MIT](LICENSE-MIT), and
individual crate `Cargo.toml` files for package-level metadata.

## Current Trackers

- `#1001`: overall toolchain replacement, install/docs coherence, and release-readiness program
- `#1011`: fresh-machine install/default-toolchain launch gate for “switch 100% now”
- `#1009`: bootstrap/dist/install work to ship `cargo-trust` with the toolchain
- `#995`: user-facing tool completeness in the stage1/shipped sysroot
- `#996`: native verification on the shipped `trust` toolchain
- `#1008`: public proof corpus and crate-first verification workflow
- `#998`: long-form/docs rebaseline to current shipped reality
- `#829`: LLVM2 experimental backend

## More

- [cargo-trust/README.md](cargo-trust/README.md): verifier-specific usage and contract
