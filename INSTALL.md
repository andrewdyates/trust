# Install tRust

> **Current status (2026-04-23):** tRust does not currently have a finished packaged installer. The supported public install flow is a local from-source build, linked into `rustup` as `trust`, plus `cargo-trust` installed from this checkout.

This repository is a fork of `rust-lang/rust`, but the old upstream `INSTALL.md`
content is not the current tRust install story.

## Canonical Install Docs

- [README.md](README.md): current product status and quick start

## Short Version

```bash
git clone https://github.com/andrewdyates/tRust tRust
cd tRust

rustup toolchain install nightly
rustup component add rustc-dev --toolchain nightly

./x.py build --stage 1
rustup toolchain link trust ./build/host/stage1

cargo install --path cargo-trust --force
```

If your build emits a target-specific sysroot instead of `./build/host/stage1`,
link that path instead.

After install, use the linked `trust` toolchain for ordinary Rust workflows:

```bash
cargo +trust check
cargo +trust build
cargo +trust test
```

For verification, the current canonical commands are:

```bash
cargo trust check
cargo trust check --format json
```

## Packaging Status

Packaged releases, combined installers, and a fully integrated `cargo-trust`
distribution path are still in progress. Until that lands, use the root
README quick start as the source of truth for the supported local-build
workflow.
