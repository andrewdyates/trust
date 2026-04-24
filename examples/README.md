# Examples

This directory is organized as a tiered verification corpus.

Current baseline:

- `cargo trust check` is the verifier front door
- native compiler-backed runs depend on a discoverable tRust compiler, usually a
  locally built toolchain linked into `rustup` as `trust`
- crate-based `trust::` examples still pair most honestly with
  `cargo trust check --standalone`

## Tier 0: Fast Smoke

Use these first when you want a quick compiler-backed verification run:

- `midpoint.rs`
- `binary_search.rs`
- `binary_search_fixed.rs`
- `demo/`

These are the smallest end-to-end examples for "bug found" and "fix proved" on
the native compiler-backed path.

## Tier 1: Enforced L0 Regression Suite

These files are the machine-enforced single-file corpus:

- `verify_*.rs`
- `verify_*_safe.rs`

They cover the current L0 story: overflow, divide-by-zero, bounds, assertions,
and closely related proof obligations.

Notes:

- The top-of-file comments are part of the corpus metadata.
- Some contract-oriented files in this tier still use legacy contracts syntax.
  They are kept that way because the single-file regression path still targets
  the native compiler-backed verifier, not the crate-based `trust::` surface
  with `trust-spec`.

## Tier 2: Public L1 Contract Corpus

Use these when you want the public-facing contract surface:

- `contracts/basic-contracts/`

This tier is crate-based and uses:

- `Cargo.toml`
- `trust.toml`
- `trust-spec`
- `#[trust::requires(...)]` / `#[trust::ensures(...)]`

Today this tier is best paired with `cargo trust check --standalone`, which
recognizes the namespaced attrs and reports spec coverage honestly. Treat it as
contract-surface inventory, not as the main proof-artifact path.

## Tier 3: Workflow and Artifact Corpus

Use these when you want a repeatable local walkthrough:

- `demo/`

This is where to learn report generation, proof diffs, and cache behavior on
the compiler-backed path when a discoverable tRust compiler is available.

## Tier 4: Research and Showcase

These examples are useful for orientation, but they are not yet the stable
front door:

- `showcase/`

Expect a mix of L0-oriented demonstrations, roadmap sketches, and future-facing
material.
