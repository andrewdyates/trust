# Basic Contracts

This is the Tier 2 public contract corpus for tRust.

It exists to show the current public spec surface:

- `trust-spec` as a Cargo dependency
- namespaced `#[trust::requires(...)]`
- namespaced `#[trust::ensures(...)]`
- crate-local `trust.toml`

## Run It

From this directory:

```bash
cargo check
cargo trust check --standalone
```

`cargo check` confirms that the crate compiles as ordinary Rust with the
namespaced attrs in place.

`cargo trust check --standalone` currently gives the most honest public result
for this crate: it inventories public APIs, finds `trust::` specs, and flags
unspecified public functions.

## What This Example Is For

- basic preconditions
- basic postconditions
- arithmetic-safety-adjacent APIs
- collections and loop-shaped code in a crate-first layout

## What It Is Not Claiming Yet

- full compiler-backed semantic proving of every `trust::` contract here
- a stable public `trust::invariant` loop-invariant workflow
- an L2 or temporal example

For the enforced single-file regression suite, see ../../verify_*.rs.
