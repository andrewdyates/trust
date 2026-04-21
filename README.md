# tRust

**Author:** Andrew Yates (andrewyates.name@gmail.com)
**Version:** 0.1.0
**License:** MIT OR Apache-2.0

**License Note:** `tRust` is a fork of `rust-lang/rust`. The upstream `rustc`
compiler and standard library are dual-licensed under MIT and Apache-2.0
unless otherwise specified, so this repository is distributed under
`MIT OR Apache-2.0` at the top level. See `LICENSE-MIT`,
`LICENSE-APACHE`, and per-crate `Cargo.toml` metadata for details.

> **Preview Release (April 2026)** -- Active research prototype. The verification pipeline calls real z4 SMT solvers on real verification conditions and produces real proofs/counterexamples. Not yet suitable for production use.

**Rust You Can Trust.** A self-authoring, self-proving compiler.

tRust is a fork of the Rust compiler (`rustc`) that adds native verification. When your code compiles under tRust, it is proven correct -- automatically, with no annotations.

```
$ cargo trust build

   Compiling my_project v0.1.0
   Proving... (iter 1: 71% | iter 2: 86% | iter 3: 93%)

   tRust build complete after 3 iterations

     functions:     142
     fully proved:  127  (89%)
     bounded check:  11  ( 8%)
     unproved:        4  ( 3%)

   Source modifications: 31 changes across 12 files
   Proof report: target/trust/report.html
```

## Three Big Ideas

**1. The compiler proves the code.** tRust compiles Rust and proves correctness properties -- no panics, no overflow, no out-of-bounds, no deadlocks, functional correctness -- using a suite of integrated verification solvers.

**2. AI infers the strongest possible proof.** An AI agent reads the code and proposes the strongest types, invariants, and specifications the code can support. The AI is allowed to be wrong. The proofs are not.

**3. Backpropagation to a better program.** When proof fails, the compiler modifies the source to make the proof succeed -- fixing bugs, strengthening types, or proposing a different algorithm. No existing compiler does this.

The three ideas form a loop: **prove -> strengthen -> backpropagate -> re-prove**. The loop converges to the maximally proven version of the program.

## Current Status

| Milestone | Status | Description |
|-----------|--------|-------------|
| **M1** | **Done** | `./x.py build` produces a working `rustc` with verification pass |
| **M2** | **~90%** | End-to-end: MIR -> vcgen -> z4 -> real proofs/counterexamples |
| **M3** | **~60%** | Pipeline tested at 120+ function scale; CLI integration in progress |
| **M4** | **~40%** | Heuristic spec inference works; LLM integration in design |
| **M5** | **~30%** | All loop components exist; end-to-end demo with real solver pending |

**By the numbers (April 2026):**
- ~29 verification crates, ~557K lines of Rust
- 11,800+ tests passing across all crates
- ~580 issues closed
- 8 solver backends: z4 (native + smtlib), zani, certus, tla2, lean5, cegar, mock
- Real z4 verification: 5-8ms per obligation, real counterexamples

## Example (Working Today)

```rust
// examples/midpoint.rs
fn get_midpoint(a: usize, b: usize) -> usize {
    (a + b) / 2
}
```

### Native compiler path

```
$ TRUST_VERIFY=1 ./build/host/stage1/bin/rustc -Z trust-verify --edition 2021 examples/midpoint.rs

=== tRust Verification Pass ===
  Crate: midpoint
  get_midpoint: overflow [PENDING]
```

### Standalone wrapper (z4 integration)

```
$ trustc --edition 2021 examples/midpoint.rs

=== tRust Verification Report ===
  get_midpoint
    arithmetic overflow (Add) FAILED (z4) counterexample: a = 1, b = 18446744073709551615

  1 functions, 0 proved, 1 failed, 0 unknown
```

tRust detects the overflow bug -- `(a + b)` wraps for large inputs -- and provides a concrete counterexample via z4. The textbook fix (`a/2 + b/2 + (a%2 + b%2)/2`) is proven safe with value-range analysis.

## Installation

### Prerequisites

- Standard Rust build dependencies (see [rust-lang/rust INSTALL.md](https://github.com/rust-lang/rust/blob/master/INSTALL.md))
- Python 3.10+
- Nightly Rust toolchain with `rustc-dev`
- **z4 SMT solver** on PATH (for real proofs)

### Usage

```bash
# 1. Clone the repo
git clone https://github.com/andrewdyates/trust tRust
cd tRust

# 2. Install nightly toolchain with rustc internals
rustup toolchain install nightly
rustup component add rustc-dev --toolchain nightly

# 3. Verify z4 is available (required for real proofs)
z4 --version
# Expected: "Z4 version 1.0.0" (or similar)

# 4. Run REAL z4 verification tests (the proof that tRust works)
cargo test --manifest-path crates/trust-integration-tests/Cargo.toml \
  --test real_z4_verification -- --nocapture

# Expected output (6 tests, all passing):
#   z4 detected: Z4 version 1.0.0
#   Generated 1 VCs for buggy_midpoint
#     VC: ArithmeticOverflow { op: Add, ... }
#   z4 result: Failed { solver: "z4-smtlib", time_ms: 6,
#     counterexample: { hi = 1, lo = 18446744073709551615 } }
#   test test_real_z4_detects_midpoint_overflow ... ok
#   ...
#   test result: ok. 6 passed; 0 failed

# 5. Run the full test suite (~11,800 tests)
cargo test -p trust-types -p trust-vcgen -p trust-router -p trust-report \
  -p trust-cache -p trust-convergence -p trust-proof-cert -p trust-temporal \
  -p trust-strengthen -p trust-config

# 6. Check which solvers are available
cargo run --manifest-path cargo-trust/Cargo.toml -- trust solvers

# 7. Build the full tRust compiler (optional, takes a while)
./x.py build

# 8. Verify a file using the native MIR pass
TRUST_VERIFY=1 ./build/host/stage1/bin/rustc -Z trust-verify --edition 2021 examples/midpoint.rs
```

### What the Tests Prove

| Test | What z4 Does | Time |
|------|-------------|------|
| Buggy midpoint `(lo+hi)/2` | Finds overflow: `lo=2^64-1, hi=1` | 6ms |
| Division by constant 2 | Proves safe (UNSAT) | 8ms |
| Division by variable | Finds div-by-zero: `b=0` | 6ms |
| Safe midpoint `lo+(hi-lo)/2` | Finds missing precondition: `hi=0, lo=1` | 6ms |

## Architecture

tRust is the full `rust-lang/rust` source tree with a verification pass added after MIR construction:

```
Source -> rustc_parse -> rustc_ast -> rustc_hir -> rustc_mir_build
                                                       |
                                               +-------v-------+
                                               |  VERIFICATION  |
                                               |  PASS (new)    |
                                               +-------+-------+
                                                       |
                                               LLVM codegen
```

### Verification Pipeline

```
MIR --> trust-mir-extract --> trust-vcgen --> trust-router --> solvers
                                                                  |
         +--------------------------------------------------------+
         v
    z4 (SMT) . zani (BMC) . sunder (deductive) . certus (ownership)
    tla2 (temporal) . lean5 (higher-order) . gamma-crown (neural net)
```

### Verification Crates

| Crate | Role |
|-------|------|
| `trust-mir-extract` | MIR -> logical model extraction |
| `trust-vcgen` | Verification condition generation (WP transformer, overflow, Horn clauses) |
| `trust-router` | VC dispatch to solvers (portfolio racer, termination) |
| `trust-cache` | Incremental verification result caching |
| `trust-cegar` | Counterexample-guided abstraction refinement |
| `trust-symex` | Symbolic execution engine |
| `trust-report` | Verification report generation (text + HTML) |
| `trust-proof-cert` | Proof certificate generation and chain verification |
| `trust-types` | Shared type definitions (Formula, Ty, proof strength) |
| `trust-strengthen` | AI specification inference (Idea 2) |
| `trust-backprop` | Source rewriting from proof failures (Idea 3) |
| `trust-convergence` | Fixed-point detection for the verification loop |
| `trust-loop` | Loop orchestration |
| `trust-driver` | Compiler integration driver (rustc_private) |
| `trust-config` | Configuration and feature flags |
| `trust-debug` | Debug output and tracing |
| `trust-lean5` | lean5 prover integration |
| `trust-temporal` | Temporal property verification (state machines) |
| `trust-transval` | Translation validation |
| `trust-testgen` | Automatic test generation from counterexamples |
| `trust-runtime` | Runtime verification support |
| `trust-integration-tests` | Cross-crate integration tests |

### Proof Dimensions

Two orthogonal dimensions classify every proof result:

**ReasoningKind** -- How the proof was obtained:
SMT, Inductive, BoundedModelCheck, Deductive, PDR, AbstractInterpretation, ExhaustiveFinite, Constructive

**AssuranceLevel** -- How much to trust it:
- `Trusted` -- tool output taken at face value
- `SmtBacked` -- backed by SMT solver proof
- `Certified` -- independently checkable proof certificate

### Proof Levels

| Level | What | How |
|-------|------|-----|
| **0: Safety** | No panics, overflow, OOB, div-by-zero, deadlocks | Extracted from MIR. z4 + zani. Zero annotation. |
| **1: Functional** | Strongest postconditions (sort -> sorted permutation) | sunder infers from implementation. |
| **2: Domain** | Linearizability, fairness, robustness | AI-proposed, solver-verified. |

### Escape Hatches

| Annotation | Meaning |
|------------|---------|
| *(none)* | Full verification + rewriting (default) |
| `#[trust_bounded(N)]` | Bounded check to depth N |
| `#[trust_skip]` | No verification; taint propagates |
| `#[trust_freeze]` | Verify but don't rewrite |
| `#[trust_axiom("...")]` | Assert without proof; flagged in audit |

## Upstream Tracking

tRust tracks `rust-lang/rust` via the `upstream` remote. All valid Rust compiles identically. Verification is additive.

```bash
git fetch upstream
git merge upstream/main
```

## Documentation

| Document | Content |
|----------|---------|
| [VISION.md](VISION.md) | Full design: three big ideas, architecture, milestones, TCB analysis |
| `docs/` | Design documents, architecture specs, and reference material |

## License

This repository is distributed under **MIT OR Apache-2.0**.

Why: `tRust` is a fork of `rust-lang/rust`, and the upstream `rustc`
compiler source and standard library are dual-licensed under MIT and
Apache-2.0 unless otherwise specified. `tRust`-owned top-level package
metadata in this repo follows that same dual-license model so the
repository-level license statement matches the distributed contents.

See [LICENSE-APACHE](LICENSE-APACHE), [LICENSE-MIT](LICENSE-MIT), and
individual crate `Cargo.toml` files for package-level metadata.
