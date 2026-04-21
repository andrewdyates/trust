# cargo-trust

**Verify Rust code. Fix what fails.**

`cargo trust` is the CLI for [tRust](https://github.com/andrewdyates/trust), a fork of the Rust compiler that proves your code is correct. It finds real bugs with counterexamples, then fixes them automatically.

```
$ cargo trust check examples/midpoint.rs

=== tRust Verification Report ===
Level: L0 | Timeout: 5000ms | Duration: 42ms

  [PROVED] [overflow:add] arithmetic overflow (Add) (z4-smtlib, 3ms)
  [FAILED] [overflow:mul] arithmetic overflow (Mul) (z4-smtlib, 5ms)

Summary: 1 proved, 1 failed, 0 unknown (2 total)
Result: FAIL
=================================
```

## Install

```bash
# From the tRust repo root:
cargo build -p cargo-trust --release
ln -s $(pwd)/target/release/cargo-trust /usr/local/bin/cargo-trust
```

### Prerequisites

- **tRust compiler** (stage1): `python3 x.py build compiler library`
- **z4 SMT solver**: Build from [andrewdyates/z4](https://github.com/andrewdyates/z4) and put on PATH

Without the stage1 compiler, `cargo trust check` falls back to `--standalone` source-level analysis automatically.

## Subcommands

### `cargo trust check`

Verify the current crate or a single file (check only, no codegen).

```bash
cargo trust check                          # verify the current crate
cargo trust check src/lib.rs               # verify a single file
cargo trust check --format json            # JSON output
cargo trust check --standalone             # source analysis without compiler
cargo trust check --fresh                  # bypass verification cache
cargo trust check --solver z4              # force a specific solver
```

Invokes the stage1 rustc with `-Z trust-verify`, parses verification diagnostics from the compiler output, and produces a summary report. When a property cannot be proved, z4 produces a counterexample with concrete input values.

If the stage1 compiler is not found, `check` automatically falls back to `--standalone` source-level analysis. Standalone mode parses Rust source files to extract function signatures and spec attributes, generates basic verification conditions, and prints a summary without building the full compiler.

### `cargo trust build`

Verify and build the crate (check + codegen).

```bash
cargo trust build                          # verify and produce a binary
cargo trust build --format json            # JSON output
```

Same as `check` but also produces compiled output.

### `cargo trust report`

Generate a verification report in the requested format.

```bash
cargo trust report                         # terminal report
cargo trust report --format json           # canonical JSON report
cargo trust report --format html           # HTML dashboard report
cargo trust report --report-dir ./out      # write JSON, HTML, NDJSON to directory
```

Runs verification (check semantics) and renders results using the `trust-report` crate. When `--report-dir` is specified, writes `report.json`, `report.html`, and `report.ndjson` to the given directory.

### `cargo trust loop`

Run the prove-strengthen-backprop convergence loop.

```bash
cargo trust loop src/lib.rs                # run the loop on a file
cargo trust loop --max-iterations 5        # limit iterations
```

Each iteration: (1) verify with rustc, (2) analyze failures and propose rewrites, (3) apply rewrites via `trust-backprop`, (4) check convergence. Stops when all obligations are proved, the proof frontier converges, or the iteration limit is reached.

The `--rewrite` flag enables loop mode on `check`/`build`:

```bash
cargo trust check --rewrite                # check with rewrite loop
cargo trust check --rewrite --max-iterations 3
```

### `cargo trust diff`

Compare verification state between git refs or saved report files.

**Git ref comparison** (recommended for CI):

```bash
cargo trust diff main..feature             # double-dot syntax
cargo trust diff --from main --to HEAD     # explicit refs
cargo trust diff --from HEAD~5 --to HEAD   # diff last 5 commits
cargo trust diff main..HEAD --scope crates/  # scope to a path prefix
cargo trust diff main..HEAD --format json  # JSON diff output
```

Analyzes changed Rust source files at both refs using `git show` (no checkout needed). Produces function-level diff of verification state: specs gained/lost, safety changes, functions added/removed.

**Baseline file comparison**:

```bash
cargo trust diff --baseline report.json                    # baseline vs empty (CI gate)
cargo trust diff --baseline base.json --current cur.json   # compare two saved reports
```

Loads `JsonProofReport` files and compares function-level verification status. Also supports legacy report formats.

Exits non-zero when regressions are detected, making it suitable as a CI gate.

### `cargo trust init`

Scaffold `#[requires]` and `#[ensures]` verification annotations for a crate.

```bash
cargo trust init                           # scaffold annotations (print to stdout)
cargo trust init --inline                  # write annotations into source files
cargo trust init src/lib.rs                # scaffold for a single file
```

Scans public functions for signatures that suggest preconditions (division parameters, slice bounds, raw pointers, index parameters) and generates heuristic annotation scaffolds. Also creates a default `trust.toml` if one does not exist.

**Heuristic annotations generated:**

| Pattern | Generated precondition |
|---------|----------------------|
| Parameter named `divisor`, `denom`, `b`, `rhs` with numeric type | `name != 0` |
| Slice parameter (`&[T]`) | `name.len() > 0` |
| Raw pointer parameter (`*const T`, `*mut T`) | `!name.is_null()` |
| Index parameter (`index`, `idx`, `pos`) with unsigned type + slice | `index < slice.len()` |
| `unsafe fn` | `true /* SAFETY: document invariants */` |
| `Result<T, E>` return type | `true /* TODO: specify when result.is_ok() */` |
| `Option<T>` return type | `true /* TODO: specify when result.is_some() */` |

### `cargo trust solvers`

Detect and report the status of dMATH solver binaries.

```bash
cargo trust solvers                        # terminal status table
cargo trust solvers --format json          # JSON output
cargo trust solvers --solver z4            # check a single solver
cargo trust doctor                         # alias for solvers
```

Searches PATH and common installation directories for z4, zani, sunder, certus, tla2, and lean5. Reports version information and availability grouped by proof level.

### `cargo trust help`

Show usage information for all subcommands and options.

```bash
cargo trust help
cargo trust --help
```

## Options

All options can be used with any applicable subcommand.

| Option | Description | Applies to |
|--------|-------------|------------|
| `--format <fmt>` | Output format: `terminal` (default), `json`, `html` | all |
| `--standalone` | Source-level analysis without the compiler | check, report |
| `--fresh` | Bypass the verification cache | check, build, report |
| `--rewrite` | Enable the prove-strengthen-backprop loop | check, build |
| `--max-iterations <N>` | Maximum loop iterations (default: 10) | loop, check --rewrite |
| `--from <ref>` | Git ref for the "from" side of diff | diff |
| `--to <ref>` | Git ref for the "to" side (default: HEAD) | diff |
| `--scope <path>` | Scope git diff to a path prefix | diff |
| `--baseline <path>` | Baseline report JSON file | diff |
| `--current <path>` | Current report JSON file | diff |
| `--report-dir <dir>` | Write report files (JSON, HTML, NDJSON) | check, build, report |
| `--solver <name>` | Force a specific solver backend | check, build, report |
| `--inline` | Write annotations into source files | init |

## Exit Codes

| Code | Meaning |
|------|---------|
| **0** | Success. All verification obligations proved, no compiler errors |
| **1** | Verification failures detected, or compiler errors occurred. For `diff`: regressions detected |
| **2** | Internal error: stage1 rustc not found, missing required flags (e.g., `--baseline` for diff), invalid arguments |

## Configuration

Create a `trust.toml` in your crate root:

```toml
# Enable/disable verification
enabled = true

# Verification level: L0 (basic), L1 (standard), L2 (exhaustive)
level = "L0"

# Solver timeout in milliseconds
timeout_ms = 5000

# Functions to skip during verification (glob patterns)
skip_functions = ["test_*", "bench_*"]

# Functions to verify (empty = all; specify to limit scope)
verify_functions = []
```

Run `cargo trust init` to generate this file automatically.

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `TRUST_RUSTC` | auto-detected | Path to the stage1 tRust rustc binary |
| `TRUST_SOLVER` | (set by --solver) | Force a specific solver backend |
| `TRUST_VERIFY` | `1` (set automatically) | Enables verification in the compiler |
| `RUSTFLAGS` | (merged) | tRust flags are appended to existing RUSTFLAGS |
| `NO_COLOR` | unset | Disable color output in terminal diff |

The stage1 compiler is auto-detected from the tRust repo build directory. Set `TRUST_RUSTC` to override.

## CI/CD Integration

### GitHub Actions: regression gate

Use `cargo trust diff` to block PRs that introduce verification regressions:

```yaml
name: tRust Verification Gate
on: [pull_request]
jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0  # full history for git diff

      - name: Check for verification regressions
        run: |
          cargo trust diff origin/main..HEAD --format json > diff.json
          # Exit code 1 if regressions detected, 0 if clean
          cargo trust diff origin/main..HEAD

      - name: Upload diff report
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: trust-diff
          path: diff.json
```

### Pre-commit hook

```bash
#!/bin/sh
# .git/hooks/pre-commit
cargo trust check --standalone --format json > /dev/null 2>&1
if [ $? -ne 0 ]; then
  echo "tRust: verification failures detected. Run 'cargo trust check' for details."
  exit 1
fi
```

The diff subcommand exits with code 1 when regressions are detected (specs lost, specified functions removed, or functions that became unsafe), making it a natural CI gate.

## Verification Cache

Results are cached in target/trust-cache/verification.json. On subsequent runs, only changed functions are re-verified. Use `--fresh` to bypass the cache and re-verify everything.

## Solver Requirements by Proof Level

| Level | Solvers Required | Description |
|-------|-----------------|-------------|
| L0 (basic) | z4, zani, certus | Arithmetic overflow, division by zero, bounds checks |
| L1 (standard) | L0 + sunder | Deductive verification, strongest postconditions |
| L2 (exhaustive) | L1 + tla2, lean5 | Temporal logic, higher-order proofs, induction |

Run `cargo trust solvers` to check which solvers are available on your system.

## What It Proves

tRust proves safety properties automatically from MIR -- no annotations needed for basic checks:

| Property | Example |
|----------|---------|
| **No arithmetic overflow** | `a + b` won't wrap for any inputs |
| **No division by zero** | Divisor is provably non-zero |
| **No out-of-bounds access** | Array index is within bounds |
| **No integer truncation** | Cast doesn't lose bits |
| **Shift amount in range** | Shift count < bit width |
| **Contract satisfaction** | `#[requires]` / `#[ensures]` hold |

When a property cannot be proved, z4 produces a **counterexample**: concrete input values that trigger the bug.

## How It Works

```
    cargo trust check foo.rs
              |
    +---------v----------+
    |   tRust compiler   |
    |                    |
    |  Rust -> MIR       |
    |  MIR -> VCs        |  trust-mir-extract, trust-vcgen
    |  VCs -> z4 (SMT)   |  trust-router, z4
    |                    |
    |  PROVED / FAILED   |
    +--------+-----------+
             |
             v
    Exit 0 (all proved)  or  Exit 1 (failures)
```

The compiler does the hard work. It is a fork of `rust-lang/rust` with a verification pass inserted after MIR optimization. The pass:

1. **Extracts** each function's MIR into a logical model (`trust-mir-extract`)
2. **Generates** verification conditions -- one per potential bug (`trust-vcgen`)
3. **Dispatches** each VC to z4 as an SMT-LIB2 query (`trust-router`)
4. **Reports** results with counterexamples via rustc diagnostics

The `loop` subcommand adds an outer loop: AI Model reads proof failures and counterexamples, proposes source fixes, and `trust-backprop` applies them. The compiler re-proves the fix. The loop converges when z4 proves everything.
