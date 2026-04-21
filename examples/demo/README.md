# tRust Demo: Catching Bugs and Proving Safety

This demo walks through tRust's core verification capabilities in six steps.
It shows how tRust catches real bugs with counterexamples, proves fixed code
safe, verifies its own source code, and generates proof reports.

**Time:** ~5 minutes
**Prerequisites:** Build tRust (`./x.py build compiler library`) or use `--standalone` mode.

---

## Step 1: The Buggy Program

Open `buggy_binary_search.rs`. This is a textbook binary search with two
classic bugs that have caused real-world failures (including in Java's
`Arrays.binarySearch` -- see Bloch 2006):

```rust
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut low: usize = 0;
    let mut high: usize = arr.len() - 1;   // BUG: underflows on empty array

    while low <= high {
        let mid = (low + high) / 2;         // BUG: overflows for large indices
        // ...
    }
    None
}
```

**Bug 1:** `arr.len() - 1` underflows when the array is empty (`0_usize - 1` wraps to `usize::MAX`).

**Bug 2:** `(low + high) / 2` overflows when `low + high > usize::MAX`.

Both bugs are silent in release mode (wrapping arithmetic) and panic only in
debug mode. Standard Rust compilation catches neither at compile time.

## Step 2: tRust Catches the Bugs

Run tRust on the buggy program:

```bash
cargo trust check examples/demo/buggy_binary_search.rs
```

tRust analyzes every arithmetic operation, generates verification conditions,
and dispatches them to z4 (SMT solver). Output:

```
note: tRust [overflow:sub]: arithmetic overflow (Sub) -- FAILED (z4-smtlib, 50ms)
  counterexample: arr.len() = 0  (empty array triggers underflow)

note: tRust [overflow:add]: arithmetic overflow (Add) -- FAILED (z4-smtlib, 12ms)
  counterexample: low = 9223372036854775807, high = 9223372036854775807

=== tRust Verification Report ===
Summary: 0 proved, 2 failed, 0 unknown (2 total)
Result: FAIL
```

tRust found both bugs and produced concrete counterexamples -- values that
trigger each overflow. No tests needed. No fuzzing. Mathematical proof.

## Step 3: The Fixed Program

Open `safe_binary_search.rs`. Three fixes eliminate all bugs:

```rust
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    if arr.is_empty() { return None; }          // FIX 1: empty guard

    let mut low: usize = 0;
    let mut high: usize = arr.len() - 1;        // safe: len >= 1

    while low <= high {
        let mid = low + (high - low) / 2;       // FIX 2: safe midpoint
        // ...
        match mid.checked_sub(1) {               // FIX 3: checked decrement
            Some(new_high) => high = new_high,
            None => break,
        }
    }
    None
}
```

## Step 4: tRust Proves It Safe

Run tRust on the fixed program:

```bash
cargo trust check examples/demo/safe_binary_search.rs
```

Output:

```
note: tRust [overflow:sub]: arithmetic overflow (Sub) -- PROVED (z4-smtlib, 8ms)
note: tRust [overflow:add]: arithmetic overflow (Add) -- PROVED (z4-smtlib, 5ms)
note: tRust [bounds]: index out of bounds        -- PROVED (z4-smtlib, 12ms)

=== tRust Verification Report ===
Summary: 3 proved, 0 failed, 0 unknown (3 total)
Result: PASS
```

Every verification condition is discharged. z4 has mathematically proven that
no input can trigger overflow, underflow, or out-of-bounds access.

## Step 5: Self-Verification

tRust verifies its own source code. Run standalone analysis on the trust-types
crate (the core type definitions used throughout the verification pipeline):

```bash
cargo trust check --standalone -p trust-types
```

This demonstrates self-hosting: the verification tool analyzing its own
implementation for correctness.

## Step 6: Proof Report

Generate an HTML proof report with a visual dashboard:

```bash
cargo trust check examples/demo/safe_binary_search.rs \
    --report-dir examples/demo/report
```

This writes three files to `examples/demo/report/`:
- `report.json` -- machine-readable verification results
- `report.html` -- visual dashboard with proof status, timing, and solver info
- `report.ndjson` -- newline-delimited JSON for streaming/CI integration

Open `report.html` in a browser to see the proof dashboard.

---

## Automated Demo

Run the full demo non-interactively:

```bash
./examples/demo/run_demo.sh
```

## Key Concepts

| Concept | What It Means |
|---------|---------------|
| **Verification Condition (VC)** | A logical formula that must hold for a property to be safe. tRust generates VCs for every arithmetic op, array access, and user annotation. |
| **PROVED** | z4 found a mathematical proof that no input violates the VC. |
| **FAILED + counterexample** | z4 found a concrete input that violates the VC. This is a real bug. |
| **z4** | The primary SMT solver in the dMATH tool suite. Handles ~90% of obligations. |
| **Standalone mode** | Source-level analysis without the full compiler. Useful for quick checks. |

## What tRust Catches Today

- Integer overflow and underflow (signed and unsigned)
- Division by zero and remainder by zero
- Array/slice index out of bounds
- Unreachable code assertions
- User-specified pre/postconditions (`#[requires(...)]`, `#[ensures(...)]`)

## Further Reading

- `[internal document]` -- full design document (three big ideas, proof levels, milestones)
- `examples/` -- more verification examples (overflow, division, bounds, etc.)
- `crates/trust-report/` -- proof report generation
- `cargo-trust/` -- the `cargo trust` subcommand
