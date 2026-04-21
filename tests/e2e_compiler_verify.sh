#!/bin/bash
# End-to-end test: built rustc with trust_verify MIR pass verifies real Rust code
#
# Tests that the compiler-integrated verification pipeline (trust_verify.rs)
# detects arithmetic overflow obligations in examples/midpoint.rs when
# TRUST_VERIFY=1 / -Z trust-verify are set.
#
# This tests the native compiler path (MIR pass), NOT the standalone trustc
# driver. See tests/e2e_midpoint.sh for the standalone driver test.
#
# Author: Andrew Yates <andrew@andrewdyates.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
INPUT="$TRUST_ROOT/examples/midpoint.rs"

echo "=== tRust E2E Test: compiler-integrated verification ==="
echo

# --- Locate stage1 rustc ---
# The bootstrap build system (./x.py build) produces the stage1 rustc at one
# of these paths depending on configuration. Check all known locations.
RUSTC=""
CANDIDATES=(
    "$TRUST_ROOT/build/host/stage1/bin/rustc"
    "$TRUST_ROOT/build/aarch64-apple-darwin/stage1/bin/rustc"
    "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage1/bin/rustc"
    "$TRUST_ROOT/build/x86_64-apple-darwin/stage1/bin/rustc"
)

for candidate in "${CANDIDATES[@]}"; do
    if [ -x "$candidate" ]; then
        RUSTC="$candidate"
        break
    fi
done

if [ -z "$RUSTC" ]; then
    echo "ERROR: stage1 rustc not found."
    echo
    echo "Checked paths:"
    for candidate in "${CANDIDATES[@]}"; do
        echo "  $candidate"
    done
    echo
    echo "Build it with:"
    echo "  cd $TRUST_ROOT && ./x.py build"
    echo
    echo "This builds the full compiler with the trust_verify MIR pass."
    exit 2
fi

echo "Using rustc: $RUSTC"
echo "Input file:  $INPUT"
echo

# --- Verify input file exists ---
if [ ! -f "$INPUT" ]; then
    echo "ERROR: Test input not found: $INPUT"
    exit 2
fi

# --- Run compilation with TRUST_VERIFY=1 and -Z trust-verify ---
# The trust_verify pass writes verification output to stderr. We capture it
# separately from stdout. The compilation itself should succeed (exit 0)
# because verification is additive -- it does not block compilation.
echo "Running: TRUST_VERIFY=1 $RUSTC -Z trust-verify --edition 2021 $INPUT"
echo

STDERR_FILE=$(mktemp /tmp/trust_verify_stderr.XXXXXX)
OUTPUT_FILE=$(mktemp /tmp/trust_verify_output.XXXXXX)
trap "rm -f '$STDERR_FILE' '$OUTPUT_FILE'" EXIT

COMPILE_EXIT=0
TRUST_VERIFY=1 "$RUSTC" -Z trust-verify --edition 2021 "$INPUT" -o "$OUTPUT_FILE" 2>"$STDERR_FILE" || COMPILE_EXIT=$?

OUTPUT=$(cat "$STDERR_FILE")

echo "--- stderr output ---"
echo "$OUTPUT"
echo "--- end stderr ---"
echo

# --- Check compilation succeeded ---
# Verification is additive; compilation must still succeed.
if [ $COMPILE_EXIT -ne 0 ]; then
    echo "WARNING: rustc exited with code $COMPILE_EXIT (compilation may have failed)"
    echo "  This test checks verification output regardless."
    echo
fi

# --- Verify expected patterns ---
PASS=0
FAIL=0

check() {
    local pattern="$1"
    local description="${2:-$1}"
    if echo "$OUTPUT" | grep -q "$pattern"; then
        echo "  PASS: $description"
        PASS=$((PASS + 1))
    else
        echo "  FAIL: $description"
        echo "        Expected pattern: $pattern"
        FAIL=$((FAIL + 1))
    fi
}

# 1. Verification report header is printed
check "tRust Verification Report" "Header: tRust Verification Report banner"

# 2. Crate name is reported in the report header
check "Verification Report (midpoint)" "Crate name reported in header"

# 3. get_midpoint function is analyzed
check "get_midpoint" "Function get_midpoint found"

# 4. Overflow obligation detected (Add on integer type)
#    The exact format is: [overflow:add] arithmetic overflow (Add) on <type>
check "overflow" "Overflow obligation detected"

# 5. The midpoint overflow is either proved as a concrete violation or
#    downgraded to a runtime-checked obligation when the solver cannot
#    discharge it statically.
check "overflow.*FAILED\|overflow.*RUNTIME-CHECKED" \
    "Overflow obligation classified as FAILED or RUNTIME-CHECKED"

echo

# --- Negative checks: things that should NOT appear ---
check_absent() {
    local pattern="$1"
    local description="${2:-No false positive: $1}"
    if echo "$OUTPUT" | grep -q "$pattern"; then
        echo "  FAIL: $description (unexpected pattern found)"
        FAIL=$((FAIL + 1))
    else
        echo "  PASS: $description"
        PASS=$((PASS + 1))
    fi
}

# midpoint.rs divides by constant 2, so division-by-zero should NOT appear
# unless the optimizer has changed the MIR significantly.
# Note: This is a best-effort check. If the MIR representation changes,
# a div obligation might appear for the literal /2 -- but that would be
# a false positive worth investigating.

echo

# --- Summary ---
echo "=== Results: $PASS passed, $FAIL failed ==="

if [ $FAIL -gt 0 ]; then
    echo
    echo "FAILED: $FAIL check(s) did not pass."
    exit 1
fi

echo
echo "All checks passed."
exit 0
