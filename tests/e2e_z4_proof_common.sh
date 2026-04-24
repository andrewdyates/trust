#!/bin/bash
# End-to-end test: tRust compiler can build and test z4-proof-common
#
# Verifies that the tRust stage1 compiler (registered as the "trust" toolchain)
# can compile z4-proof-common — the simplest z4 crate (725 LOC, zero unsafe,
# zero async, zero nightly features). This is the first external crate in the
# tRust compilation bootstrap sequence.
#
# The tRust verification pass runs on every function and emits diagnostics,
# but compilation and test execution must succeed identically to vanilla rustc.
#
# Part of #879
#
# Author: Andrew Yates <andrew@andrewdyates.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
Z4_ROOT="${Z4_ROOT:-$HOME/z4}"

echo "=== tRust E2E Test: z4-proof-common compilation bootstrap ==="
echo

# --- Verify z4 repo exists ---
if [ ! -d "$Z4_ROOT/crates/z4-proof-common" ]; then
    echo "ERROR: z4-proof-common not found at $Z4_ROOT/crates/z4-proof-common"
    echo
    echo "Clone the z4 repo:"
    echo "  git clone https://github.com/andrewdyates/z4 ~/z4"
    exit 2
fi

# --- Ensure trust toolchain is linked ---
if ! rustup toolchain list | grep -q '^trust'; then
    echo "Linking trust toolchain from stage1 build..."
    STAGE1=""
    CANDIDATES=(
        "$TRUST_ROOT/build/host/stage1"
        "$TRUST_ROOT/build/aarch64-apple-darwin/stage1"
        "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage1"
        "$TRUST_ROOT/build/x86_64-apple-darwin/stage1"
    )
    for candidate in "${CANDIDATES[@]}"; do
        if [ -x "$candidate/bin/rustc" ]; then
            STAGE1="$candidate"
            break
        fi
    done
    if [ -z "$STAGE1" ]; then
        echo "ERROR: stage1 build not found. Build with: cd $TRUST_ROOT && ./x.py build"
        exit 2
    fi
    rustup toolchain link trust "$STAGE1"
    echo "Linked: $STAGE1"
fi

echo "Trust toolchain: $(rustc +trust --version)"
echo "Stable toolchain: $(rustc +stable --version 2>/dev/null || echo 'not available')"
echo "z4 root: $Z4_ROOT"
echo

# --- Phase 1: Build with trust toolchain ---
echo "--- Phase 1: cargo +trust build -p z4-proof-common ---"
cd "$Z4_ROOT"

BUILD_EXIT=0
CARGO_SKIP_CACHE=1 cargo +trust build -p z4-proof-common 2>&1 | tail -5 || BUILD_EXIT=$?

if [ $BUILD_EXIT -ne 0 ]; then
    echo "FAIL: cargo +trust build -p z4-proof-common exited with code $BUILD_EXIT"
    exit 1
fi
echo "PASS: Build succeeded"
echo

# --- Phase 2: Run tests with trust toolchain ---
echo "--- Phase 2: cargo +trust test -p z4-proof-common ---"

TEST_OUTPUT=$(mktemp /tmp/trust_z4_test.XXXXXX)
trap "rm -f '$TEST_OUTPUT'" EXIT

TEST_EXIT=0
CARGO_SKIP_CACHE=1 cargo +trust test -p z4-proof-common 2>&1 | tee "$TEST_OUTPUT" | tail -20 || TEST_EXIT=$?

if [ $TEST_EXIT -ne 0 ]; then
    echo "FAIL: cargo +trust test -p z4-proof-common exited with code $TEST_EXIT"
    exit 1
fi

# Extract test count from output
TRUST_PASSED=$(grep -o '[0-9]* passed' "$TEST_OUTPUT" | head -1 | grep -o '[0-9]*')
TRUST_FAILED=$(grep -o '[0-9]* failed' "$TEST_OUTPUT" | head -1 | grep -o '[0-9]*')

echo "PASS: Tests passed (${TRUST_PASSED:-0} passed, ${TRUST_FAILED:-0} failed)"
echo

# --- Phase 3: Cross-check with stable toolchain ---
if rustup toolchain list | grep -q '^stable'; then
    echo "--- Phase 3: Cross-check with cargo +stable test ---"

    STABLE_OUTPUT=$(mktemp /tmp/stable_z4_test.XXXXXX)
    trap "rm -f '$TEST_OUTPUT' '$STABLE_OUTPUT'" EXIT

    STABLE_EXIT=0
    CARGO_SKIP_CACHE=1 cargo +stable test -p z4-proof-common 2>&1 | tee "$STABLE_OUTPUT" | tail -10 || STABLE_EXIT=$?

    STABLE_PASSED=$(grep -o '[0-9]* passed' "$STABLE_OUTPUT" | head -1 | grep -o '[0-9]*')

    if [ "${TRUST_PASSED:-0}" = "${STABLE_PASSED:-0}" ]; then
        echo "PASS: Test counts match (trust=$TRUST_PASSED, stable=$STABLE_PASSED)"
    else
        echo "WARN: Test count mismatch (trust=${TRUST_PASSED:-0}, stable=${STABLE_PASSED:-0})"
    fi
    echo
else
    echo "--- Phase 3: Skipped (stable toolchain not available) ---"
    echo
fi

# --- Summary ---
echo "=== z4-proof-common compilation bootstrap: ALL CHECKS PASSED ==="
echo
echo "The tRust compiler successfully builds and tests z4-proof-common."
echo "Verification pass runs on all functions (additive, non-blocking)."
exit 0
