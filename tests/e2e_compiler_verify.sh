#!/bin/bash
# End-to-end test: built trustc with trust_verify MIR pass emits verification transport
#
# Tests that the compiler-integrated verification pipeline (trust_verify.rs)
# is wired into the built compiler and emits machine-readable verification
# transport for real Rust code when `-Z trust-verify-output=json` is set.
#
# This tests the native trustc path (MIR pass).
#
# Author: Andrew Yates <andrew@andrewdyates.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
INPUT="$TRUST_ROOT/examples/midpoint.rs"

echo "=== tRust E2E Test: compiler-integrated verification ==="
echo

# --- Locate built trustc ---
# Prefer stage2 because plain `./x.py build` is configured to produce it.
TRUSTC_BIN=""

runtime_library_path_var() {
    case "$(uname -s)" in
        Darwin) echo "DYLD_LIBRARY_PATH" ;;
        Linux) echo "LD_LIBRARY_PATH" ;;
        *) echo "" ;;
    esac
}

runtime_library_path_for_trustc() {
    local trustc="$1"
    local bin_dir sysroot stage_name build_dir deps_root rustlib_root
    local -a paths=()

    bin_dir="$(cd "$(dirname "$trustc")" && pwd -P)"
    sysroot="$(cd "$bin_dir/.." && pwd -P)"
    stage_name="$(basename "$sysroot")"
    build_dir="$(dirname "$sysroot")"
    deps_root="$build_dir/${stage_name}-rustc"
    rustlib_root="$sysroot/lib/rustlib"

    [ -d "$sysroot/lib" ] && paths+=("$sysroot/lib")

    for libdir in "$rustlib_root"/*/lib; do
        [ -d "$libdir" ] && paths+=("$libdir")
    done

    for depsdir in "$deps_root"/*/release/deps; do
        [ -d "$depsdir" ] && paths+=("$depsdir")
    done

    local joined=""
    local path
    for path in "${paths[@]}"; do
        if [ -z "$joined" ]; then
            joined="$path"
        else
            joined="$joined:$path"
        fi
    done

    printf '%s' "$joined"
}

run_trustc_with_runtime_env() {
    local trustc="$1"
    shift

    local path_var
    local path_value
    local existing=""

    path_var="$(runtime_library_path_var)"
    path_value="$(runtime_library_path_for_trustc "$trustc")"

    if [ -n "$path_var" ] && [ -n "$path_value" ]; then
        existing="${!path_var:-}"
        if [ -n "$existing" ]; then
            env "$path_var=$path_value:$existing" TRUST_VERIFY=1 "$trustc" "$@"
        else
            env "$path_var=$path_value" TRUST_VERIFY=1 "$trustc" "$@"
        fi
    else
        TRUST_VERIFY=1 "$trustc" "$@"
    fi
}

supports_trust_verify() {
    local trustc="$1"
    local metadata_out
    metadata_out=$(mktemp /tmp/trust_verify_probe.XXXXXX)
    printf 'pub fn trust_verify_probe(a: usize, b: usize) -> usize { (a + b) / 2 }\n' | \
        run_trustc_with_runtime_env "$trustc" -Z trust-verify --edition 2021 --crate-name trust_verify_probe \
            --crate-type lib --emit metadata -o "$metadata_out" - >/dev/null 2>&1
    local rc=$?
    rm -f "$metadata_out"
    return $rc
}

supports_json_output() {
    local trustc="$1"
    local metadata_out
    local stderr_file
    metadata_out=$(mktemp /tmp/trust_verify_probe_json.XXXXXX)
    stderr_file=$(mktemp /tmp/trust_verify_probe_stderr.XXXXXX)
    printf 'pub fn trust_verify_probe(a: usize, b: usize) -> usize { (a + b) / 2 }\n' | \
        run_trustc_with_runtime_env "$trustc" -Z trust-verify -Z trust-verify-output=json \
            --edition 2021 --crate-name trust_verify_probe --crate-type lib --emit metadata \
            -o "$metadata_out" - 2>"$stderr_file" >/dev/null
    local rc=$?
    if [ $rc -eq 0 ] && grep -q 'TRUST_JSON:' "$stderr_file"; then
        rm -f "$metadata_out" "$stderr_file"
        return 0
    fi
    rm -f "$metadata_out" "$stderr_file"
    return 1
}

if [ -n "${TRUSTC:-}" ] && [ -x "${TRUSTC}" ]; then
    if supports_trust_verify "${TRUSTC}"; then
        TRUSTC_BIN="${TRUSTC}"
    else
        echo "WARN: TRUSTC is set but does not provide a usable native verification path: ${TRUSTC}"
    fi
fi

CANDIDATES=(
    "$TRUST_ROOT/build/host/stage2/bin/trustc"
    "$TRUST_ROOT/build/host/stage1/bin/trustc"
    "$TRUST_ROOT/build/aarch64-apple-darwin/stage2/bin/trustc"
    "$TRUST_ROOT/build/aarch64-apple-darwin/stage1/bin/trustc"
    "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage2/bin/trustc"
    "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage1/bin/trustc"
    "$TRUST_ROOT/build/x86_64-apple-darwin/stage2/bin/trustc"
    "$TRUST_ROOT/build/x86_64-apple-darwin/stage1/bin/trustc"
    "$TRUST_ROOT/build/host/stage2/bin/rustc"
    "$TRUST_ROOT/build/host/stage1/bin/rustc"
    "$TRUST_ROOT/build/aarch64-apple-darwin/stage2/bin/rustc"
    "$TRUST_ROOT/build/aarch64-apple-darwin/stage1/bin/rustc"
    "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage2/bin/rustc"
    "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage1/bin/rustc"
    "$TRUST_ROOT/build/x86_64-apple-darwin/stage2/bin/rustc"
    "$TRUST_ROOT/build/x86_64-apple-darwin/stage1/bin/rustc"
)

if [ -z "$TRUSTC_BIN" ]; then
    for candidate in "${CANDIDATES[@]}"; do
        if [ -x "$candidate" ] && supports_trust_verify "$candidate"; then
            TRUSTC_BIN="$candidate"
            break
        fi
    done
fi

if [ -z "$TRUSTC_BIN" ]; then
    echo "ERROR: built trustc with a usable native verification path not found."
    echo
    echo "Checked paths:"
    for candidate in "${CANDIDATES[@]}"; do
        if [ -x "$candidate" ]; then
            if supports_trust_verify "$candidate"; then
                echo "  $candidate (usable native verification path)"
            else
                echo "  $candidate (native verification unavailable)"
            fi
        else
            echo "  $candidate (not found)"
        fi
    done
    echo
    echo "Build it with:"
    echo "  cd $TRUST_ROOT && ./x.py build"
    echo
    echo "This builds the full compiler with the trust_verify MIR pass."
    exit 2
fi

echo "Using trustc: $TRUSTC_BIN"
echo "Input file:  $INPUT"
echo

if ! supports_trust_verify "$TRUSTC_BIN"; then
    echo "ERROR: selected trustc does not provide a usable native verification path"
    exit 2
fi

SUPPORTS_JSON_OUTPUT=0
if supports_json_output "$TRUSTC_BIN"; then
    SUPPORTS_JSON_OUTPUT=1
fi

# --- Verify input file exists ---
if [ ! -f "$INPUT" ]; then
    echo "ERROR: Test input not found: $INPUT"
    exit 2
fi

# --- Run compilation with JSON transport enabled ---
# The trust_verify pass writes verification output to stderr. We capture it
# separately from stdout. The compilation itself should succeed (exit 0)
# because verification is additive -- it does not block compilation.
if [ "$SUPPORTS_JSON_OUTPUT" -eq 1 ]; then
    CMD=(
        "$TRUSTC_BIN" -Z trust-verify -Z trust-verify-output=json --edition 2021 "$INPUT"
    )
    echo "Running: TRUST_VERIFY=1 $TRUSTC_BIN -Z trust-verify -Z trust-verify-output=json --edition 2021 $INPUT"
else
    CMD=("$TRUSTC_BIN" -Z trust-verify --edition 2021 "$INPUT")
    echo "Running: TRUST_VERIFY=1 $TRUSTC_BIN -Z trust-verify --edition 2021 $INPUT"
    echo "Note: selected trustc does not provide live JSON transport on the native path; falling back to note-based verification checks."
fi
echo

STDERR_FILE=$(mktemp /tmp/trust_verify_stderr.XXXXXX)
OUTPUT_FILE=$(mktemp /tmp/trust_verify_output.XXXXXX)
trap "rm -f '$STDERR_FILE' '$OUTPUT_FILE'" EXIT

COMPILE_EXIT=0
if [ "$SUPPORTS_JSON_OUTPUT" -eq 1 ]; then
    run_trustc_with_runtime_env "$TRUSTC_BIN" -Z trust-verify -Z trust-verify-output=json --edition 2021 "$INPUT" -o "$OUTPUT_FILE" 2>"$STDERR_FILE" || COMPILE_EXIT=$?
else
    run_trustc_with_runtime_env "$TRUSTC_BIN" -Z trust-verify --edition 2021 "$INPUT" -o "$OUTPUT_FILE" 2>"$STDERR_FILE" || COMPILE_EXIT=$?
fi

OUTPUT=$(cat "$STDERR_FILE")

echo "--- stderr output ---"
echo "$OUTPUT"
echo "--- end stderr ---"
echo

# --- Check compilation succeeded ---
if [ $COMPILE_EXIT -ne 0 ]; then
    echo "FAILED: trustc exited with code $COMPILE_EXIT"
    exit 1
fi

# --- Verify expected transport contract ---
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

if [ "$SUPPORTS_JSON_OUTPUT" -eq 1 ]; then
    # 1. Machine-readable transport lines are emitted
    check "TRUST_JSON:" "Transport: TRUST_JSON lines emitted"

    # 2. main function is reported
    check '"function":"main"' "Transport: main function reported"

    # 3. get_midpoint function is reported
    check '"function":"get_midpoint"' "Transport: get_midpoint function reported"

    # 4. Summary counters are present
    check '"proved":[0-9]' "Transport: proved counter present"
    check '"failed":[0-9]' "Transport: failed counter present"
    check '"unknown":[0-9]' "Transport: unknown counter present"
    check '"runtime_checked":[0-9]' "Transport: runtime_checked counter present"
    check '"total":[0-9]' "Transport: total counter present"
else
    # Older stage1 compilers still emit human-readable verification notes.
    check "=== tRust Verification Report" "Report header emitted"
    check "tRust \\[" "Verification note emitted"
    check "PROVED\\|FAILED\\|UNKNOWN\\|TIMEOUT\\|RUNTIME-CHECKED" "Verification outcome emitted"
fi

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

check_absent "divzero" "No division-by-zero false positive on midpoint / 2"

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
