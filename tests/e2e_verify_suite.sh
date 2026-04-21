#!/bin/bash
# E2E Verification Suite Runner
#
# Runs all examples/verify_*.rs programs through the tRust verification
# pipeline and checks that each produces its expected result.
#
# Buggy variants (no _safe suffix): asserts the expected VcKind appears
# with FAILED status in verification output.
#
# Safe variants (_safe suffix): asserts the target VcKind is absent or
# has PROVED status.
#
# Usage:
#   ./tests/e2e_verify_suite.sh              # run all
#   ./tests/e2e_verify_suite.sh verify_div_zero  # run one (substring match)
#
# Prerequisites:
#   Stage1 rustc build (./x.py build) for full verification.
#   Falls back to cargo check (syntax only) if stage1 is unavailable.
#
# Author: Andrew Yates <andrew@andrewdyates.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
EXAMPLES_DIR="$TRUST_ROOT/examples"
FILTER="${1:-}"

# Counters
TOTAL=0
PASSED=0
FAILED=0
SKIPPED=0
ERRORS=""

# --- Colors (if terminal supports them) ---
if [ -t 1 ]; then
    GREEN='\033[0;32m'
    RED='\033[0;31m'
    YELLOW='\033[0;33m'
    BOLD='\033[1m'
    RESET='\033[0m'
else
    GREEN=''
    RED=''
    YELLOW=''
    BOLD=''
    RESET=''
fi

# --- Locate stage1 rustc ---
find_rustc() {
    local candidates=(
        "$TRUST_ROOT/build/host/stage1/bin/rustc"
        "$TRUST_ROOT/build/aarch64-apple-darwin/stage1/bin/rustc"
        "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage1/bin/rustc"
        "$TRUST_ROOT/build/x86_64-apple-darwin/stage1/bin/rustc"
    )
    for candidate in "${candidates[@]}"; do
        if [ -x "$candidate" ]; then
            echo "$candidate"
            return 0
        fi
    done
    return 1
}

# --- Parse expected patterns from file header ---
# Reads "// Expected: ..." lines and extracts VcKind names + FAILED status.
# Returns a newline-separated list of grep patterns.
parse_expected_patterns() {
    local file="$1"
    local expected_line
    expected_line=$(grep '^// Expected:' "$file" | head -1)
    if [ -z "$expected_line" ]; then
        echo ""
        return
    fi

    # Strip prefix "// Expected: "
    local body="${expected_line#// Expected: }"

    # Split on comma/AND separators, extract VcKind names
    # Each token looks like "VcKindName FAILED" or "VcKindName(Op) FAILED"
    echo "$body" | tr ',' '\n' | sed 's/ AND /\n/g' | while IFS= read -r token; do
        # Trim whitespace
        token=$(echo "$token" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')
        # Skip empty
        [ -z "$token" ] && continue
        # Extract the VcKind name (everything before FAILED, trimmed)
        local vc_name
        vc_name=$(echo "$token" | sed 's/[[:space:]]*FAILED.*//;s/[[:space:]]*$//')
        [ -z "$vc_name" ] && continue
        # Some names have parenthesized ops like ArithmeticOverflow(Sub)
        # We need to escape parens for grep
        echo "$vc_name"
    done
}

# --- Determine if file is a safe variant ---
is_safe_variant() {
    local basename
    basename=$(basename "$1" .rs)
    case "$basename" in
        *_safe) return 0 ;;
        *) return 1 ;;
    esac
}

# --- Clear TRUST_DISABLE_* environment variables ---
unset_trust_disables() {
    local var
    for var in $(env | grep '^TRUST_DISABLE_' | cut -d= -f1); do
        unset "$var"
    done
}

# --- Run a single test ---
run_test() {
    local file="$1"
    local rustc="$2"
    local mode="$3"  # "rustc" or "cargo-check"
    local basename
    basename=$(basename "$file" .rs)

    TOTAL=$((TOTAL + 1))
    echo -e "${BOLD}[$TOTAL] $basename${RESET}"

    # Parse expected patterns
    local patterns
    patterns=$(parse_expected_patterns "$file")

    if [ -z "$patterns" ]; then
        echo -e "  ${YELLOW}SKIP${RESET}: No '// Expected:' header found"
        SKIPPED=$((SKIPPED + 1))
        return
    fi

    # Clear any TRUST_DISABLE_* variables
    unset_trust_disables

    local output=""
    local exit_code=0
    local stderr_file
    stderr_file=$(mktemp /tmp/trust_e2e_XXXXXX)

    if [ "$mode" = "rustc" ]; then
        # Full verification via stage1 rustc
        local output_file
        output_file=$(mktemp /tmp/trust_e2e_out_XXXXXX)
        TRUST_VERIFY=1 "$rustc" -Z trust-verify --edition 2021 "$file" \
            -o "$output_file" 2>"$stderr_file" || exit_code=$?
        output=$(cat "$stderr_file")
        rm -f "$output_file"
    else
        # Fallback: system rustc syntax check (no verification output)
        local output_file
        output_file=$(mktemp /tmp/trust_e2e_out_XXXXXX)
        rustc --edition 2021 "$file" -o "$output_file" 2>"$stderr_file" || exit_code=$?
        output=$(cat "$stderr_file")
        rm -f "$output_file"
    fi
    rm -f "$stderr_file"

    # For syntax-only mode, we can only verify compilation
    if [ "$mode" = "syntax-check" ]; then
        if [ $exit_code -eq 0 ]; then
            echo -e "  ${YELLOW}SKIP${RESET}: compiles OK (no verification without stage1 rustc)"
            SKIPPED=$((SKIPPED + 1))
        else
            echo -e "  ${RED}FAIL${RESET}: compilation failed (exit $exit_code)"
            FAILED=$((FAILED + 1))
            ERRORS="${ERRORS}\n  $basename: compilation failed"
        fi
        return
    fi

    # --- Check verification results ---
    local test_passed=true

    if is_safe_variant "$file"; then
        # Safe variant: each VcKind should be absent or PROVED
        while IFS= read -r vc_name; do
            [ -z "$vc_name" ] && continue
            # Escape parens for grep
            local pattern
            pattern=$(echo "$vc_name" | sed 's/(/\\(/g;s/)/\\)/g')
            if echo "$output" | grep -q "${pattern}.*FAILED"; then
                echo -e "  ${RED}FAIL${RESET}: $vc_name should not be FAILED in safe variant"
                test_passed=false
            elif echo "$output" | grep -q "${pattern}.*PROVED"; then
                echo -e "  ${GREEN}OK${RESET}: $vc_name PROVED"
            else
                echo -e "  ${GREEN}OK${RESET}: $vc_name absent (expected for safe variant)"
            fi
        done <<< "$patterns"
    else
        # Buggy variant: each VcKind should appear with FAILED status
        while IFS= read -r vc_name; do
            [ -z "$vc_name" ] && continue
            # Escape parens for grep
            local pattern
            pattern=$(echo "$vc_name" | sed 's/(/\\(/g;s/)/\\)/g')
            # Check for FAILED (or RUNTIME-CHECKED, which also indicates detection)
            if echo "$output" | grep -qi "${pattern}.*FAILED\|${pattern}.*RUNTIME-CHECKED"; then
                echo -e "  ${GREEN}OK${RESET}: $vc_name FAILED (bug detected)"
            else
                echo -e "  ${RED}FAIL${RESET}: Expected $vc_name FAILED but not found"
                test_passed=false
            fi
        done <<< "$patterns"
    fi

    if $test_passed; then
        PASSED=$((PASSED + 1))
    else
        FAILED=$((FAILED + 1))
        ERRORS="${ERRORS}\n  $basename: verification output mismatch"
    fi
}

# ============================================================
# Main
# ============================================================

echo "=============================================="
echo "  tRust E2E Verification Suite"
echo "=============================================="
echo

# Detect verification mode
RUSTC=""
MODE="syntax-check"

if RUSTC=$(find_rustc); then
    MODE="rustc"
    echo "Mode:    stage1 rustc (full verification)"
    echo "Rustc:   $RUSTC"
else
    MODE="syntax-check"
    echo "Mode:    system rustc (syntax check only, no verification)"
    echo "         Build stage1 for full verification: cd $TRUST_ROOT && ./x.py build"
fi

echo "Root:    $TRUST_ROOT"
echo "Filter:  ${FILTER:-<all>}"
echo

# Collect test files
FILES=()
for f in "$EXAMPLES_DIR"/verify_*.rs; do
    [ -f "$f" ] || continue
    if [ -n "$FILTER" ]; then
        basename=$(basename "$f" .rs)
        case "$basename" in
            *"$FILTER"*) ;;
            *) continue ;;
        esac
    fi
    FILES+=("$f")
done

if [ ${#FILES[@]} -eq 0 ]; then
    echo "No matching examples/verify_*.rs files found."
    if [ -n "$FILTER" ]; then
        echo "Filter '$FILTER' matched nothing."
    fi
    exit 2
fi

echo "Found ${#FILES[@]} test file(s)"
echo "----------------------------------------------"
echo

# Run tests
START_TIME=$(date +%s)

for file in "${FILES[@]}"; do
    run_test "$file" "$RUSTC" "$MODE"
    echo
done

END_TIME=$(date +%s)
ELAPSED=$((END_TIME - START_TIME))

# --- Summary ---
echo "=============================================="
echo "  Summary"
echo "=============================================="
echo
echo "  Total:   $TOTAL"
echo -e "  Passed:  ${GREEN}$PASSED${RESET}"
echo -e "  Failed:  ${RED}$FAILED${RESET}"
echo -e "  Skipped: ${YELLOW}$SKIPPED${RESET}"
echo "  Time:    ${ELAPSED}s"

if [ $FAILED -gt 0 ]; then
    echo
    echo -e "${RED}FAILURES:${RESET}"
    echo -e "$ERRORS"
    echo
    exit 1
fi

if [ $PASSED -eq 0 ] && [ $SKIPPED -gt 0 ]; then
    echo
    echo -e "${YELLOW}WARNING: All tests skipped (no stage1 rustc available)${RESET}"
    echo "Build stage1 with: cd $TRUST_ROOT && ./x.py build"
    echo
    exit 0
fi

echo
echo -e "${GREEN}All tests passed.${RESET}"
exit 0
