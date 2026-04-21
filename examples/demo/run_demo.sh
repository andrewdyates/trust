#!/usr/bin/env bash
# examples/demo/run_demo.sh -- Automated tRust demo script.
#
# Walks through the six demo steps non-interactively:
#   1. Show buggy program
#   2. Verify buggy program (tRust catches bugs)
#   3. Show fixed program
#   4. Verify fixed program (tRust proves safety)
#   5. Self-verification (tRust on its own types crate)
#   6. Generate HTML proof report
#
# Usage:
#   ./examples/demo/run_demo.sh [--standalone]
#
# Options:
#   --standalone  Use source-level analysis (no stage1 rustc required)
#
# Author: Andrew Yates <andrew@andrewdyates.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0

set -euo pipefail

DEMO_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$DEMO_DIR/../.." && pwd)"
STANDALONE=""
REPORT_DIR="$DEMO_DIR/report"

for arg in "$@"; do
    case "$arg" in
        --standalone) STANDALONE="--standalone" ;;
        *) echo "Unknown option: $arg"; exit 1 ;;
    esac
done

# Color output helpers (no-op if not a terminal)
if [ -t 1 ]; then
    BOLD='\033[1m'
    GREEN='\033[0;32m'
    RED='\033[0;31m'
    CYAN='\033[0;36m'
    RESET='\033[0m'
else
    BOLD='' GREEN='' RED='' CYAN='' RESET=''
fi

banner() {
    echo ""
    echo -e "${BOLD}${CYAN}=== $1 ===${RESET}"
    echo ""
}

pause() {
    if [ -t 0 ]; then
        echo -e "${BOLD}Press Enter to continue...${RESET}"
        read -r
    fi
}

# ---------------------------------------------------------------------------
banner "tRust Demo: Catching Bugs and Proving Safety"
echo "This demo shows tRust catching a real bug, proving the fix safe,"
echo "verifying its own source code, and generating a proof report."
pause

# ---------------------------------------------------------------------------
banner "Step 1: The Buggy Program"
echo "File: examples/demo/buggy_binary_search.rs"
echo ""
echo "A textbook binary search with two classic integer overflow bugs:"
echo "  - arr.len() - 1 underflows on empty arrays"
echo "  - (low + high) / 2 overflows for large indices"
echo ""
echo "Source:"
echo "--------"
cat "$DEMO_DIR/buggy_binary_search.rs"
echo "--------"
pause

# ---------------------------------------------------------------------------
banner "Step 2: tRust Catches the Bugs"
echo "Running: cargo trust check examples/demo/buggy_binary_search.rs $STANDALONE"
echo ""

cd "$REPO_ROOT"
# Allow failure -- the buggy program SHOULD fail verification.
set +e
cargo trust check examples/demo/buggy_binary_search.rs $STANDALONE 2>&1
BUGGY_EXIT=$?
set -e

echo ""
if [ "$BUGGY_EXIT" -ne 0 ]; then
    echo -e "${RED}Verification FAILED (exit $BUGGY_EXIT) -- bugs detected!${RESET}"
else
    echo -e "${GREEN}Verification passed (exit 0)${RESET}"
fi
pause

# ---------------------------------------------------------------------------
banner "Step 3: The Fixed Program"
echo "File: examples/demo/safe_binary_search.rs"
echo ""
echo "Three fixes applied:"
echo "  1. Empty-array guard before arr.len() - 1"
echo "  2. Safe midpoint: low + (high - low) / 2"
echo "  3. Checked subtraction: mid.checked_sub(1)"
echo ""
echo "Source:"
echo "--------"
cat "$DEMO_DIR/safe_binary_search.rs"
echo "--------"
pause

# ---------------------------------------------------------------------------
banner "Step 4: tRust Proves It Safe"
echo "Running: cargo trust check examples/demo/safe_binary_search.rs $STANDALONE"
echo ""

set +e
cargo trust check examples/demo/safe_binary_search.rs $STANDALONE 2>&1
SAFE_EXIT=$?
set -e

echo ""
if [ "$SAFE_EXIT" -eq 0 ]; then
    echo -e "${GREEN}Verification PASSED (exit 0) -- all obligations proved!${RESET}"
else
    echo -e "${RED}Verification FAILED (exit $SAFE_EXIT)${RESET}"
fi
pause

# ---------------------------------------------------------------------------
banner "Step 5: Self-Verification"
echo "tRust verifying its own trust-types crate (core type definitions)."
echo ""
echo "Running: cargo trust check --standalone -p trust-types"
echo ""

set +e
cargo trust check --standalone -p trust-types 2>&1
SELF_EXIT=$?
set -e

echo ""
if [ "$SELF_EXIT" -eq 0 ]; then
    echo -e "${GREEN}Self-verification PASSED!${RESET}"
else
    echo -e "${RED}Self-verification reported issues (exit $SELF_EXIT)${RESET}"
fi
pause

# ---------------------------------------------------------------------------
banner "Step 6: Proof Report"
echo "Generating HTML proof report for the safe binary search."
echo ""
echo "Running: cargo trust check examples/demo/safe_binary_search.rs \\"
echo "             --report-dir examples/demo/report $STANDALONE"
echo ""

mkdir -p "$REPORT_DIR"
set +e
cargo trust check examples/demo/safe_binary_search.rs \
    --report-dir examples/demo/report $STANDALONE 2>&1
REPORT_EXIT=$?
set -e

echo ""
if [ -f "$REPORT_DIR/report.html" ]; then
    echo -e "${GREEN}Report generated:${RESET}"
    echo "  $REPORT_DIR/report.json    (machine-readable)"
    echo "  $REPORT_DIR/report.html    (visual dashboard)"
    echo "  $REPORT_DIR/report.ndjson  (streaming/CI format)"
    echo ""
    # Open in browser if on macOS
    if command -v open >/dev/null 2>&1; then
        echo "Opening report.html in browser..."
        open "$REPORT_DIR/report.html"
    fi
else
    echo "Report files not generated (report-dir feature may require stage1 rustc)."
fi

# ---------------------------------------------------------------------------
banner "Demo Complete"
echo "Summary:"
echo "  Step 2 (buggy):   exit $BUGGY_EXIT (expected: non-zero = bugs found)"
echo "  Step 4 (safe):    exit $SAFE_EXIT (expected: 0 = all proved)"
echo "  Step 5 (self):    exit $SELF_EXIT"
echo "  Step 6 (report):  exit $REPORT_EXIT"
echo ""
echo "Learn more:"
echo "  VISION.md                  -- design document"
echo "  examples/                  -- more verification examples"
echo "  cargo trust help           -- all subcommands"
echo ""
