#!/usr/bin/env bash
# examples/demo/run_demo.sh -- Scripted walkthrough for the deeper tRust demo.
#
# This is not the canonical first-run path. For initial setup and the current
# public contract, start with:
#   README.md
#   docs/install.md
#   docs/USING_TRUST.md
#   cargo-trust/README.md
#
# Walks through the six demo steps non-interactively:
#   1. Show buggy program
#   2. Verify buggy program (tRust catches bugs)
#   3. Show fixed program
#   4. Re-check fixed program (current proof-frontier example)
#   5. Standalone self-analysis (tRust on its own types crate)
#   6. Attempt proof report generation
#
# Usage:
#   ./examples/demo/run_demo.sh [--standalone] [--help]
#
# Author: Andrew Yates <andrew@andrewdyates.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0

set -euo pipefail

DEMO_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$DEMO_DIR/../.." && pwd)"
STANDALONE=""
REPORT_DIR="$DEMO_DIR/report"

usage() {
    cat <<'EOF'
Usage:
  ./examples/demo/run_demo.sh [--standalone] [--help]

This is a scripted walkthrough of examples/demo/, not the primary onboarding
or install flow.

Current first-run/docs path:
  README.md
  docs/install.md
  docs/USING_TRUST.md
  cargo-trust/README.md

Current public verifier surface:
  cargo trust check
  cargo trust check --format json

Options:
  --standalone  Force source analysis instead of compiler-backed verification.
                Useful without a discoverable tRust compiler; report artifacts
                may be limited or absent in this mode.
  --help        Show this help.
EOF
}

for arg in "$@"; do
    case "$arg" in
        --standalone) STANDALONE="--standalone" ;;
        -h|--help) usage; exit 0 ;;
        *)
            echo "Unknown option: $arg" >&2
            echo "" >&2
            usage >&2
            exit 1
            ;;
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
banner "tRust Demo: Catching Bugs and Tracking Proof Progress"
echo "This is a deeper repo-local demo, not the canonical first-run path."
echo "For install/setup and the current product contract, start with:"
echo "  README.md"
echo "  docs/install.md"
echo "  docs/USING_TRUST.md"
echo "  cargo-trust/README.md"
echo ""
echo "Current public verifier surface:"
echo "  cargo trust check"
echo "  cargo trust check --format json"
echo ""
echo "This walkthrough then shows tRust catching a real bug, re-checking a"
echo "fixed source against the current prover frontier, running standalone"
echo "self-analysis on one of its own crates, and attempting report generation."
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
banner "Step 4: tRust Re-checks the Fixed Program"
echo "Running: cargo trust check examples/demo/safe_binary_search.rs $STANDALONE"
echo ""

set +e
cargo trust check examples/demo/safe_binary_search.rs $STANDALONE 2>&1
SAFE_EXIT=$?
set -e

echo ""
if [ "$SAFE_EXIT" -eq 0 ]; then
    echo -e "${GREEN}Verification PASSED (exit 0)${RESET}"
else
    echo -e "${RED}Fixed example still has open obligations on the current toolchain (exit $SAFE_EXIT).${RESET}"
fi
pause

# ---------------------------------------------------------------------------
banner "Step 5: Standalone Self-Analysis"
echo "tRust analyzing its own trust-types crate (core type definitions)."
echo "This is a deeper self-hosting smoke test of the public standalone workflow,"
echo "not the main first-run install check."
echo ""
echo "Running: cargo trust check --standalone -p trust-types"
echo ""

set +e
cargo trust check --standalone -p trust-types 2>&1
SELF_EXIT=$?
set -e

echo ""
if [ "$SELF_EXIT" -eq 0 ]; then
    echo -e "${GREEN}Standalone self-analysis PASSED!${RESET}"
else
    echo -e "${RED}Standalone self-analysis reported issues (exit $SELF_EXIT)${RESET}"
fi
pause

# ---------------------------------------------------------------------------
banner "Step 6: Proof Report"
echo "Attempting proof report generation for the safe binary search."
if [ -n "$STANDALONE" ]; then
    echo "Note: --standalone forces source analysis. The checked docs treat"
    echo "report artifacts as part of the compiler-backed workflow, so missing"
    echo "HTML/JSON outputs are expected in this mode."
else
    echo "Note: report artifacts are part of the compiler-backed workflow."
fi
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
    if [ -n "$STANDALONE" ]; then
        echo "Report files were not generated. That can be expected in standalone"
        echo "mode; rerun without --standalone after following docs/install.md if"
        echo "you want the compiler-backed report artifacts."
    else
        echo "Report files were not generated. Check compiler discovery and the"
        echo "supported install flow in docs/install.md."
    fi
fi

# ---------------------------------------------------------------------------
banner "Demo Complete"
echo "Summary:"
echo "  Step 2 (buggy):   exit $BUGGY_EXIT (expected: non-zero = bugs found)"
echo "  Step 4 (fixed):   exit $SAFE_EXIT (current frontier example)"
echo "  Step 5 (self):    exit $SELF_EXIT"
echo "  Step 6 (report):  exit $REPORT_EXIT"
echo ""
echo "Next references:"
echo "  README.md                  -- product overview and first-run entrypoint"
echo "  docs/install.md            -- supported from-source install flow"
echo "  docs/USING_TRUST.md        -- current product boundaries/status"
echo "  cargo-trust/README.md      -- canonical cargo trust usage"
echo "  examples/demo/README.md    -- manual walkthrough for this demo"
echo "  VISION.md                  -- strategic architecture background"
echo ""
