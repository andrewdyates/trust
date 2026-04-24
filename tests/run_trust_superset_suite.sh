#!/bin/bash
# Trust-first release suite wrapper.
#
# Mode names intentionally use `trust-*`, not `rust-*`. The inherited upstream
# corpus is a compatibility baseline that the `trust` toolchain must pass.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
MODE="${1:-quick}"
STRICT="${TRUST_STRICT:-0}"

section() {
    echo
    echo "--- $1"
}

run() {
    echo
    echo ">>> $*"
    "$@"
}

run_no_unexpected_skip() {
    local log
    log="$(mktemp /tmp/trust-suite.XXXXXX.log)"
    echo
    echo ">>> $*"
    "$@" 2>&1 | tee "$log"
    local status=${PIPESTATUS[0]}
    if [ "$status" -ne 0 ]; then
        rm -f "$log"
        return "$status"
    fi
    if [ "$STRICT" = "1" ] && grep -Eq '(^|[[:space:]])SKIP(PING|PED)?:' "$log"; then
        echo "FAIL: strict trust suite saw an unexpected skip in: $*" >&2
        rm -f "$log"
        return 1
    fi
    rm -f "$log"
}

usage() {
    cat <<'USAGE'
Usage: tests/run_trust_superset_suite.sh [quick|trust-compat|trustc-native|trust-extra|release]

Modes:
  quick          Fast tRust crate/unit feedback only.
  trust-compat   Full inherited upstream compatibility corpus for the trust toolchain.
  trustc-native  Canonical trustc/native verification transport checks.
  trust-extra    tRust-only verification, backend, parallel, and lift/decompile checks.
  release        Strict replacement proof: trust-compat + trustc-native + trust-extra + install gates.

Set TRUST_STRICT=1 to fail on unexpected SKIP lines in wrapped e2e gates.
USAGE
}

echo "=== tRust Superset Test Suite ($MODE) ==="

case "$MODE" in
    quick)
        section "Fast trust crate feedback"
        run "$TRUST_ROOT/scripts/dev-test.sh" --lib
        run cargo test --manifest-path "$TRUST_ROOT/cargo-trust/Cargo.toml" --lib
        ;;
    trust-compat)
        section "Trust compatibility corpus"
        run ./x.py build --stage 2
        run ./x.py test --stage 2 --no-fail-fast
        run ./x.py test tidy
        ;;
    trustc-native)
        section "trustc native verification transport"
        run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_compiler_verify.sh"
        run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_cargo_trust_cli.sh"
        run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_cargo_trust_root_resolution.sh"
        ;;
    trust-extra)
        section "Verification corpus"
        run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_verify_suite.sh"
        section "LLVM2 explicit opt-in"
        run_no_unexpected_skip bash "$TRUST_ROOT/tests/e2e_llvm2_parity_gate.sh"
        section "Trust crate/library corpus"
        run "$TRUST_ROOT/scripts/dev-test.sh" --lib
        ;;
    release)
        section "Strict trust replacement proof"
        run env TRUST_STRICT=1 bash "$TRUST_ROOT/tests/run_trust_superset_suite.sh" trust-compat
        run env TRUST_STRICT=1 bash "$TRUST_ROOT/tests/run_trust_superset_suite.sh" trustc-native
        run env TRUST_STRICT=1 bash "$TRUST_ROOT/tests/run_trust_superset_suite.sh" trust-extra
        run bash "$TRUST_ROOT/tests/run_trust_robust_suite.sh" prepublish
        run bash "$TRUST_ROOT/tests/run_trust_robust_suite.sh" installed
        run bash "$TRUST_ROOT/tests/run_trust_robust_suite.sh" installed-default
        run bash "$TRUST_ROOT/tests/run_trust_robust_suite.sh" stage0-lineage
        run bash "$TRUST_ROOT/tests/report_trust_gate_status.sh"
        ;;
    -h|--help|help)
        usage
        exit 0
        ;;
    *)
        usage >&2
        exit 2
        ;;
esac

echo
echo "=== tRust Superset Test Suite ($MODE): PASS ==="
