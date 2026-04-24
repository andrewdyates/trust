#!/bin/bash
# Robust test runner for tRust.
#
# Separates:
#   - baseline Rust parity
#   - the supported linked-toolchain + `cargo trust check` public contract
#   - the installed-toolchain proof gate
#   - the installed default/no-flags proof gate
#   - the pre-publish dist artifact rehearsal gate
#   - the bootstrap stage0 lineage proof gate
#   - the deeper native compiler transport gate
#
# A green smoke/full run should make it obvious whether a failure is in the
# linked toolchain, the public CLI, or the raw compiler integration.
# The `launch` mode is the current linked/local approximation of the eventual
# fresh-machine switch gate; it is not a packaged install/dist claim.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
MODE="${1:-smoke}"

run() {
    echo
    echo ">>> $*"
    "$@"
}

section() {
    echo
    echo "--- $1"
}

run_launch_gate() {
    section "Supported launch gate: linked trust toolchain"
    run bash "$TRUST_ROOT/tests/e2e_trust_toolchain.sh"
    section "Supported launch gate: cargo trust public CLI"
    run bash "$TRUST_ROOT/tests/e2e_cargo_trust_cli.sh"
    section "Supported launch gate: cargo trust root resolution"
    run bash "$TRUST_ROOT/tests/e2e_cargo_trust_root_resolution.sh"
    section "Explicit native compiler transport gate"
    run bash "$TRUST_ROOT/tests/e2e_compiler_verify.sh"
}

echo "=== tRust Robust Test Suite ($MODE) ==="

case "$MODE" in
    smoke)
        section "Baseline parity"
        run bash "$TRUST_ROOT/tests/e2e_semantic_parity.sh"
        run_launch_gate
        ;;
    launch)
        section "Current linked/local launch approximation"
        run_launch_gate
        ;;
    installed)
        section "Installed-toolchain proof gate"
        run bash "$TRUST_ROOT/tests/e2e_trust_installed_toolchain.sh"
        ;;
    installed-default)
        section "Installed default/no-flags proof gate"
        run env TRUST_ALLOW_DEFAULT_MUTATION=1 bash "$TRUST_ROOT/tests/e2e_trust_installed_toolchain.sh" --set-default
        ;;
    prepublish)
        section "Pre-publish dist artifact rehearsal"
        run bash "$TRUST_ROOT/tests/e2e_trust_dist_artifacts.sh"
        section "Pre-publish local rustup install rehearsal"
        run bash "$TRUST_ROOT/tests/e2e_trust_local_rustup_install.sh"
        ;;
    stage0-lineage)
        section "Bootstrap stage0 lineage proof gate"
        run bash "$TRUST_ROOT/tests/e2e_trust_stage0_lineage.sh"
        ;;
    parity)
        section "Baseline parity"
        run bash "$TRUST_ROOT/tests/e2e_semantic_parity.sh"
        run ./x.py test --stage 2 tests/ui tests/run-make tests/mir-opt tests/codegen tests/codegen-units tests/incremental tests/ui-fulldeps tests/rustdoc-ui
        ;;
    full)
        section "Baseline parity"
        run bash "$TRUST_ROOT/tests/e2e_semantic_parity.sh"
        run ./x.py test --stage 2 tests/ui tests/run-make tests/mir-opt tests/codegen tests/codegen-units tests/incremental tests/ui-fulldeps tests/rustdoc-ui
        run_launch_gate
        section "Verification regression corpus"
        run bash "$TRUST_ROOT/tests/e2e_verify_suite.sh"
        ;;
    *)
        echo "Usage: $0 [smoke|launch|installed|installed-default|prepublish|stage0-lineage|parity|full]"
        exit 2
        ;;
esac

echo
echo "=== tRust Robust Test Suite ($MODE): PASS ==="
