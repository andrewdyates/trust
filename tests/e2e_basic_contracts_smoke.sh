#!/bin/bash
# Smoke test: the basic contracts example crate type-checks independently and,
# when the public verifier CLI is installed, produces a JSON verification report.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CRATE_DIR="$TRUST_ROOT/examples/contracts/basic-contracts"

echo "=== tRust E2E Test: basic contracts proof corpus smoke ==="
echo

fail_setup() {
    echo "ERROR: $1"
    exit 2
}

fail_test() {
    echo "FAIL: $1"
    exit 1
}

resolve_cargo() {
    local cargo_bin
    cargo_bin="$(command -v cargo 2>/dev/null || true)"
    if [ -n "$cargo_bin" ]; then
        printf '%s\n' "$cargo_bin"
        return
    fi

    if [ -x "$HOME/.cargo/bin/cargo" ]; then
        printf '%s\n' "$HOME/.cargo/bin/cargo"
        return
    fi

    fail_setup "cargo not found on PATH or at \$HOME/.cargo/bin/cargo"
}

run_host_cargo() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS \
        -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        -u CARGO_BUILD_RUSTC_WRAPPER -u CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER \
        "$CARGO_BIN" "$@"
}

run_public_cli() {
    env -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS \
        -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        -u CARGO_BUILD_RUSTC_WRAPPER -u CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER \
        TRUSTC="${LINKED_RUSTC:-}" \
        "$CARGO_BIN" trust "$@"
}

if [ ! -f "$CRATE_DIR/Cargo.toml" ]; then
    fail_setup "example crate manifest not found: $CRATE_DIR/Cargo.toml"
fi

CARGO_BIN="$(resolve_cargo)"
TMP_DIR="$(mktemp -d /tmp/basic_contracts_smoke_XXXXXX)"
trap 'rm -rf "$TMP_DIR"' EXIT

echo "Using cargo: $CARGO_BIN"
echo "Crate:       $CRATE_DIR"
echo

echo "--- cargo check"
CHECK_STDOUT="$TMP_DIR/cargo_check.stdout"
CHECK_STDERR="$TMP_DIR/cargo_check.stderr"
check_exit=0
(
    cd "$CRATE_DIR"
    CARGO_TARGET_DIR="$TMP_DIR/target" run_host_cargo check --locked >"$CHECK_STDOUT" 2>"$CHECK_STDERR"
) || check_exit=$?

if [ "$check_exit" -ne 0 ]; then
    echo "FAIL: basic-contracts cargo check exited with status $check_exit"
    echo "--- cargo check stdout"
    cat "$CHECK_STDOUT"
    echo "--- cargo check stderr"
    cat "$CHECK_STDERR"
    exit 1
fi
echo "  PASS: basic-contracts cargo check succeeded"
echo

echo "--- cargo trust check --format json"
if ! command -v rustup >/dev/null 2>&1; then
    echo "SKIP: rustup not found on PATH; public cargo trust verification requires linked toolchain setup"
    exit 0
fi

if ! LINKED_RUSTC="$(rustup which --toolchain trust rustc 2>/dev/null)"; then
    echo "SKIP: linked rustup toolchain \`trust\` not found; cargo check already validated the example crate"
    exit 0
fi
if [ ! -x "$LINKED_RUSTC" ]; then
    echo "SKIP: linked trust rustc is not executable: $LINKED_RUSTC"
    exit 0
fi
if ! run_public_cli --help >/dev/null 2>&1; then
    echo "SKIP: cargo trust is not installed for $CARGO_BIN; run: cargo install --path cargo-trust --force"
    exit 0
fi

TRUST_JSON="$TMP_DIR/trust_check.json"
TRUST_STDERR="$TMP_DIR/trust_check.stderr"
trust_exit=0
(
    cd "$CRATE_DIR"
    CARGO_TARGET_DIR="$TMP_DIR/target" run_public_cli check --format json >"$TRUST_JSON" 2>"$TRUST_STDERR"
) || trust_exit=$?

if [ "$trust_exit" -gt 1 ]; then
    echo "FAIL: cargo trust check --format json exited with unexpected status $trust_exit"
    echo "--- cargo trust stderr"
    cat "$TRUST_STDERR"
    echo "--- cargo trust stdout"
    cat "$TRUST_JSON"
    exit 1
fi

if grep -q "TRUST_JSON:" "$TRUST_JSON" "$TRUST_STDERR"; then
    fail_test "cargo trust check leaked raw TRUST_JSON transport"
fi
if grep -q "falling back to standalone source analysis" "$TRUST_STDERR"; then
    echo "--- cargo trust stderr"
    cat "$TRUST_STDERR"
    fail_setup "linked trust toolchain is visible, but cargo trust fell back to standalone analysis"
fi
if ! grep -q "using native compiler" "$TRUST_STDERR"; then
    echo "--- cargo trust stderr"
    cat "$TRUST_STDERR"
    fail_setup "linked trust toolchain is visible, but cargo trust did not report native compiler verification"
fi

if ! command -v python3 >/dev/null 2>&1; then
    fail_setup "python3 not found on PATH; needed to validate cargo trust JSON output"
fi

if ! python3 - "$TRUST_JSON" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

functions = report.get("functions")
if not isinstance(functions, list) or not functions:
    raise AssertionError("expected at least one reported function")

names = {
    str(entry.get("function", "")).split("::")[-1]
    for entry in functions
    if isinstance(entry, dict)
}
expected = {"divide_exact", "abs_total", "get_at"}
missing = sorted(expected - names)
if missing:
    raise AssertionError("missing expected contract functions: " + ", ".join(missing))

summary = report.get("summary")
if not isinstance(summary, dict):
    raise AssertionError("missing summary object")
if summary.get("total_obligations", 0) < 1:
    raise AssertionError("expected at least one verification obligation")
PY
then
    echo "FAIL: cargo trust JSON report did not match the expected proof-corpus schema"
    echo "--- cargo trust stdout"
    cat "$TRUST_JSON"
    echo "--- cargo trust stderr"
    cat "$TRUST_STDERR"
    exit 1
fi

if [ "$trust_exit" -eq 1 ]; then
    fail_test "basic-contracts produced verification failures under cargo trust check --format json"
fi

echo "  PASS: cargo trust JSON report includes expected basic contract functions"
echo
echo "=== basic contracts proof corpus smoke: PASS ==="
