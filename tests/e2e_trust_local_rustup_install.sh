#!/bin/bash
# End-to-end test: rehearse the installed-toolchain gate from local `x dist`
# outputs by serving `build` as a temporary rustup dist server.
#
# This is a pre-publish rehearsal. It exercises rustup manifest/profile
# installation using local artifacts without mutating the user's real
# rustup home.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "=== tRust E2E Test: local rustup install rehearsal ==="
echo

fail_setup() {
    echo "ERROR: $1" >&2
    exit 2
}

fail_test() {
    echo "FAIL: $1" >&2
    exit 1
}

require_command() {
    local cmd="$1"
    local install_hint="$2"
    if ! command -v "$cmd" >/dev/null 2>&1; then
        fail_setup "$cmd not found on PATH. $install_hint"
    fi
}

sha256_cmd() {
    if command -v sha256sum >/dev/null 2>&1; then
        echo "sha256sum"
        return
    fi
    if command -v shasum >/dev/null 2>&1; then
        echo "shasum -a 256"
        return
    fi
    fail_setup "neither sha256sum nor shasum is available"
}

require_command rustup "Install rustup first."
require_command rustc "Install Rust first."
require_command python3 "Install Python 3 first."

DIST_DIR="$TRUST_ROOT/build/dist"
SERVER_ROOT="$TRUST_ROOT/build"
MANIFEST="$DIST_DIR/channel-rust-nightly.toml"
MANIFEST_SHA="$DIST_DIR/channel-rust-nightly.toml.sha256"
TMP_RUSTUP_HOME="$(mktemp -d /tmp/trust-rustup-home.XXXXXX)"
SERVER_PID=""
RUSTUP_BIN_DIR="$(dirname "$(command -v rustup)")"

cleanup() {
    if [ -n "$SERVER_PID" ]; then
        kill "$SERVER_PID" >/dev/null 2>&1 || true
    fi
    rm -rf "$TMP_RUSTUP_HOME"
}
trap cleanup EXIT

if [ ! -d "$DIST_DIR" ]; then
    fail_setup "build/dist not found. Run ./x dist first."
fi
if [ ! -f "$MANIFEST" ]; then
    fail_setup "channel manifest not found at $MANIFEST. Run ./x dist first."
fi

SHA256="$(sha256_cmd)"
(
    cd "$DIST_DIR"
    $SHA256 channel-rust-nightly.toml > "$MANIFEST_SHA"
)

PORT="$(python3 - <<'PY'
import socket

sock = socket.socket()
sock.bind(("127.0.0.1", 0))
print(sock.getsockname()[1])
sock.close()
PY
)"

(
    cd "$SERVER_ROOT"
    python3 -m http.server "$PORT" >/dev/null 2>&1
) &
SERVER_PID=$!
sleep 1

export RUSTUP_HOME="$TMP_RUSTUP_HOME"
export PATH="$RUSTUP_BIN_DIR:$PATH"

RUSTUP_DIST_SERVER="http://127.0.0.1:$PORT" \
    rustup toolchain install nightly --profile default

INSTALLED_NIGHTLY_SYSROOT="$(
    RUSTUP_DIST_SERVER="http://127.0.0.1:$PORT" \
        rustup run nightly rustc --print sysroot
)"

rustup toolchain link trust "$INSTALLED_NIGHTLY_SYSROOT"

INSTALLED_CARGO_TRUST="$(rustup which --toolchain trust cargo-trust 2>/dev/null || true)"
if [ -z "$INSTALLED_CARGO_TRUST" ]; then
    fail_setup "temporary trust toolchain is missing installed \`cargo-trust\`"
fi
if [ ! -x "$INSTALLED_CARGO_TRUST" ]; then
    fail_setup "temporary trust toolchain \`cargo-trust\` is not executable: $INSTALLED_CARGO_TRUST"
fi
case "$INSTALLED_CARGO_TRUST" in
    "$INSTALLED_NIGHTLY_SYSROOT"/bin/*) ;;
    *)
        fail_setup "temporary trust toolchain resolved \`cargo-trust\` outside the installed sysroot: $INSTALLED_CARGO_TRUST"
        ;;
esac

if ! rustup run trust cargo trust --help >/dev/null 2>&1; then
    fail_setup "temporary trust toolchain does not expose \`cargo trust\` through \`rustup run trust cargo trust\`"
fi

TMP_CHECK_DIR="$(mktemp -d /tmp/trust-local-rustup-check.XXXXXX)"
DOCTOR_JSON="$TMP_CHECK_DIR/doctor.json"
cleanup_check_dir() {
    rm -rf "$TMP_CHECK_DIR"
}
trap 'cleanup_check_dir; cleanup' EXIT

if ! (
    cd "$TMP_CHECK_DIR"
    rustup run trust cargo trust doctor --format json > "$DOCTOR_JSON"
); then
    fail_test "\`rustup run trust cargo trust doctor --format json\` failed"
fi

python3 - "$DOCTOR_JSON" <<'PY' || fail_test "doctor json did not report native installed-toolchain mode"
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

compiler = report["compiler"]
assert compiler["trust_verify"] is True, "native trust-verify is not available"
assert compiler["json_transport"] is True, "native JSON transport is not available"
assert compiler["check_report_mode"] == "native_compiler", "check/report is not using native mode"
PY

echo "Dist dir:          $DIST_DIR"
echo "Temporary home:    $RUSTUP_HOME"
echo "Installed sysroot: $INSTALLED_NIGHTLY_SYSROOT"
echo "Installed cargo-trust: $INSTALLED_CARGO_TRUST"
echo "Dist server:       http://127.0.0.1:$PORT"
echo

TRUST_ALLOW_DEFAULT_MUTATION=1 \
    RUSTUP_HOME="$RUSTUP_HOME" \
    bash "$TRUST_ROOT/tests/e2e_trust_installed_toolchain.sh" --set-default

echo
echo "=== local rustup install rehearsal: PASS ==="
