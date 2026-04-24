#!/bin/bash
# End-to-end test: installed `cargo trust` is the canonical human-facing
# verification CLI for the linked `trust` toolchain release baseline.
#
# Verifies the supported public commands:
#   1. `cargo trust check`: human-readable summary, no raw TRUST_JSON leakage
#   2. `cargo trust check --format json`: canonical JSON report on stdout
#   3. default config is meaningful out of the box (L1, not "no obligations")
#   4. native verification comes from the linked rustup toolchain `trust`,
#      not from standalone fallback or repo-local developer shortcuts
#
# This intentionally tests the installed subcommand from a repo-external temp
# directory with compiler/toolchain override env cleared. It is still a
# linked/local baseline, not a packaged install/dist test.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
INPUT="$TRUST_ROOT/examples/midpoint.rs"

echo "=== tRust E2E Test: cargo trust public CLI ==="
echo

fail_setup() {
    echo "ERROR: $1"
    exit 2
}

run_public_cli() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS \
        -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        -u CARGO_BUILD_RUSTC_WRAPPER -u CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER \
        "$CARGO_BIN" trust "$@"
}

require_command() {
    local cmd="$1"
    local install_hint="$2"
    if ! command -v "$cmd" >/dev/null 2>&1; then
        fail_setup "$cmd not found on PATH. $install_hint"
    fi
}

require_command cargo "Install Rust/Cargo first."
require_command rustup "Install rustup and link the local toolchain as \`trust\`."
require_command python3 "Install Python 3 for JSON validation."

CARGO_BIN="$(command -v cargo)"
if ! LINKED_RUSTC="$(rustup which --toolchain trust rustc 2>/dev/null)"; then
    fail_setup "linked trust toolchain not found. Run: rustup toolchain link trust /abs/path/to/build/.../stage1-or-stage2"
fi
if [ ! -x "$LINKED_RUSTC" ]; then
    fail_setup "linked trust rustc is not executable: $LINKED_RUSTC"
fi

if ! run_public_cli --help >/dev/null 2>&1; then
    fail_setup "cargo trust is not installed on PATH. Run: cargo install --path cargo-trust --force"
fi

echo "Using cargo:        $CARGO_BIN"
echo "Linked trust rustc: $LINKED_RUSTC"
echo "Input file:         $INPUT"
echo

TMP_DIR="$(mktemp -d /tmp/cargo_trust_cli_XXXXXX)"
trap 'rm -rf "$TMP_DIR"' EXIT

TERMINAL_STDOUT="$TMP_DIR/terminal.stdout"
TERMINAL_STDERR="$TMP_DIR/terminal.stderr"
DOCTOR_STDOUT="$TMP_DIR/doctor.stdout"
DOCTOR_STDERR="$TMP_DIR/doctor.stderr"
JSON_STDOUT="$TMP_DIR/json.stdout"
JSON_STDERR="$TMP_DIR/json.stderr"

cd "$TMP_DIR"

if ! run_public_cli --help >/dev/null 2>&1; then
    echo "FAIL: installed cargo trust is not runnable from a repo-external temp dir"
    exit 1
fi

echo "--- doctor json"
doctor_exit=0
run_public_cli doctor --format json >"$DOCTOR_STDOUT" 2>"$DOCTOR_STDERR" || doctor_exit=$?

if [ "$doctor_exit" -ne 0 ]; then
    if [ "$doctor_exit" -gt 1 ]; then
        echo "FAIL: doctor json exited with unexpected status $doctor_exit"
        exit 1
    fi
fi
if grep -q "TRUST_JSON:" "$DOCTOR_STDOUT" "$DOCTOR_STDERR"; then
    echo "FAIL: doctor json leaked raw TRUST_JSON transport"
    exit 1
fi

doctor_parse_exit=0
LINKED_RUSTC="$LINKED_RUSTC" python3 - "$DOCTOR_STDOUT" <<'PY' || doctor_parse_exit=$?
import json
import os
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

compiler = report.get("compiler")
if not isinstance(compiler, dict):
    raise AssertionError("missing compiler object")

required_fields = [
    "path",
    "discovery_source",
    "linked_toolchain_status",
    "linked_toolchain_path",
    "trust_verify",
    "json_transport",
    "check_report_mode",
]
missing = [field for field in required_fields if field not in compiler]
if missing:
    raise AssertionError("missing compiler fields: " + ", ".join(missing))

if compiler["linked_toolchain_status"] != "visible":
    print(
        "SETUP: doctor does not see linked rustup toolchain `trust`: "
        + str(compiler["linked_toolchain_status"]),
        file=sys.stderr,
    )
    sys.exit(2)

linked = compiler["linked_toolchain_path"]
expected = os.environ["LINKED_RUSTC"]
if not linked or os.path.realpath(linked) != os.path.realpath(expected):
    print(
        f"SETUP: doctor linked rustc mismatch: expected {expected}, got {linked}",
        file=sys.stderr,
    )
    sys.exit(2)

if compiler["discovery_source"] != "rustup_toolchain_trust":
    raise AssertionError(
        "doctor selected "
        + str(compiler["discovery_source"])
        + " instead of linked rustup toolchain `trust`"
    )

if compiler["trust_verify"] is not True:
    print("SETUP: linked trust rustc lacks -Z trust-verify", file=sys.stderr)
    sys.exit(2)

if compiler["json_transport"] is not True:
    print("SETUP: linked trust rustc lacks -Z trust-verify-output=json", file=sys.stderr)
    sys.exit(2)

if compiler["check_report_mode"] != "native_compiler":
    print(
        "SETUP: doctor reports check/report mode "
        + str(compiler["check_report_mode"])
        + " instead of native_compiler",
        file=sys.stderr,
    )
    sys.exit(2)

solvers = report.get("solvers")
if not isinstance(solvers, dict):
    raise AssertionError("missing solvers object")
if solvers.get("available", 0) < 1:
    print("SETUP: doctor reports no available solver", file=sys.stderr)
    sys.exit(2)

if report.get("ready") is not True:
    print(
        "SETUP: doctor reports status " + str(report.get("status")) + " instead of ready",
        file=sys.stderr,
    )
    sys.exit(2)
PY
if [ "$doctor_parse_exit" -ne 0 ]; then
    if [ "$doctor_parse_exit" -eq 2 ]; then
        fail_setup "cargo trust doctor --format json reports native verification is not available"
    fi
    echo "FAIL: doctor json did not expose required native-vs-fallback diagnostics"
    echo "--- doctor stdout"
    cat "$DOCTOR_STDOUT"
    echo "--- doctor stderr"
    cat "$DOCTOR_STDERR"
    exit 1
fi
echo "  PASS: doctor json exposes linked native compiler mode and discovery diagnostics"

echo "--- command surface"
HELP_STDOUT="$TMP_DIR/help.stdout"
SOLVERS_STDOUT="$TMP_DIR/solvers.stdout"
REPORT_STDOUT="$TMP_DIR/report.stdout"
DIFF_STDOUT="$TMP_DIR/diff.stdout"
INIT_STDOUT="$TMP_DIR/init.stdout"
BUILD_STDERR="$TMP_DIR/build.stderr"
LOOP_STDERR="$TMP_DIR/loop.stderr"
SURFACE_INPUT="$TMP_DIR/surface_midpoint.rs"
INIT_INPUT="$TMP_DIR/init_sample.rs"
BUILD_INPUT="$TMP_DIR/build_ok.rs"
BASELINE_JSON="$TMP_DIR/baseline.json"
CURRENT_JSON="$TMP_DIR/current.json"

cp "$INPUT" "$SURFACE_INPUT"
cat > "$INIT_INPUT" <<'RUST'
pub fn increment(x: i32) -> i32 {
    x + 1
}
RUST
cat > "$BUILD_INPUT" <<'RUST'
fn main() {
    println!("build-ok");
}
RUST
cat > "$BASELINE_JSON" <<'JSON'
{"results":[{"kind":"overflow","message":"surface","outcome":"Failed","backend":"trust","time_ms":1}]}
JSON
cat > "$CURRENT_JSON" <<'JSON'
{"results":[{"kind":"overflow","message":"surface","outcome":"Proved","backend":"trust","time_ms":1}]}
JSON

run_public_cli help >"$HELP_STDOUT" 2>"$TMP_DIR/help.stderr"
for subcommand in check build report loop diff init solvers doctor help; do
    if ! grep -q "cargo trust $subcommand" "$HELP_STDOUT"; then
        echo "FAIL: help output is missing subcommand surface: $subcommand"
        exit 1
    fi
done

run_public_cli solvers --format json >"$SOLVERS_STDOUT" 2>"$TMP_DIR/solvers.stderr"
python3 - "$SOLVERS_STDOUT" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)
solvers = report.get("solvers")
if not isinstance(solvers, list) or not solvers:
    raise AssertionError("expected non-empty solver list")
if report.get("total") != len(solvers):
    raise AssertionError("solver total does not match solver list length")
if not isinstance(report.get("available"), int):
    raise AssertionError("solver report is missing available count")
PY

run_public_cli report --standalone --format json "$SURFACE_INPUT" >"$REPORT_STDOUT" 2>"$TMP_DIR/report.stderr"
python3 - "$REPORT_STDOUT" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)
if report.get("mode") != "standalone":
    raise AssertionError("standalone report did not identify standalone mode")
for field in ("functions_found", "total_vcs", "proved", "failed", "unknown", "functions", "vcs"):
    if field not in report:
        raise AssertionError(f"standalone report is missing {field}")
if not isinstance(report["functions"], list) or not report["functions"]:
    raise AssertionError("standalone report did not include analyzed functions")
PY

run_public_cli diff --baseline "$BASELINE_JSON" --current "$CURRENT_JSON" --format json >"$DIFF_STDOUT" 2>"$TMP_DIR/diff.stderr"
python3 - "$DIFF_STDOUT" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)
if report.get("improvements", 0) < 1:
    raise AssertionError("diff output did not report the expected improvement")
PY

run_public_cli init "$INIT_INPUT" >"$INIT_STDOUT" 2>"$TMP_DIR/init.stderr"
if ! grep -q "increment" "$INIT_STDOUT"; then
    echo "FAIL: init output did not mention the target function"
    exit 1
fi

build_exit=0
BUILD_OUTPUT_UNIX="${BUILD_INPUT%.rs}"
BUILD_OUTPUT_EXE="${BUILD_OUTPUT_UNIX}.exe"
rm -f "$BUILD_OUTPUT_UNIX" "$BUILD_OUTPUT_EXE"
run_public_cli build "$BUILD_INPUT" >"$TMP_DIR/build.stdout" 2>"$BUILD_STDERR" || build_exit=$?
if [ "$build_exit" -ne 0 ] \
    || ! grep -q "using native compiler" "$BUILD_STDERR" \
    || { [ ! -x "$BUILD_OUTPUT_UNIX" ] && [ ! -x "$BUILD_OUTPUT_EXE" ]; }; then
    echo "FAIL: build command did not exercise native cargo-trust surface"
    cat "$BUILD_STDERR"
    exit 1
fi

loop_exit=0
run_public_cli loop --max-iterations 1 "$SURFACE_INPUT" >"$TMP_DIR/loop.stdout" 2>"$LOOP_STDERR" || loop_exit=$?
if [ "$loop_exit" -gt 1 ] || ! grep -q "starting rewrite loop" "$LOOP_STDERR"; then
    echo "FAIL: loop command did not exercise native cargo-trust surface"
    cat "$LOOP_STDERR"
    exit 1
fi
echo "  PASS: public subcommand surface is present and runnable"

echo "--- terminal mode"
terminal_exit=0
run_public_cli check "$INPUT" >"$TERMINAL_STDOUT" 2>"$TERMINAL_STDERR" || terminal_exit=$?

if [ "$terminal_exit" -gt 1 ]; then
    echo "FAIL: terminal mode exited with unexpected status $terminal_exit"
    exit 1
fi

terminal_output="$(cat "$TERMINAL_STDERR")"
if echo "$terminal_output" | grep -q "falling back to standalone source analysis"; then
    echo "FAIL: terminal mode fell back to standalone analysis"
    exit 1
fi
if ! echo "$terminal_output" | grep -q 'linked rustup toolchain `trust`'; then
    echo "FAIL: terminal mode did not use the linked trust toolchain"
    exit 1
fi
if ! echo "$terminal_output" | grep -q "=== tRust Verification Report ==="; then
    echo "FAIL: terminal mode did not render the human report"
    exit 1
fi
if ! echo "$terminal_output" | grep -q "Level: L1"; then
    echo "FAIL: terminal mode did not use the default L1 configuration"
    exit 1
fi
if echo "$terminal_output" | grep -q "No verification obligations found"; then
    echo "FAIL: terminal mode defaulted to an empty verification run"
    exit 1
fi
if ! echo "$terminal_output" | grep -q "get_midpoint"; then
    echo "FAIL: terminal mode did not report the target function"
    exit 1
fi
if ! echo "$terminal_output" | grep -Eq "\\[(PROVED|FAILED|RUNTIME-CHECKED|TIMEOUT)\\]"; then
    echo "FAIL: terminal mode did not report any verification outcome"
    exit 1
fi
if ! echo "$terminal_output" | grep -q "Result:"; then
    echo "FAIL: terminal mode did not render a final result line"
    exit 1
fi
if grep -q "TRUST_JSON:" "$TERMINAL_STDOUT" "$TERMINAL_STDERR"; then
    echo "FAIL: terminal mode leaked raw TRUST_JSON transport"
    exit 1
fi
echo "  PASS: terminal mode renders a meaningful human summary without raw transport"

echo "--- json mode"
json_exit=0
run_public_cli check --format json "$INPUT" >"$JSON_STDOUT" 2>"$JSON_STDERR" || json_exit=$?

if [ "$json_exit" -gt 1 ]; then
    echo "FAIL: json mode exited with unexpected status $json_exit"
    exit 1
fi

python3 - "$JSON_STDOUT" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

assert "summary" in report, "missing summary"
assert "functions" in report, "missing functions"
assert report["summary"]["total_obligations"] >= 1, "expected at least one obligation"
assert report["functions"], "expected at least one function result"
assert any(
    str(fn.get("function", "")).split("::")[-1] == "get_midpoint"
    for fn in report["functions"]
), "missing get_midpoint"
PY

json_stderr="$(cat "$JSON_STDERR")"
if echo "$json_stderr" | grep -q "falling back to standalone source analysis"; then
    echo "FAIL: json mode fell back to standalone analysis"
    exit 1
fi
if ! echo "$json_stderr" | grep -q "using native compiler"; then
    echo "FAIL: json mode did not use a native compiler"
    exit 1
fi
if ! echo "$json_stderr" | grep -q 'linked rustup toolchain `trust`'; then
    echo "FAIL: json mode did not use the linked trust toolchain"
    exit 1
fi
if grep -q "TRUST_JSON:" "$JSON_STDOUT" "$JSON_STDERR"; then
    echo "FAIL: json mode leaked raw TRUST_JSON transport"
    exit 1
fi
echo "  PASS: json mode emits canonical JSON report"

echo
echo "=== cargo trust public CLI test: PASS ==="
