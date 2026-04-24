#!/bin/bash
# End-to-end test: a rustup-installed `trust` toolchain exposes `cargo trust`
# without repo-local/manual `cargo-trust` installation.
#
# This is intentionally separate from the current linked/local launch
# approximation. It is the installed-toolchain proof gate for the eventual
# fresh-machine switch contract.

set -euo pipefail

SET_DEFAULT=0
if [ "${1:-}" = "--set-default" ]; then
    SET_DEFAULT=1
    shift
fi
if [ "$#" -ne 0 ]; then
    fail_setup() {
        echo "ERROR: $1" >&2
        exit 2
    }
    fail_setup "usage: $0 [--set-default]"
fi

echo "=== tRust E2E Test: installed trust toolchain ==="
echo

fail_setup() {
    echo "ERROR: $1" >&2
    exit 2
}

fail_test() {
    echo "FAIL: $1" >&2
    exit 1
}

run_default_surface_trust_cargo() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFMT -u CLIPPY_DRIVER -u MIRI \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        RUSTUP_TOOLCHAIN=trust \
        cargo trust "$@"
}

run_mutated_default_trust_cargo() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFMT -u CLIPPY_DRIVER -u MIRI \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        cargo trust "$@"
}

run_installed_cargo() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFMT -u CLIPPY_DRIVER -u MIRI \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        rustup run trust cargo "$@"
}

run_default_surface_cargo() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFMT -u CLIPPY_DRIVER -u MIRI \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        RUSTUP_TOOLCHAIN=trust \
        cargo "$@"
}

run_mutated_default_cargo() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFMT -u CLIPPY_DRIVER -u MIRI \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        cargo "$@"
}

run_mutated_default_rustc() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFMT -u CLIPPY_DRIVER -u MIRI \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        rustc "$@"
}

run_mutated_default_rustdoc() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFMT -u CLIPPY_DRIVER -u MIRI \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        rustdoc "$@"
}

require_command() {
    local cmd="$1"
    local install_hint="$2"
    if ! command -v "$cmd" >/dev/null 2>&1; then
        fail_setup "$cmd not found on PATH. $install_hint"
    fi
}

rustup_which_tool() {
    rustup which --toolchain trust "$1" 2>/dev/null
}

optional_tool() {
    local tool="$1"
    rustup_which_tool "$tool" || true
}

require_tool() {
    local tool="$1"
    local path
    if ! path="$(rustup_which_tool "$tool")"; then
        fail_setup "installed trust toolchain is missing required tool \`$tool\`. Install the default-profile \`trust\` toolchain first."
    fi
    if [ ! -x "$path" ]; then
        fail_setup "installed trust tool \`$tool\` is not executable: $path"
    fi
    printf '%s\n' "$path"
}

require_one_tool() {
    local label="$1"
    shift
    local tool path
    for tool in "$@"; do
        path="$(optional_tool "$tool")"
        if [ -n "$path" ]; then
            if [ ! -x "$path" ]; then
                fail_setup "installed trust $label tool \`$tool\` is not executable: $path"
            fi
            printf '%s\n' "$path"
            return 0
        fi
    done
    fail_setup "installed trust toolchain is missing required $label surface: expected one of \`$*\`."
}

require_directory() {
    if [ ! -d "$1" ]; then
        fail_setup "$2: $1"
    fi
}

require_executable_path() {
    if [ ! -x "$1" ]; then
        fail_setup "$2: $1"
    fi
}

run_smoke_step() {
    local label="$1"
    shift
    if ! "$@"; then
        fail_test "$label failed through the installed trust toolchain"
    fi
}

require_command cargo "Install Rust/Cargo first."
require_command rustup "Install rustup first."
require_command python3 "Install Python 3 first."

INSTALLED_CARGO_TRUST="$(require_tool cargo-trust)"
INSTALLED_RUSTC="$(require_tool rustc)"
INSTALLED_CARGO="$(require_tool cargo)"
INSTALLED_RUSTDOC="$(require_tool rustdoc)"
INSTALLED_RUST_ANALYZER="$(require_tool rust-analyzer)"
INSTALLED_FMT="$(require_one_tool "formatting" cargo-fmt rustfmt)"
INSTALLED_CLIPPY="$(require_one_tool "linting" cargo-clippy clippy-driver)"
INSTALLED_CARGO_FMT="$(optional_tool cargo-fmt)"
INSTALLED_RUSTFMT="$(optional_tool rustfmt)"
INSTALLED_CARGO_CLIPPY="$(optional_tool cargo-clippy)"
INSTALLED_CLIPPY_DRIVER="$(optional_tool clippy-driver)"
INSTALLED_CARGO_MIRI="$(optional_tool cargo-miri)"
INSTALLED_MIRI="$(optional_tool miri)"

INSTALLED_SYSROOT="$(rustup run trust rustc --print sysroot 2>/dev/null || true)"
if [ -z "$INSTALLED_SYSROOT" ]; then
    fail_setup "rustup could not run \`trust\` toolchain rustc"
fi
if ! HOST_INFO="$(rustup run trust rustc -vV 2>/dev/null)"; then
    fail_setup "rustup could not run \`trust\` toolchain rustc -vV"
fi
HOST_TRIPLE="$(printf '%s\n' "$HOST_INFO" | awk '/^host: / { print $2 }')"
if [ -z "$HOST_TRIPLE" ]; then
    fail_setup "could not determine host triple from installed trust rustc -vV"
fi
case "$INSTALLED_CARGO_TRUST" in
    "$INSTALLED_SYSROOT"/bin/*) ;;
    *)
        fail_setup "installed cargo-trust is not under the trust sysroot bin directory: $INSTALLED_CARGO_TRUST"
        ;;
esac

for installed_tool in \
    "$INSTALLED_RUSTC" \
    "$INSTALLED_CARGO" \
    "$INSTALLED_RUSTDOC" \
    "$INSTALLED_RUST_ANALYZER" \
    "$INSTALLED_FMT" \
    "$INSTALLED_CLIPPY"
do
    case "$installed_tool" in
        "$INSTALLED_SYSROOT"/bin/*) ;;
        *)
            fail_setup "installed tool is not under the trust sysroot bin directory: $installed_tool"
            ;;
    esac
done

if [ -n "$INSTALLED_CARGO_MIRI$INSTALLED_MIRI" ]; then
    if [ -z "$INSTALLED_CARGO_MIRI" ] || [ -z "$INSTALLED_MIRI" ]; then
        fail_setup "installed trust miri surface is incomplete: cargo-miri=$INSTALLED_CARGO_MIRI miri=$INSTALLED_MIRI"
    fi
    case "$INSTALLED_CARGO_MIRI" in
        "$INSTALLED_SYSROOT"/bin/*) ;;
        *) fail_setup "installed cargo-miri is not under the trust sysroot bin directory: $INSTALLED_CARGO_MIRI" ;;
    esac
    case "$INSTALLED_MIRI" in
        "$INSTALLED_SYSROOT"/bin/*) ;;
        *) fail_setup "installed miri is not under the trust sysroot bin directory: $INSTALLED_MIRI" ;;
    esac
fi

if [ -d "$INSTALLED_SYSROOT/lib/rustlib/src/rust" ]; then
    INSTALLED_RUST_SRC="$INSTALLED_SYSROOT/lib/rustlib/src/rust"
elif [ -d "$INSTALLED_SYSROOT/lib/rustlib/rustc-src/rust" ]; then
    INSTALLED_RUST_SRC="$INSTALLED_SYSROOT/lib/rustlib/rustc-src/rust"
else
    fail_setup "installed trust toolchain is missing rust-src evidence under $INSTALLED_SYSROOT/lib/rustlib/{src,rustc-src}/rust"
fi

LLVM_TOOLS_DIR="$INSTALLED_SYSROOT/lib/rustlib/$HOST_TRIPLE/bin"
require_directory "$LLVM_TOOLS_DIR" "installed trust toolchain is missing llvm-tools host bin directory"
for llvm_tool in llvm-ar llvm-nm llvm-objdump llvm-profdata; do
    require_executable_path "$LLVM_TOOLS_DIR/$llvm_tool" "installed trust toolchain is missing required llvm-tools executable"
done

if ! rustup run trust cargo trust --help >/dev/null 2>&1; then
    fail_setup "installed toolchain does not expose \`cargo trust\` through \`rustup run trust cargo trust\`"
fi
if ! run_default_surface_trust_cargo --help >/dev/null 2>&1; then
    fail_setup "installed toolchain does not expose \`cargo trust\` through the default-surface cargo shim"
fi
if ! run_default_surface_cargo --version >/dev/null 2>&1; then
    fail_setup "installed toolchain does not expose default-surface \`cargo\` with RUSTUP_TOOLCHAIN=trust"
fi

TMP_DIR="$(mktemp -d /tmp/cargo_trust_installed_toolchain_XXXXXX)"
trap 'rm -rf "$TMP_DIR"' EXIT

INPUT="$TMP_DIR/midpoint.rs"
CRATE_DIR="$TMP_DIR/smoke"
DOCTOR_JSON="$TMP_DIR/doctor.json"
CHECK_STDOUT="$TMP_DIR/check.stdout"
CHECK_STDERR="$TMP_DIR/check.stderr"
JSON_STDOUT="$TMP_DIR/report.json"
JSON_STDERR="$TMP_DIR/json.stderr"

cat > "$INPUT" <<'RUST'
fn get_midpoint(a: i32, b: i32) -> i32 {
    a + (b - a) / 2
}

fn main() {
    assert_eq!(get_midpoint(2, 6), 4);
}
RUST

echo "Installed cargo-trust: $INSTALLED_CARGO_TRUST"
echo "Installed rustc:       $INSTALLED_RUSTC"
echo "Installed cargo:       $INSTALLED_CARGO"
echo "Installed rustdoc:     $INSTALLED_RUSTDOC"
echo "Installed rust-analyzer: $INSTALLED_RUST_ANALYZER"
echo "Installed rust-src:    $INSTALLED_RUST_SRC"
echo "Installed llvm-tools:  $LLVM_TOOLS_DIR"
echo "Installed fmt surface: $INSTALLED_FMT"
echo "Installed clippy surface: $INSTALLED_CLIPPY"
if [ -n "$INSTALLED_CARGO_MIRI" ]; then
    echo "Installed miri surface: $INSTALLED_CARGO_MIRI / $INSTALLED_MIRI"
else
    echo "Installed miri surface: not shipped in this profile"
fi
echo "Input file:            $INPUT"
echo

run_smoke_step "cargo new" run_installed_cargo new "$CRATE_DIR" --bin --quiet
cat > "$CRATE_DIR/src/main.rs" <<'RUST'
fn midpoint(a: i32, b: i32) -> i32 {
    a + (b - a) / 2
}

fn main() {
    assert_eq!(midpoint(2, 6), 4);
    println!("{}", midpoint(10, 14));
}

#[cfg(test)]
mod tests {
    use super::midpoint;

    #[test]
    fn computes_midpoint() {
        assert_eq!(midpoint(-2, 2), 0);
    }
}
RUST

(
    cd "$CRATE_DIR"
    run_smoke_step "cargo check" run_installed_cargo check --quiet
    run_smoke_step "default-surface cargo check" run_default_surface_cargo check --quiet
    run_smoke_step "cargo test" run_installed_cargo test --quiet
    run_smoke_step "cargo doc --no-deps" run_installed_cargo doc --no-deps --quiet

    if [ -n "$INSTALLED_CARGO_FMT" ]; then
        run_smoke_step "cargo fmt --check" run_installed_cargo fmt --check
    elif [ -n "$INSTALLED_RUSTFMT" ]; then
        run_smoke_step "rustfmt --check" "$INSTALLED_RUSTFMT" --check src/main.rs
    else
        fail_setup "installed trust formatting surface vanished after setup checks"
    fi

    if [ -n "$INSTALLED_CARGO_CLIPPY" ]; then
        run_smoke_step "cargo clippy" run_installed_cargo clippy --quiet -- -D warnings
    elif [ -n "$INSTALLED_CLIPPY_DRIVER" ]; then
        run_smoke_step "clippy-driver --version" "$INSTALLED_CLIPPY_DRIVER" --version
    else
        fail_setup "installed trust clippy surface vanished after setup checks"
    fi

    if [ -n "$INSTALLED_CARGO_MIRI" ]; then
        if run_installed_cargo miri --version >/dev/null 2>&1; then
            run_smoke_step "cargo miri test" run_installed_cargo miri test --quiet
        else
            echo "cargo miri smoke skipped: cargo-miri is installed but standalone dispatch is unavailable"
        fi
    fi
)

(
    cd "$TMP_DIR"
    run_default_surface_trust_cargo doctor --format json > "$DOCTOR_JSON"
)

python3 - "$DOCTOR_JSON" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

compiler = report["compiler"]
assert compiler["trust_verify"] is True, "native trust-verify is not available"
assert compiler["json_transport"] is True, "native JSON transport is not available"
assert compiler["check_report_mode"] == "native_compiler", "check/report is not using native mode"
assert compiler["discovery_source"] in {"sibling_cargo_trust", "rustup_toolchain_trust"}, "unexpected compiler discovery source"
PY

check_status=0
(
    cd "$TMP_DIR"
    run_default_surface_trust_cargo check "$INPUT" > "$CHECK_STDOUT" 2> "$CHECK_STDERR"
) || check_status=$?

if [ "$check_status" -gt 1 ]; then
    fail_test "installed toolchain terminal check exited with unexpected status $check_status"
fi

check_output="$(cat "$CHECK_STDERR")"
if ! echo "$check_output" | grep -q "using native compiler"; then
    fail_test "terminal mode did not use a native compiler"
fi
if echo "$check_output" | grep -q "falling back to standalone source analysis"; then
    fail_test "terminal mode fell back to standalone analysis"
fi
if echo "$check_output" | grep -q "TRUST_JSON:"; then
    fail_test "terminal mode leaked raw TRUST_JSON transport"
fi
if ! echo "$check_output" | grep -q "=== tRust Verification Report ==="; then
    fail_test "terminal mode did not render the human report"
fi
if ! echo "$check_output" | grep -q "get_midpoint"; then
    fail_test "terminal mode did not report the target function"
fi

json_status=0
(
    cd "$TMP_DIR"
    run_default_surface_trust_cargo check --format json "$INPUT" > "$JSON_STDOUT" 2> "$JSON_STDERR"
) || json_status=$?

if [ "$json_status" -gt 1 ]; then
    fail_test "installed toolchain json check exited with unexpected status $json_status"
fi

python3 - "$JSON_STDOUT" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

assert "summary" in report, "missing summary"
assert "functions" in report, "missing functions"
assert any(fn["function"] == "get_midpoint" for fn in report["functions"]), "missing get_midpoint"
PY

json_output="$(cat "$JSON_STDERR")"
if ! echo "$json_output" | grep -q "using native compiler"; then
    fail_test "json mode did not use a native compiler"
fi
if echo "$json_output" | grep -q "falling back to standalone source analysis"; then
    fail_test "json mode fell back to standalone analysis"
fi
if echo "$json_output" | grep -q "TRUST_JSON:"; then
    fail_test "json mode leaked raw TRUST_JSON transport"
fi

if [ "$SET_DEFAULT" -eq 1 ]; then
    if [ "${TRUST_ALLOW_DEFAULT_MUTATION:-0}" != "1" ]; then
        fail_setup "refusing to mutate rustup default without TRUST_ALLOW_DEFAULT_MUTATION=1"
    fi

    PREVIOUS_DEFAULT="$(rustup default 2>/dev/null | awk 'NR==1 { print $1 }')"
    if [ -z "$PREVIOUS_DEFAULT" ]; then
        fail_setup "could not determine the current rustup default toolchain"
    fi

    restore_default() {
        rustup default "$PREVIOUS_DEFAULT" >/dev/null 2>&1 || true
    }
    trap 'restore_default; rm -rf "$TMP_DIR"' EXIT

    rustup default trust >/dev/null

    DEFAULT_RUSTC_SYSROOT="$(run_mutated_default_rustc --print sysroot 2>/dev/null || true)"
    if [ "$DEFAULT_RUSTC_SYSROOT" != "$INSTALLED_SYSROOT" ]; then
        fail_test "plain rustc after rustup default trust resolved the wrong sysroot: $DEFAULT_RUSTC_SYSROOT"
    fi
    if ! run_mutated_default_rustdoc --version >/dev/null 2>&1; then
        fail_test "plain rustdoc did not work after rustup default trust"
    fi
    if ! run_mutated_default_trust_cargo --help >/dev/null 2>&1; then
        fail_test "cargo trust did not work after rustup default trust"
    fi
    if ! run_mutated_default_cargo check --manifest-path "$CRATE_DIR/Cargo.toml" --quiet >/dev/null 2>&1; then
        fail_test "cargo check did not work after rustup default trust"
    fi
    if ! run_mutated_default_cargo test --manifest-path "$CRATE_DIR/Cargo.toml" --quiet >/dev/null 2>&1; then
        fail_test "cargo test did not work after rustup default trust"
    fi
    if ! run_mutated_default_cargo doc --manifest-path "$CRATE_DIR/Cargo.toml" --no-deps --quiet >/dev/null 2>&1; then
        fail_test "cargo doc did not work after rustup default trust"
    fi
    if [ -n "$INSTALLED_CARGO_FMT" ]; then
        if ! (
            cd "$CRATE_DIR"
            run_mutated_default_cargo fmt --check
        ) >/dev/null 2>&1; then
            fail_test "cargo fmt did not work after rustup default trust"
        fi
    elif [ -n "$INSTALLED_RUSTFMT" ]; then
        if ! "$INSTALLED_RUSTFMT" --check "$CRATE_DIR/src/main.rs" >/dev/null 2>&1; then
            fail_test "rustfmt did not work from the installed trust sysroot"
        fi
    else
        fail_setup "installed trust formatting surface vanished before default-toolchain smoke"
    fi
    if [ -n "$INSTALLED_CARGO_CLIPPY" ]; then
        if ! run_mutated_default_cargo clippy --manifest-path "$CRATE_DIR/Cargo.toml" --quiet -- -D warnings >/dev/null 2>&1; then
            fail_test "cargo clippy did not work after rustup default trust"
        fi
    elif [ -n "$INSTALLED_CLIPPY_DRIVER" ]; then
        if ! "$INSTALLED_CLIPPY_DRIVER" --version >/dev/null 2>&1; then
            fail_test "clippy-driver did not work from the installed trust sysroot"
        fi
    else
        fail_setup "installed trust clippy surface vanished before default-toolchain smoke"
    fi
    if [ -n "$INSTALLED_CARGO_MIRI" ]; then
        if run_mutated_default_cargo miri --version >/dev/null 2>&1; then
            if ! (
                cd "$CRATE_DIR"
                run_mutated_default_cargo miri test --quiet
            ) >/dev/null 2>&1; then
                fail_test "cargo miri did not work after rustup default trust"
            fi
        else
            echo "cargo miri default smoke skipped: cargo-miri is installed but standalone dispatch is unavailable"
        fi
    fi

    DEFAULT_DOCTOR_JSON="$TMP_DIR/default-doctor.json"
    (
        cd "$TMP_DIR"
        run_mutated_default_trust_cargo doctor --format json > "$DEFAULT_DOCTOR_JSON"
    )

    python3 - "$DEFAULT_DOCTOR_JSON" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

compiler = report["compiler"]
assert compiler["trust_verify"] is True, "default-toolchain smoke lost native trust-verify"
assert compiler["check_report_mode"] == "native_compiler", "default-toolchain smoke is not native"
PY

    DEFAULT_CHECK_STDOUT="$TMP_DIR/default-check.stdout"
    DEFAULT_CHECK_STDERR="$TMP_DIR/default-check.stderr"
    default_check_status=0
    (
        cd "$TMP_DIR"
        run_mutated_default_trust_cargo check "$INPUT" > "$DEFAULT_CHECK_STDOUT" 2> "$DEFAULT_CHECK_STDERR"
    ) || default_check_status=$?

    if [ "$default_check_status" -gt 1 ]; then
        fail_test "cargo trust check did not work after rustup default trust"
    fi
    default_check_output="$(cat "$DEFAULT_CHECK_STDERR")"
    if ! echo "$default_check_output" | grep -q "using native compiler"; then
        fail_test "cargo trust check after rustup default trust did not use a native compiler"
    fi
    if echo "$default_check_output" | grep -q "falling back to standalone source analysis"; then
        fail_test "cargo trust check after rustup default trust fell back to standalone analysis"
    fi
fi

echo
echo "=== installed trust toolchain test: PASS ==="
