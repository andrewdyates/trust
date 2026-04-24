#!/bin/bash
# End-to-end test: `cargo trust` resolves config/cache roots from the intended
# crate or file target, not from the caller's shell cwd.
#
# This exercises the linked/local public CLI baseline through:
#   - crate-root invocation
#   - subdirectory invocation under a crate
#   - repo-external invocation with --manifest-path
#   - repo-external single-file invocation
#   - repo-external invocation against a non-root workspace member manifest

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "=== tRust E2E Test: cargo trust root resolution ==="
echo

fail_setup() {
    echo "ERROR: $1"
    exit 2
}

fail_test() {
    echo "FAIL: $1"
    exit 1
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

assert_terminal_report() {
    local stderr_file="$1"
    local expected_symbol="$2"
    local expected_level="$3"

    local output
    output="$(cat "$stderr_file")"

    if echo "$output" | grep -q "falling back to standalone source analysis"; then
        fail_setup "linked trust toolchain is visible, but cargo trust fell back to standalone analysis"
    fi
    if ! echo "$output" | grep -q "using native compiler"; then
        fail_setup "linked trust toolchain is visible, but cargo trust did not use a native compiler"
    fi
    if ! echo "$output" | grep -q "=== tRust Verification Report ==="; then
        fail_test "terminal mode did not render the human report"
    fi
    if ! echo "$output" | grep -q "Level: $expected_level"; then
        fail_test "terminal mode did not use the expected $expected_level configuration"
    fi
    if ! echo "$output" | grep -q "$expected_symbol"; then
        fail_test "terminal mode did not report the expected symbol $expected_symbol"
    fi
    if echo "$output" | grep -q "TRUST_JSON:"; then
        fail_test "terminal mode leaked raw TRUST_JSON transport"
    fi
}

run_check_case() {
    local workdir="$1"
    local stderr_file="$2"
    shift 2

    local stdout_file="${stderr_file%.stderr}.stdout"
    local exit_code=0
    (
        cd "$workdir"
        run_public_cli check "$@" >"$stdout_file" 2>"$stderr_file"
    ) || exit_code=$?

    if [ "$exit_code" -gt 1 ]; then
        fail_test "terminal mode exited with unexpected status $exit_code for args: $*"
    fi
}

require_command cargo "Install Rust/Cargo first."
require_command rustup "Install rustup and link the local toolchain as \`trust\`."

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

TMP_DIR="$(mktemp -d /tmp/cargo_trust_root_resolution_XXXXXX)"
trap 'rm -rf "$TMP_DIR"' EXIT

CRATE_DIR="$TMP_DIR/rooted-crate"
SUBDIR="$CRATE_DIR/src/nested/deeper"
UNRELATED_CWD="$TMP_DIR/unrelated"
SINGLE_DIR="$TMP_DIR/single-file"
WORKSPACE_DIR="$TMP_DIR/workspace"
MEMBER_DIR="$WORKSPACE_DIR/member-crate"

mkdir -p "$CRATE_DIR/src" "$SUBDIR" "$UNRELATED_CWD" "$SINGLE_DIR" "$MEMBER_DIR/src"

cat > "$CRATE_DIR/Cargo.toml" <<'TOML'
[package]
name = "rooted-crate"
version = "0.1.0"
edition = "2021"
TOML

cat > "$CRATE_DIR/trust.toml" <<'TOML'
level = "L2"
TOML

cat > "$CRATE_DIR/src/lib.rs" <<'RUST'
pub fn midpoint(a: i32, b: i32) -> i32 {
    a + (b - a) / 2
}

#[cfg(test)]
mod tests {
    use super::midpoint;

    #[test]
    fn computes_midpoint() {
        assert_eq!(midpoint(2, 6), 4);
    }
}
RUST

cat > "$SINGLE_DIR/trust.toml" <<'TOML'
level = "L2"
TOML

cat > "$SINGLE_DIR/demo.rs" <<'RUST'
pub fn demo_value(x: i32) -> i32 {
    x + 1
}

fn main() {
    println!("{}", demo_value(4));
}
RUST

cat > "$WORKSPACE_DIR/Cargo.toml" <<'TOML'
[workspace]
members = ["member-crate"]
resolver = "2"
TOML

cat > "$WORKSPACE_DIR/trust.toml" <<'TOML'
level = "L0"
TOML

cat > "$MEMBER_DIR/Cargo.toml" <<'TOML'
[package]
name = "member-crate"
version = "0.1.0"
edition = "2021"
TOML

cat > "$MEMBER_DIR/trust.toml" <<'TOML'
level = "L2"
TOML

cat > "$MEMBER_DIR/src/lib.rs" <<'RUST'
pub fn member_value(x: i32) -> i32 {
    x * 2
}

#[cfg(test)]
mod tests {
    use super::member_value;

    #[test]
    fn doubles_value() {
        assert_eq!(member_value(4), 8);
    }
}
RUST

echo "Using cargo:        $CARGO_BIN"
echo "Linked trust rustc: $LINKED_RUSTC"
echo

echo "--- crate root"
rm -rf "$CRATE_DIR/target"
ROOT_STDERR="$TMP_DIR/root.stderr"
run_check_case "$CRATE_DIR" "$ROOT_STDERR"
assert_terminal_report "$ROOT_STDERR" "midpoint" "L2"
if [ ! -f "$CRATE_DIR/target/trust-cache/verification.json" ]; then
    fail_test "crate-root invocation did not write cache under $CRATE_DIR/target/trust-cache"
fi

echo "--- crate subdirectory"
rm -rf "$CRATE_DIR/target" "$SUBDIR/target"
SUBDIR_STDERR="$TMP_DIR/subdir.stderr"
run_check_case "$SUBDIR" "$SUBDIR_STDERR"
assert_terminal_report "$SUBDIR_STDERR" "midpoint" "L2"
if [ ! -f "$CRATE_DIR/target/trust-cache/verification.json" ]; then
    fail_test "subdirectory invocation did not write cache under crate root"
fi
if [ -e "$SUBDIR/target/trust-cache/verification.json" ]; then
    fail_test "subdirectory invocation incorrectly wrote cache under the caller subdir"
fi

echo "--- unrelated cwd with --manifest-path"
rm -rf "$CRATE_DIR/target" "$UNRELATED_CWD/target"
MANIFEST_STDERR="$TMP_DIR/manifest.stderr"
run_check_case "$UNRELATED_CWD" "$MANIFEST_STDERR" --manifest-path "$CRATE_DIR/Cargo.toml"
assert_terminal_report "$MANIFEST_STDERR" "midpoint" "L2"
if [ ! -f "$CRATE_DIR/target/trust-cache/verification.json" ]; then
    fail_test "--manifest-path invocation did not write cache under crate root"
fi
if [ -e "$UNRELATED_CWD/target/trust-cache/verification.json" ]; then
    fail_test "--manifest-path invocation incorrectly wrote cache under unrelated cwd"
fi

echo "--- unrelated cwd single-file mode"
rm -rf "$SINGLE_DIR/target" "$UNRELATED_CWD/target"
SINGLE_STDERR="$TMP_DIR/single.stderr"
run_check_case "$UNRELATED_CWD" "$SINGLE_STDERR" "$SINGLE_DIR/demo.rs"
assert_terminal_report "$SINGLE_STDERR" "demo_value" "L2"
if [ ! -f "$SINGLE_DIR/target/trust-cache/verification.json" ]; then
    fail_test "single-file invocation did not write cache under the file parent"
fi
if [ -e "$UNRELATED_CWD/target/trust-cache/verification.json" ]; then
    fail_test "single-file invocation incorrectly wrote cache under unrelated cwd"
fi

echo "--- unrelated cwd with non-root workspace member --manifest-path"
rm -rf "$MEMBER_DIR/target" "$WORKSPACE_DIR/target" "$UNRELATED_CWD/target"
MEMBER_STDERR="$TMP_DIR/member.stderr"
run_check_case "$UNRELATED_CWD" "$MEMBER_STDERR" --manifest-path "$MEMBER_DIR/Cargo.toml"
assert_terminal_report "$MEMBER_STDERR" "member_value" "L2"
if [ ! -f "$MEMBER_DIR/target/trust-cache/verification.json" ]; then
    fail_test "workspace member invocation did not write cache under the member root"
fi
if [ -e "$WORKSPACE_DIR/target/trust-cache/verification.json" ]; then
    fail_test "workspace member invocation incorrectly wrote cargo-trust cache under the workspace root"
fi
if [ -e "$UNRELATED_CWD/target/trust-cache/verification.json" ]; then
    fail_test "workspace member invocation incorrectly wrote cache under unrelated cwd"
fi

echo
echo "=== cargo trust root resolution test: PASS ==="
