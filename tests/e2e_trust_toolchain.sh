#!/bin/bash
# Smoke test: a built local tRust sysroot is linked into rustup as `trust`
# and behaves like a practical Rust toolchain.
#
# Exercises the linked-toolchain daily-driver flow through:
#   - `rustup run trust cargo ...`
#   - `cargo +trust ...`
#   - `RUSTUP_TOOLCHAIN=trust cargo ...` as a non-invasive approximation of
#     default-toolchain dispatch
#
# This runs against a fresh temp crate while checking that the linked `trust`
# toolchain resolves to the expected local sysroot. It may refresh the rustup
# `trust` link, but it does not mutate `rustup default`.
#
# It also verifies cargo build/check/test/doc/fmt/clippy/miri surfaces plus
# `cargo trust check` with the default backend and LLVM2 when available.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
HOST_RUSTUP_BIN="$(command -v rustup 2>/dev/null || true)"
HOST_CARGO_SHIM=""
if [ -n "$HOST_RUSTUP_BIN" ]; then
    HOST_CARGO_SHIM_CANDIDATE="$(dirname "$HOST_RUSTUP_BIN")/cargo"
    if [ -x "$HOST_CARGO_SHIM_CANDIDATE" ]; then
        HOST_CARGO_SHIM="$HOST_CARGO_SHIM_CANDIDATE"
    fi
fi
if [ -z "$HOST_CARGO_SHIM" ]; then
    HOST_CARGO_SHIM="$(command -v cargo 2>/dev/null || true)"
fi

echo "=== tRust Smoke Test: linked trust toolchain ==="
echo

skip_test() {
    printf 'SKIP: %s\n' "$1" >&2
    exit 0
}

fail_test() {
    printf 'FAIL: %s\n' "$1" >&2
    exit 1
}

canonicalize_dir() {
    (
        cd "$1"
        pwd -P
    )
}

require_executable() {
    if [ ! -x "$1" ]; then
        fail_test "missing executable: $1"
    fi
}

require_directory() {
    if [ ! -d "$1" ]; then
        fail_test "missing directory: $1"
    fi
}

require_linked_tool() {
    local tool="$1"
    if ! rustup which --toolchain trust "$tool" >/dev/null 2>&1; then
        fail_test "linked trust toolchain is missing $tool"
    fi
}

current_trust_path() {
    rustup toolchain list -v | awk '$1 == "trust" { print $NF; exit }'
}

run_linked_cargo() {
    env -u RUSTC -u RUSTDOC -u RUSTFMT -u CLIPPY_DRIVER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC -u RUSTUP_TOOLCHAIN \
        rustup run trust cargo "$@"
}

run_plus_trust_cargo() {
    env -u RUSTC -u RUSTDOC -u RUSTFMT -u CLIPPY_DRIVER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC -u RUSTUP_TOOLCHAIN \
        "$HOST_CARGO_SHIM" +trust "$@"
}

run_default_toolchain_cargo() {
    env -u RUSTC -u RUSTDOC -u RUSTFMT -u CLIPPY_DRIVER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC -u RUSTUP_TOOLCHAIN \
        RUSTUP_TOOLCHAIN=trust "$HOST_CARGO_SHIM" "$@"
}

find_llvm2_backend() {
    local backend_dir="$1"
    local pattern

    for pattern in \
        "$backend_dir"/librustc_codegen_llvm2*.dylib \
        "$backend_dir"/librustc_codegen_llvm2*.so \
        "$backend_dir"/rustc_codegen_llvm2*.dll
    do
        if [ -e "$pattern" ]; then
            printf '%s\n' "$pattern"
            return 0
        fi
    done

    return 1
}

LOCAL_SYSROOT=""
CANDIDATES=(
    "$TRUST_ROOT/build/host/stage2"
    "$TRUST_ROOT/build/host/stage1"
    "$TRUST_ROOT/build/aarch64-apple-darwin/stage2"
    "$TRUST_ROOT/build/aarch64-apple-darwin/stage1"
    "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage2"
    "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage1"
    "$TRUST_ROOT/build/x86_64-apple-darwin/stage2"
    "$TRUST_ROOT/build/x86_64-apple-darwin/stage1"
)

for candidate in "${CANDIDATES[@]}"; do
    if [ -x "$candidate/bin/rustc" ]; then
        LOCAL_SYSROOT="$candidate"
        break
    fi
done

if [ -z "$LOCAL_SYSROOT" ]; then
    skip_test "local toolchain not found (build with ./x.py build --stage 1 compiler/rustc or --stage 2 under download-rustc)"
fi

LOCAL_SYSROOT="$(canonicalize_dir "$LOCAL_SYSROOT")"
BIN_DIR="$LOCAL_SYSROOT/bin"
CARGO_BIN="$BIN_DIR/cargo"
TARGET_TRIPLE="$(basename "$(dirname "$LOCAL_SYSROOT")")"
STAGE_NAME="$(basename "$LOCAL_SYSROOT")"
RUSTC_DEPS_DIR="$(dirname "$LOCAL_SYSROOT")/${STAGE_NAME}-rustc/$TARGET_TRIPLE/release/deps"
export PATH="$BIN_DIR:$PATH"
export RUSTC="$BIN_DIR/rustc"
export RUSTDOC="$BIN_DIR/rustdoc"
export RUSTFMT="$BIN_DIR/rustfmt"
export CLIPPY_DRIVER="$BIN_DIR/clippy-driver"
require_executable "$CARGO_BIN"
require_executable "$RUSTDOC"

RUNTIME_LIB_PATHS=("$LOCAL_SYSROOT/lib")
if [ -d "$LOCAL_SYSROOT/lib/rustlib/$TARGET_TRIPLE/lib" ]; then
    RUNTIME_LIB_PATHS+=("$LOCAL_SYSROOT/lib/rustlib/$TARGET_TRIPLE/lib")
fi
if [ -d "$RUSTC_DEPS_DIR" ]; then
    RUNTIME_LIB_PATHS+=("$RUSTC_DEPS_DIR")
fi
RUNTIME_LIB_PATH="$(IFS=:; echo "${RUNTIME_LIB_PATHS[*]}")"
case "$(uname -s)" in
    Darwin)
        export DYLD_LIBRARY_PATH="$RUNTIME_LIB_PATH${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"
        ;;
    Linux)
        export LD_LIBRARY_PATH="$RUNTIME_LIB_PATH${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
        ;;
esac

if ! command -v rustup >/dev/null 2>&1; then
    skip_test "rustup not found on PATH; linked trust toolchain smoke test requires rustup"
fi
if [ -z "$HOST_CARGO_SHIM" ] || [ ! -x "$HOST_CARGO_SHIM" ]; then
    fail_test "cargo shim not found on PATH; linked launch smoke requires cargo +trust / RUSTUP_TOOLCHAIN=trust dispatch"
fi

CURRENT_TRUST_PATH="$(current_trust_path || true)"
if [ -n "$CURRENT_TRUST_PATH" ] && [ -d "$CURRENT_TRUST_PATH" ]; then
    CURRENT_TRUST_PATH="$(canonicalize_dir "$CURRENT_TRUST_PATH")"
else
    CURRENT_TRUST_PATH=""
fi

if [ "$CURRENT_TRUST_PATH" != "$LOCAL_SYSROOT" ]; then
    echo "linking rustup toolchain 'trust' -> $LOCAL_SYSROOT"
    rustup toolchain link trust "$LOCAL_SYSROOT"
fi

if ! LINKED_RUSTC="$(rustup which --toolchain trust rustc 2>&1)"; then
    fail_test "linked trust toolchain not found after linking $LOCAL_SYSROOT
$LINKED_RUSTC"
fi
require_executable "$LINKED_RUSTC"

echo "sysroot: $LOCAL_SYSROOT"
echo "rustc: $("$RUSTC" --version)"
echo "cargo: $("$CARGO_BIN" --version)"
echo "linked rustc: $LINKED_RUSTC"
if ! LINKED_CARGO_VERSION="$(run_linked_cargo --version 2>&1)"; then
    fail_test "rustup could not run trust cargo --version
$LINKED_CARGO_VERSION"
fi
echo "linked cargo: $LINKED_CARGO_VERSION"
if ! PLUS_TRUST_CARGO_VERSION="$(run_plus_trust_cargo --version 2>&1)"; then
    fail_test "cargo +trust dispatch failed
$PLUS_TRUST_CARGO_VERSION"
fi
echo "cargo +trust: $PLUS_TRUST_CARGO_VERSION"
if ! DEFAULT_TOOLCHAIN_CARGO_VERSION="$(run_default_toolchain_cargo --version 2>&1)"; then
    fail_test "RUSTUP_TOOLCHAIN=trust cargo dispatch failed
$DEFAULT_TOOLCHAIN_CARGO_VERSION"
fi
echo "default-surface cargo: $DEFAULT_TOOLCHAIN_CARGO_VERSION"
echo

if ! SYSROOT="$(rustup run trust rustc --print sysroot 2>&1)"; then
    fail_test "rustup could not run trust rustc --print sysroot
$SYSROOT"
fi
if ! HOST_INFO="$(rustup run trust rustc -vV 2>&1)"; then
    fail_test "rustup could not run trust rustc -vV
$HOST_INFO"
fi
HOST_TRIPLE="$(printf '%s\n' "$HOST_INFO" | awk '/^host: / { print $2 }')"
if [ -z "$HOST_TRIPLE" ]; then
    fail_test "could not determine host triple from linked trust rustc -vV"
fi

if [ "$(canonicalize_dir "$SYSROOT")" != "$LOCAL_SYSROOT" ]; then
    fail_test "linked trust sysroot mismatch: expected $LOCAL_SYSROOT, got $SYSROOT"
fi

for tool in cargo cargo-trust rust-analyzer rustdoc cargo-fmt cargo-clippy clippy-driver rustfmt cargo-miri miri; do
    require_linked_tool "$tool"
done

require_executable "$SYSROOT/libexec/rust-analyzer-proc-macro-srv"
require_directory "$SYSROOT/lib/rustlib/src/rust"
require_directory "$SYSROOT/lib/rustlib/rustc-src/rust"

for llvm_tool in llvm-ar llvm-nm llvm-objdump llvm-profdata; do
    require_executable "$SYSROOT/lib/rustlib/$HOST_TRIPLE/bin/$llvm_tool"
done

TMP_DIR="$(mktemp -d /tmp/trust_toolchain_smoke_XXXXXX)"
trap 'rm -rf "$TMP_DIR"' EXIT

pushd "$TMP_DIR" >/dev/null

run_linked_cargo new smoke --bin --quiet
cd smoke

run_cargo_trust_check() {
    local label="$1"
    shift

    local stdout_file="$TMP_DIR/cargo-trust-${label}.stdout"
    local stderr_file="$TMP_DIR/cargo-trust-${label}.stderr"
    local exit_code=0

    if run_linked_cargo trust check --format json "$@" >"$stdout_file" 2>"$stderr_file"; then
        exit_code=0
    else
        exit_code=$?
    fi

    if [ "$exit_code" -gt 1 ]; then
        fail_test "cargo trust check ($label) exited with $exit_code
$(cat "$stderr_file")"
    fi

    if [ ! -s "$stdout_file" ]; then
        fail_test "cargo trust check ($label) produced no JSON output
$(cat "$stderr_file")"
    fi
}

cat <<'RUST' > src/main.rs
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

echo "--- cargo check"
run_linked_cargo check

echo "--- cargo +trust check"
run_plus_trust_cargo check

echo "--- cargo build"
run_linked_cargo build

echo "--- cargo test"
run_linked_cargo test

echo "--- RUSTUP_TOOLCHAIN=trust cargo test"
run_default_toolchain_cargo test

echo "--- cargo doc --no-deps"
run_linked_cargo doc --no-deps

if [ -x "$BIN_DIR/cargo-fmt" ] && [ -x "$BIN_DIR/rustfmt" ]; then
    echo "--- cargo fmt --check"
    run_linked_cargo fmt --check
else
    echo "--- cargo fmt --check (SKIP: rustfmt not present)"
fi

if [ -x "$BIN_DIR/cargo-clippy" ] && [ -x "$BIN_DIR/clippy-driver" ]; then
    echo "--- cargo clippy -- -D warnings"
    run_linked_cargo clippy -- -D warnings
else
    echo "--- cargo clippy -- -D warnings (SKIP: clippy not present)"
fi

if [ -x "$BIN_DIR/cargo-miri" ] && [ -x "$BIN_DIR/miri" ]; then
    if run_linked_cargo miri --version >/dev/null 2>&1; then
        echo "--- cargo miri test"
        run_linked_cargo miri test
    else
        echo "--- cargo miri test (SKIP: standalone cargo-miri dispatch unavailable)"
    fi
else
    echo "--- cargo miri test (SKIP: miri not present)"
fi

echo "--- cargo trust check --format json"
run_cargo_trust_check default src/main.rs

LLVM2_BACKEND_DIR="$SYSROOT/lib/rustlib/$HOST_TRIPLE/codegen-backends"
LLVM2_BACKEND="$(find_llvm2_backend "$LLVM2_BACKEND_DIR" || true)"
if [ -n "$LLVM2_BACKEND" ]; then
    echo "--- cargo trust check --backend llvm2 --format json"
    run_cargo_trust_check llvm2 --backend llvm2 src/main.rs
else
    echo "--- cargo trust check --backend llvm2 --format json (SKIP: llvm2 backend not present)"
fi

popd >/dev/null

echo
echo "=== local trust toolchain smoke test: PASS ==="
