#!/bin/bash
# Smoke test: LLVM2 codegen backend exercises adapter + MIR extraction + bridge lowering
#
# Tests that:
# 1. rustc can be invoked with -Z codegen-backend=llvm2
# 2. Metadata emission succeeds and writes an .rmeta artifact
# 3. A focused checked_div/Option<i32> object+link smoke reaches LLVM2 MIR
#    extraction + bridge lowering
# 4. Object and link outputs are materialized
# 5. The smallest linked runtime repro executes and validates native call behavior
# 6. A rustc-generated checked-overflow runtime smoke reaches the native abort path
#
# Prerequisites: stage1 rustc built with codegen-backends = ["llvm", "llvm2"]
#
# Author: Andrew Yates <andrew@andrewdyates.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "=== tRust Smoke Test: LLVM2 codegen backend ==="
echo

# --- Locate stage1 trustc / compatibility rustc ---
RUSTC=""
CANDIDATES=(
    "$TRUST_ROOT/build/host/stage1/bin/trustc"
    "$TRUST_ROOT/build/aarch64-apple-darwin/stage1/bin/trustc"
    "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage1/bin/trustc"
    "$TRUST_ROOT/build/x86_64-apple-darwin/stage1/bin/trustc"
    "$TRUST_ROOT/build/host/stage1/bin/rustc"
    "$TRUST_ROOT/build/aarch64-apple-darwin/stage1/bin/rustc"
    "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage1/bin/rustc"
    "$TRUST_ROOT/build/x86_64-apple-darwin/stage1/bin/rustc"
)

for candidate in "${CANDIDATES[@]}"; do
    if [ -x "$candidate" ]; then
        RUSTC="$candidate"
        break
    fi
done

if [ -z "$RUSTC" ]; then
    echo "SKIP: stage1 trustc not found (build with ./x.py build)"
    echo "  Ensure config.toml has: codegen-backends = [\"llvm\", \"llvm2\"]"
    echo "  under [rust]"
    exit 0  # Skip gracefully -- not a failure
fi

echo "Using trustc: $RUSTC"

# --- Verify the stage1 sysroot actually contains the LLVM2 backend ---
SYSROOT=$("$RUSTC" --print sysroot)
HOST_TRIPLE=$("$RUSTC" -vV | sed -n 's/^host: //p')
RUSTC_RELEASE=$("$RUSTC" -vV | sed -n 's/^release: //p')
BACKEND_DIR="$SYSROOT/lib/rustlib/$HOST_TRIPLE/codegen-backends"
BACKEND_CANDIDATES=(
    "$BACKEND_DIR/librustc_codegen_llvm2-$RUSTC_RELEASE.so"
    "$BACKEND_DIR/librustc_codegen_llvm2.so"
    "$BACKEND_DIR/librustc_codegen_llvm2-$RUSTC_RELEASE.dylib"
    "$BACKEND_DIR/librustc_codegen_llvm2.dylib"
    "$BACKEND_DIR/rustc_codegen_llvm2-$RUSTC_RELEASE.dll"
    "$BACKEND_DIR/rustc_codegen_llvm2.dll"
)

if [ ! -d "$BACKEND_DIR" ]; then
    echo "ERROR: stage1 rustc found, but codegen backends directory is missing:"
    echo "  $BACKEND_DIR"
    echo "  Rebuild stage1 with codegen-backends = [\"llvm\", \"llvm2\"]"
    exit 1
fi

LLVM2_BACKEND=""
for candidate in "${BACKEND_CANDIDATES[@]}"; do
    if [ -f "$candidate" ]; then
        LLVM2_BACKEND="$candidate"
        break
    fi
done

if [ -z "$LLVM2_BACKEND" ]; then
    echo "ERROR: stage1 rustc found, but the llvm2 backend is missing from:"
    echo "  $BACKEND_DIR"
    echo "  Expected one of:"
    for candidate in "${BACKEND_CANDIDATES[@]}"; do
        echo "    $candidate"
    done
    exit 1
fi

echo "Using llvm2 backend: $LLVM2_BACKEND"

# --- Create test input ---
TMP_DIR=$(mktemp -d /tmp/llvm2_smoke_XXXXXX)
METADATA_INPUT="$TMP_DIR/llvm2_smoke.rs"
BUG_INPUT="$TMP_DIR/llvm2_checked_div_option.rs"
RUNTIME_INPUT="$TMP_DIR/llvm2_runtime_min.rs"
RUNTIME_CF_INPUT="$TMP_DIR/llvm2_runtime_cf.rs"
RUNTIME_ABORT_INPUT="$TMP_DIR/llvm2_runtime_abort.rs"
RUNTIME_OVERFLOW_INPUT="$TMP_DIR/llvm2_runtime_overflow.rs"
METADATA_OUT="$TMP_DIR/llvm2_smoke.rmeta"
OBJECT_OUT="$TMP_DIR/llvm2_smoke.o"
LINK_OUT="$TMP_DIR/llvm2_smoke_bin"
RUNTIME_LINK_OUT="$TMP_DIR/llvm2_runtime_smoke_bin"
RUNTIME_CF_LINK_OUT="$TMP_DIR/llvm2_runtime_cf_smoke_bin"
RUNTIME_ABORT_LINK_OUT="$TMP_DIR/llvm2_runtime_abort_smoke_bin"
RUNTIME_OVERFLOW_LINK_OUT="$TMP_DIR/llvm2_runtime_overflow_smoke_bin"
METADATA_STDERR="$TMP_DIR/metadata.stderr"
OBJECT_STDERR="$TMP_DIR/object.stderr"
LINK_STDERR="$TMP_DIR/link.stderr"
RUNTIME_LINK_STDERR="$TMP_DIR/runtime-link.stderr"
RUNTIME_CF_LINK_STDERR="$TMP_DIR/runtime-cf-link.stderr"
RUNTIME_ABORT_LINK_STDERR="$TMP_DIR/runtime-abort-link.stderr"
RUNTIME_OVERFLOW_LINK_STDERR="$TMP_DIR/runtime-overflow-link.stderr"
RUNTIME_STDOUT="$TMP_DIR/runtime.stdout"
RUNTIME_STDERR="$TMP_DIR/runtime.stderr"
RUNTIME_CF_STDOUT="$TMP_DIR/runtime-cf.stdout"
RUNTIME_CF_STDERR="$TMP_DIR/runtime-cf.stderr"
RUNTIME_ABORT_STDOUT="$TMP_DIR/runtime-abort.stdout"
RUNTIME_ABORT_STDERR="$TMP_DIR/runtime-abort.stderr"
RUNTIME_OVERFLOW_STDOUT="$TMP_DIR/runtime-overflow.stdout"
RUNTIME_OVERFLOW_STDERR="$TMP_DIR/runtime-overflow.stderr"
RUNTIME_FULL_DISASM="$TMP_DIR/runtime-full.disasm"
RUNTIME_MAIN_DISASM="$TMP_DIR/runtime-main.disasm"
trap 'rm -rf "$TMP_DIR"' EXIT

cat > "$METADATA_INPUT" << 'RUST'
// Smoke test input for LLVM2 codegen backend.
// Exercises: straight-line, branching, function call.

pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

pub fn identity(x: u64) -> u64 {
    x
}

pub fn sum_to(n: u32) -> u32 {
    let mut acc = 0u32;
    let mut i = 0u32;
    while i < n {
        acc += i;
        i += 1;
    }
    acc
}

fn main() {
    let added = add(2, 3);
    let ident = identity(7);

    if added == 5 && ident == 7 {
        std::process::exit(0);
    }

    std::process::exit(21);
}
RUST

cat > "$BUG_INPUT" << 'RUST'
// Focused native object-emission regression input for checked_div/Option<i32>.

pub fn checked_div(a: i32, b: i32) -> Option<i32> {
    if b == 0 { None } else { Some(a / b) }
}

fn main() {
    let _ = checked_div(10, 2);
}
RUST

cat > "$RUNTIME_INPUT" << 'RUST'
// Smallest linked runtime repro found so far: a single direct call in main.

fn main() {
    std::process::exit(0);
}
RUST

cat > "$RUNTIME_CF_INPUT" << 'RUST'
// No-std-surface runtime smoke: branch/join plus call continuation.

#[inline(never)]
fn input() -> bool {
    true
}

#[inline(never)]
fn bump(x: i32) -> i32 {
    x + 1
}

#[inline(never)]
fn choose(flag: bool) -> i32 {
    let base = if flag { 3 } else { 99 };
    bump(base)
}

fn main() {
    let joined = choose(input());
    if joined == 4 {
        return;
    }
    loop {}
}
RUST

cat > "$RUNTIME_ABORT_INPUT" << 'RUST'
// Abnormal runtime smoke: direct abort-style trap.

#[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
compile_error!("runtime abort smoke requires aarch64 or x86_64");

fn main() {
    unsafe {
        #[cfg(target_arch = "aarch64")]
        core::arch::asm!("brk #0", options(noreturn));

        #[cfg(target_arch = "x86_64")]
        core::arch::asm!("ud2", options(noreturn));
    }
}
RUST

cat > "$RUNTIME_OVERFLOW_INPUT" << 'RUST'
// Abnormal runtime smoke: rustc-generated checked overflow should abort.

#[inline(never)]
fn checked_add(x: i32, y: i32) -> i32 {
    x + y
}

fn main() {
    let _ = checked_add(i32::MAX, 1);
}
RUST

echo "Metadata input: $METADATA_INPUT"
echo "Object/link regression input: $BUG_INPUT"
echo "Runtime repro input: $RUNTIME_INPUT"
echo "Runtime control-flow input: $RUNTIME_CF_INPUT"
echo "Runtime abnormal input: $RUNTIME_ABORT_INPUT"
echo "Runtime overflow input: $RUNTIME_OVERFLOW_INPUT"
echo

run_case() {
    local case_name="$1"
    local stderr_file="$2"
    shift 2

    local cmd=(
        "$RUSTC"
        -Z codegen-backend=llvm2
        --edition 2021
        "$@"
    )

    echo "Running [$case_name]: RUSTC_LOG=rustc_codegen_llvm2=info ${cmd[*]}"
    echo

    RUN_CASE_EXIT=0
    RUSTC_LOG="rustc_codegen_llvm2=info" "${cmd[@]}" >/dev/null 2>"$stderr_file" || RUN_CASE_EXIT=$?
    RUN_CASE_OUTPUT=$(cat "$stderr_file")

    echo "--- [$case_name] stderr output (first 40 lines) ---"
    echo "$RUN_CASE_OUTPUT" | head -40
    echo "--- end [$case_name] stderr ---"
    echo
}

runtime_main_disasm() {
    local binary="$1"

    if command -v otool >/dev/null 2>&1; then
        otool -tvV "$binary" | sed -n '/_main:/,+24p'
        return
    fi

    if command -v llvm-objdump >/dev/null 2>&1; then
        llvm-objdump -d "$binary" | sed -n '/<_main>:/,+24p'
        return
    fi

    if command -v objdump >/dev/null 2>&1; then
        objdump -d "$binary" | sed -n '/<_main>:/,+24p'
    fi
}

runtime_full_disasm() {
    local binary="$1"

    if command -v otool >/dev/null 2>&1; then
        otool -tvV "$binary"
        return
    fi

    if command -v llvm-objdump >/dev/null 2>&1; then
        llvm-objdump -d "$binary"
        return
    fi

    if command -v objdump >/dev/null 2>&1; then
        objdump -d "$binary"
    fi
}

runtime_main_address() {
    local binary="$1"

    if command -v nm >/dev/null 2>&1; then
        nm -nm "$binary" 2>/dev/null | awk '$NF == "_main" { print $1; exit }'
        return
    fi

    if command -v llvm-nm >/dev/null 2>&1; then
        llvm-nm "$binary" 2>/dev/null | awk '$NF == "_main" { print $1; exit }'
    fi
}

run_binary_with_timeout() {
    local binary="$1"
    local stdout_file="$2"
    local stderr_file="$3"
    local timeout_secs="$4"
    local timeout_file="$TMP_DIR/runtime-timeout.$RANDOM.$$"
    local runner_pid=""
    local watchdog_pid=""

    RUN_BINARY_EXIT=125
    : >"$stdout_file"
    : >"$stderr_file"
    rm -f "$timeout_file"

    "$binary" >"$stdout_file" 2>"$stderr_file" &
    runner_pid=$!

    (
        sleep "$timeout_secs"
        if kill -0 "$runner_pid" 2>/dev/null; then
            printf 'runtime timeout after %s seconds\n' "$timeout_secs" >>"$stderr_file"
            : >"$timeout_file"
            kill -TERM "$runner_pid" 2>/dev/null || true
            sleep 1
            kill -KILL "$runner_pid" 2>/dev/null || true
        fi
    ) &
    watchdog_pid=$!

    if wait "$runner_pid" 2>/dev/null; then
        RUN_BINARY_EXIT=0
    else
        RUN_BINARY_EXIT=$?
    fi
    kill "$watchdog_pid" 2>/dev/null || true
    wait "$watchdog_pid" 2>/dev/null || true

    if [ -f "$timeout_file" ]; then
        RUN_BINARY_EXIT=124
        rm -f "$timeout_file"
    fi
}

run_runtime_binary_case() {
    local case_name="$1"
    local link_exit="$2"
    local binary="$3"
    local stdout_file="$4"
    local stderr_file="$5"
    local case_tag=""
    local full_disasm_file=""
    local main_disasm_file=""

    RUNTIME_CASE_EXIT=125
    RUNTIME_CASE_OUTPUT=""
    RUNTIME_CASE_ERROR_OUTPUT=""
    RUNTIME_CASE_DISASM_OUTPUT=""
    RUNTIME_CASE_MAIN_ENTRY_ADDR=""
    RUNTIME_CASE_MAIN_ENTRY_TARGETS=""
    RUNTIME_CASE_MAIN_BRANCH_SUMMARY=""
    RUNTIME_CASE_SELF_CALL_SIGNATURE=""
    RUNTIME_CASE_FIRST_CALL_SITE=""
    RUNTIME_CASE_SKIP_REASON=""

    if [ "$link_exit" -eq 0 ] && [ -x "$binary" ]; then
        echo "Running [$case_name]: $binary"
        echo

        run_binary_with_timeout "$binary" "$stdout_file" "$stderr_file" 5
        RUNTIME_CASE_EXIT="$RUN_BINARY_EXIT"
        RUNTIME_CASE_OUTPUT=$(cat "$stdout_file")
        RUNTIME_CASE_ERROR_OUTPUT=$(cat "$stderr_file")

        if [ "$RUNTIME_CASE_EXIT" -ne 0 ]; then
            case_tag=$(printf '%s' "$case_name" | tr -cs '[:alnum:]' '_')
            full_disasm_file="$TMP_DIR/${case_tag}.full.disasm"
            main_disasm_file="$TMP_DIR/${case_tag}.main.disasm"

            RUNTIME_CASE_MAIN_ENTRY_ADDR=$(runtime_main_address "$binary" || true)
            runtime_full_disasm "$binary" >"$full_disasm_file" 2>/dev/null || true
            if [ -n "$RUNTIME_CASE_MAIN_ENTRY_ADDR" ] && [ -s "$full_disasm_file" ]; then
                RUNTIME_CASE_MAIN_ENTRY_TARGETS=$(runtime_targeting_main_branches "$full_disasm_file" "$RUNTIME_CASE_MAIN_ENTRY_ADDR" || true)
            fi

            runtime_main_disasm "$binary" >"$main_disasm_file" 2>/dev/null || true
            if [ -s "$main_disasm_file" ]; then
                RUNTIME_CASE_DISASM_OUTPUT=$(cat "$main_disasm_file")
                if [ -n "$RUNTIME_CASE_MAIN_ENTRY_ADDR" ]; then
                    RUNTIME_CASE_MAIN_BRANCH_SUMMARY=$(runtime_main_branch_summary "$main_disasm_file" "$RUNTIME_CASE_MAIN_ENTRY_ADDR" || true)
                    RUNTIME_CASE_SELF_CALL_SIGNATURE=$(printf '%s\n' "$RUNTIME_CASE_MAIN_BRANCH_SUMMARY" | grep -m1 'self-targeting' || true)
                fi
                RUNTIME_CASE_FIRST_CALL_SITE=$(printf '%s\n' "$RUNTIME_CASE_DISASM_OUTPUT" | grep -m1 -E '[[:space:]](bl|call)[[:space:]]' || true)
            fi
        fi

        echo "--- [$case_name] stdout ---"
        if [ -n "$RUNTIME_CASE_OUTPUT" ]; then
            echo "$RUNTIME_CASE_OUTPUT" | head -40
        else
            echo "(empty)"
        fi
        echo "--- [$case_name] stderr ---"
        if [ -n "$RUNTIME_CASE_ERROR_OUTPUT" ]; then
            echo "$RUNTIME_CASE_ERROR_OUTPUT" | head -40
        else
            echo "(empty)"
        fi
        echo "--- end [$case_name] output ---"
        echo

        if [ -n "$RUNTIME_CASE_MAIN_ENTRY_ADDR" ]; then
            echo "--- [$case_name] _main entry address ---"
            echo "0x${RUNTIME_CASE_MAIN_ENTRY_ADDR#0x}"
            echo "--- end [$case_name] _main entry address ---"
            echo
        fi

        if [ -n "$RUNTIME_CASE_DISASM_OUTPUT" ]; then
            echo "--- [$case_name] _main disassembly (first 25 lines) ---"
            echo "$RUNTIME_CASE_DISASM_OUTPUT"
            echo "--- end [$case_name] _main disassembly ---"
            echo
        fi

        if [ "$RUNTIME_CASE_EXIT" -ne 0 ]; then
            echo "--- [$case_name] calls/jumps targeting _main entry ---"
            if [ -n "$RUNTIME_CASE_MAIN_ENTRY_TARGETS" ]; then
                echo "$RUNTIME_CASE_MAIN_ENTRY_TARGETS" | head -40
            elif [ -n "$RUNTIME_CASE_MAIN_ENTRY_ADDR" ]; then
                echo "(none)"
            else
                echo "(unavailable: _main symbol address not found)"
            fi
            echo "--- end [$case_name] calls/jumps targeting _main entry ---"
            echo
        fi

        if [ "$RUNTIME_CASE_EXIT" -ne 0 ]; then
            echo "--- [$case_name] suspicious control transfers in _main ---"
            if [ -n "$RUNTIME_CASE_MAIN_BRANCH_SUMMARY" ]; then
                echo "$RUNTIME_CASE_MAIN_BRANCH_SUMMARY" | head -40
            else
                echo "(none)"
            fi
            echo "--- end [$case_name] suspicious control transfers in _main ---"
            echo
        fi

        if [ -n "$RUNTIME_CASE_FIRST_CALL_SITE" ]; then
            echo "--- [$case_name] first call site in _main ---"
            echo "$RUNTIME_CASE_FIRST_CALL_SITE"
            echo "--- end [$case_name] first call site ---"
            echo
        fi
    else
        RUNTIME_CASE_SKIP_REASON="${case_name}-link exit=$link_exit"
        if [ ! -e "$binary" ]; then
            RUNTIME_CASE_SKIP_REASON="$RUNTIME_CASE_SKIP_REASON; linked binary not materialized"
        elif [ ! -x "$binary" ]; then
            RUNTIME_CASE_SKIP_REASON="$RUNTIME_CASE_SKIP_REASON; linked binary not executable"
        fi

        echo "SKIP: $case_name execution not entered ($RUNTIME_CASE_SKIP_REASON)"
        echo
    fi
}

run_runtime_abnormal_case() {
    local case_name="$1"
    local link_exit="$2"
    local binary="$3"
    local stdout_file="$4"
    local stderr_file="$5"

    RUNTIME_ABNORMAL_EXIT=125
    RUNTIME_ABNORMAL_OUTPUT=""
    RUNTIME_ABNORMAL_ERROR_OUTPUT=""
    RUNTIME_ABNORMAL_SKIP_REASON=""

    if [ "$link_exit" -eq 0 ] && [ -x "$binary" ]; then
        echo "Running [$case_name]: $binary"
        echo

        run_binary_with_timeout "$binary" "$stdout_file" "$stderr_file" 5
        RUNTIME_ABNORMAL_EXIT="$RUN_BINARY_EXIT"
        RUNTIME_ABNORMAL_OUTPUT=$(cat "$stdout_file")
        RUNTIME_ABNORMAL_ERROR_OUTPUT=$(cat "$stderr_file")

        echo "--- [$case_name] stdout ---"
        if [ -n "$RUNTIME_ABNORMAL_OUTPUT" ]; then
            echo "$RUNTIME_ABNORMAL_OUTPUT" | head -20
        else
            echo "(empty)"
        fi
        echo "--- [$case_name] stderr ---"
        if [ -n "$RUNTIME_ABNORMAL_ERROR_OUTPUT" ]; then
            echo "$RUNTIME_ABNORMAL_ERROR_OUTPUT" | head -20
        else
            echo "(empty)"
        fi
        echo "--- end [$case_name] output ---"
        echo "[$case_name] exit: $RUNTIME_ABNORMAL_EXIT"
        echo
    else
        RUNTIME_ABNORMAL_SKIP_REASON="${case_name}-link exit=$link_exit"
        if [ ! -e "$binary" ]; then
            RUNTIME_ABNORMAL_SKIP_REASON="$RUNTIME_ABNORMAL_SKIP_REASON; linked binary not materialized"
        elif [ ! -x "$binary" ]; then
            RUNTIME_ABNORMAL_SKIP_REASON="$RUNTIME_ABNORMAL_SKIP_REASON; linked binary not executable"
        fi

        echo "SKIP: $case_name execution not entered ($RUNTIME_ABNORMAL_SKIP_REASON)"
        echo
    fi
}

runtime_abnormal_exit_brief() {
    local exit_code="$1"
    local signal_num=""
    local signal_name="SIGUNKNOWN"
    local signal_kind="signal-termination"

    if [ "$exit_code" -eq 0 ]; then
        printf 'kind=unexpected-success exit=%s\n' "$exit_code"
        return 0
    fi

    if [ "$exit_code" -eq 124 ]; then
        printf 'kind=timeout exit=%s detail=timeout after 5 seconds\n' "$exit_code"
        return 0
    fi

    if [ "$exit_code" -lt 128 ]; then
        printf 'kind=runtime-failure exit=%s\n' "$exit_code"
        return 0
    fi

    signal_num=$((exit_code - 128))
    case "$signal_num" in
        1) signal_name="SIGHUP" ;;
        2) signal_name="SIGINT" ;;
        3) signal_name="SIGQUIT" ;;
        4) signal_name="SIGILL" ;;
        5) signal_name="SIGTRAP" ;;
        6) signal_name="SIGABRT" ;;
        7) signal_name="SIGEMT" ;;
        8) signal_name="SIGFPE" ;;
        9) signal_name="SIGKILL" ;;
        10) signal_name="SIGBUS" ;;
        11) signal_name="SIGSEGV" ;;
        12) signal_name="SIGSYS" ;;
        13) signal_name="SIGPIPE" ;;
        14) signal_name="SIGALRM" ;;
        15) signal_name="SIGTERM" ;;
    esac

    case "$signal_name" in
        SIGABRT)
            signal_kind="abort-signal"
            ;;
        SIGTRAP|SIGILL)
            signal_kind="trap-signal"
            ;;
        SIGFPE)
            signal_kind="fpe-signal"
            ;;
    esac

    printf 'kind=%s exit=%s signal_num=%s signal=%s\n' \
        "$signal_kind" "$exit_code" "$signal_num" "$signal_name"
}

runtime_targeting_main_branches() {
    local disasm_file="$1"
    local main_addr="$2"

    python3 - "$disasm_file" "$main_addr" <<'PY'
import re
import sys

disasm_path, raw_addr = sys.argv[1:]
addr = raw_addr.strip().lower()
if addr.startswith("0x"):
    addr = addr[2:]
addr = addr.lstrip("0") or "0"

branch_re = re.compile(
    r"\b(?:b(?:\.[a-z]+)?|bl|blr|br|cbz|cbnz|tbz|tbnz|jmp|j[a-z]+|callq?)\b",
    re.IGNORECASE,
)

hits = []
with open(disasm_path, "r", encoding="utf-8", errors="replace") as disasm:
    for line in disasm:
        match = branch_re.search(line)
        if not match:
            continue

        operand_text = line[match.end():].lower()
        if (
            f"0x{addr}" in operand_text
            or re.search(rf"(^|[^0-9a-f]){re.escape(addr)}([^0-9a-f]|$)", operand_text)
            or "_main" in operand_text
        ):
            hits.append(line.rstrip("\n"))

if hits:
    print("\n".join(hits))
PY
}

runtime_main_branch_summary() {
    local disasm_file="$1"
    local main_addr="$2"

    python3 - "$disasm_file" "$main_addr" <<'PY'
import re
import sys

disasm_path, raw_main_addr = sys.argv[1:]
main_addr = raw_main_addr.strip().lower()
if main_addr.startswith("0x"):
    main_addr = main_addr[2:]
main_value = int(main_addr, 16) if main_addr else None

branch_re = re.compile(
    r"\b(?:b(?:\.[a-z]+)?|bl|blr|br|cbz|cbnz|tbz|tbnz|jmp|j[a-z]+|callq?)\b",
    re.IGNORECASE,
)
addr_re = re.compile(r"^\s*([0-9a-f]+)\b", re.IGNORECASE)
target_re = re.compile(r"\b(?:0x)?([0-9a-f]{6,})\b", re.IGNORECASE)

hits = []
with open(disasm_path, "r", encoding="utf-8", errors="replace") as disasm:
    for line in disasm:
        branch = branch_re.search(line)
        if not branch:
            continue

        addr_match = addr_re.match(line)
        if not addr_match:
            continue

        operand_text = line[branch.end():]
        target_match = target_re.search(operand_text)
        if not target_match:
            continue

        instr_addr = int(addr_match.group(1), 16)
        target_addr = int(target_match.group(1), 16)

        tags = []
        if target_addr == instr_addr:
            tags.append("self-targeting")
        if main_value is not None and target_addr == main_value:
            tags.append("targets _main entry")

        if not tags:
            continue

        delta = target_addr - instr_addr
        hits.append(f"{', '.join(tags)} (delta {delta:+#x}): {line.rstrip()}")

if hits:
    print("\n".join(hits))
PY
}

llvm2_emit_failure_summary() {
    local stderr_file="$1"

    python3 - "$stderr_file" <<'PY'
import re
import sys

stderr_path = sys.argv[1]
with open(stderr_path, "r", encoding="utf-8", errors="replace") as stderr:
    lines = [line.rstrip("\n") for line in stderr]

bridge_line = next((line.strip() for line in lines if "[llvm2] bridge lowering complete" in line), "")
emit_line = next((line.strip() for line in lines if "error: LLVM2: failed to emit object(s)" in line), "")
if not emit_line:
    sys.exit(0)

match = re.search(r"for `([^`]+)`:\s*llvm2 pipeline failed for `([^`]+)`: (.+)$", emit_line)
if bridge_line:
    print(f"bridge-lowering: {bridge_line}")
if match:
    codegen_unit, function_name, cause = match.groups()
    print(f"codegen-unit: {codegen_unit}")
    print(f"function: {function_name}")
    print(f"cause: {cause}")
print(f"emit-error: {emit_line}")
PY
}

llvm2_emit_failure_signature() {
    local stderr_file="$1"

    python3 - "$stderr_file" <<'PY'
import re
import sys

stderr_path = sys.argv[1]
with open(stderr_path, "r", encoding="utf-8", errors="replace") as stderr:
    for raw_line in stderr:
        line = raw_line.strip()
        match = re.search(r"llvm2 pipeline failed for `([^`]+)`: (.+)$", line)
        if match:
            function_name, cause = match.groups()
            print(f"{function_name}: {cause}")
            sys.exit(0)

sys.exit(0)
PY
}

llvm2_emit_failure_brief() {
    local stderr_file="$1"
    local failure
    local codegen_unit
    local function_name
    local cause
    local value_id

    failure=$(sed -nE \
        's/.*failed to emit object\(s\) for `([^`]+)`: llvm2 pipeline failed for `([^`]+)`: (.*)$/\1|\2|\3/p' \
        "$stderr_file" | head -n1)
    [ -n "$failure" ] || return 0

    IFS='|' read -r codegen_unit function_name cause <<EOF
$failure
EOF

    value_id=$(printf '%s\n' "$cause" | sed -nE \
        's/.*instruction selection failed: value Value\(([0-9]+)\) not defined before use.*/\1/p' \
        | head -n1)
    if [ -n "$value_id" ]; then
        printf 'subtype=isel-use-before-def function=%s value_id=%s codegen_unit=%s\n' \
            "$function_name" "$value_id" "$codegen_unit"
        return 0
    fi

    cause=$(printf '%s\n' "$cause" | tr '\n' ' ' | sed -E 's/[[:space:]]+/ /g; s/[[:space:]]+$//')
    printf 'subtype=emit-failure function=%s codegen_unit=%s cause=%s\n' \
        "$function_name" "$codegen_unit" "$cause"
}

runtime_link_failure_brief() {
    local stderr_file="$1"
    local line
    local parsed
    local linker=""
    local linker_exit=""
    local undef_arch=""
    local undef_symbol=""
    local ref_symbol=""
    local ref_object=""
    local ref_object_role=""
    local native_bucket=""
    local ref_site=""
    local ref_object_base=""

    while IFS= read -r line; do
        if [ -z "$linker" ]; then
            parsed=$(printf '%s\n' "$line" | sed -nE \
                's/.*error: linking with `([^`]+)` failed: exit status: ([0-9]+).*/\1|\2/p')
            if [ -n "$parsed" ]; then
                IFS='|' read -r linker linker_exit <<EOF
$parsed
EOF
            fi
        fi

        if [ -z "$undef_arch" ]; then
            parsed=$(printf '%s\n' "$line" | sed -nE \
                's/^[[:space:]]*Undefined symbols for architecture ([^:]+):/\1/p')
            if [ -n "$parsed" ]; then
                undef_arch="$parsed"
                continue
            fi
        fi

        if [ -n "$undef_arch" ] && [ -z "$undef_symbol" ]; then
            parsed=$(printf '%s\n' "$line" | sed -nE \
                's/^[[:space:]]*"([^"]+)", referenced from:/\1/p')
            if [ -n "$parsed" ]; then
                undef_symbol="$parsed"
                continue
            fi
        fi

        if [ -n "$undef_symbol" ] && [ -z "$ref_symbol" ]; then
            parsed=$(printf '%s\n' "$line" | sed -nE \
                's/^[[:space:]]*([^[:space:]].*) in ([^[:space:]]+)$/\1|\2/p')
            if [ -n "$parsed" ]; then
                IFS='|' read -r ref_symbol ref_object <<EOF
$parsed
EOF
                case "$ref_object" in
                    *.allocator.*)
                        ref_object_role="allocator"
                        ;;
                    *.codegen_unit.*)
                        ref_object_role="codegen-unit"
                        ;;
                    *)
                        ref_object_role="other"
                        ;;
                esac
                break
            fi
        fi
    done < "$stderr_file"

    if [ -n "$undef_symbol" ]; then
        ref_object_base=$(basename "$ref_object" 2>/dev/null || true)
        case "$ref_object_role" in
            allocator|codegen-unit)
                if [ -n "$ref_symbol" ]; then
                    ref_site="$ref_symbol@$ref_object_role"
                else
                    ref_site="$ref_object_role"
                fi
                ;;
            *)
                if [ -n "$ref_symbol" ]; then
                    ref_site="$ref_symbol"
                elif [ -n "$ref_object_base" ]; then
                    ref_site="$ref_object_base"
                fi
                ;;
        esac

        case "$undef_symbol" in
            _std::*|_core::*|_alloc::*)
                native_bucket="std-surface"
                ;;
            __rust_alloc|__rust_alloc_zeroed|__rust_dealloc|__rust_realloc|__rg_*|__rdl_*)
                native_bucket="allocator-abi"
                ;;
            _rust_begin_unwind|_Unwind_*|__gxx_personality_v0|___gxx_personality_v0)
                native_bucket="panic-unwind"
                ;;
            _memcpy|_memmove|_memset|_memcmp|_bzero|_malloc|_calloc|_realloc|_free)
                native_bucket="libc-surface"
                ;;
            *)
                case "$ref_object_role" in
                    allocator)
                        native_bucket="allocator-fallout"
                        ;;
                    codegen-unit)
                        native_bucket="generic-codegen-unit"
                        ;;
                    *)
                        native_bucket="generic"
                        ;;
                esac
                ;;
        esac

        printf 'kind=linker-undefined-symbol'
        [ -n "$linker" ] && printf ' linker=%s' "$linker"
        [ -n "$linker_exit" ] && printf ' linker_exit=%s' "$linker_exit"
        [ -n "$undef_arch" ] && printf ' arch=%s' "$undef_arch"
        printf ' symbol=%s' "$undef_symbol"
        [ -n "$native_bucket" ] && printf ' bucket=%s' "$native_bucket"
        [ -n "$ref_site" ] && printf ' ref_site=%s' "$ref_site"
        printf '\n'
        return 0
    fi

    if [ -n "$linker" ]; then
        printf 'kind=linker-failure linker=%s' "$linker"
        [ -n "$linker_exit" ] && printf ' linker_exit=%s' "$linker_exit"
        printf '\n'
    fi
}

run_case \
    "metadata" \
    "$METADATA_STDERR" \
    --crate-type=lib \
    --crate-name=llvm2_smoke_meta \
    "$METADATA_INPUT" \
    --emit=metadata \
    -o "$METADATA_OUT"
METADATA_EXIT="$RUN_CASE_EXIT"
METADATA_OUTPUT="$RUN_CASE_OUTPUT"

run_case \
    "object" \
    "$OBJECT_STDERR" \
    --crate-type=bin \
    --crate-name=llvm2_checked_div_obj \
    "$BUG_INPUT" \
    --emit=obj \
    -o "$OBJECT_OUT"
OBJECT_EXIT="$RUN_CASE_EXIT"
OBJECT_OUTPUT="$RUN_CASE_OUTPUT"
OBJECT_EMIT_FAILURE_SUMMARY=$(llvm2_emit_failure_summary "$OBJECT_STDERR" || true)
OBJECT_EMIT_FAILURE_SIGNATURE=$(llvm2_emit_failure_signature "$OBJECT_STDERR" || true)
OBJECT_EMIT_FAILURE_BRIEF=$(llvm2_emit_failure_brief "$OBJECT_STDERR" || true)

run_case \
    "link" \
    "$LINK_STDERR" \
    --crate-type=bin \
    --crate-name=llvm2_checked_div_link \
    "$BUG_INPUT" \
    --emit=link \
    -o "$LINK_OUT"
LINK_EXIT="$RUN_CASE_EXIT"
LINK_OUTPUT="$RUN_CASE_OUTPUT"
LINK_EMIT_FAILURE_SUMMARY=$(llvm2_emit_failure_summary "$LINK_STDERR" || true)
LINK_EMIT_FAILURE_SIGNATURE=$(llvm2_emit_failure_signature "$LINK_STDERR" || true)
LINK_EMIT_FAILURE_BRIEF=$(llvm2_emit_failure_brief "$LINK_STDERR" || true)

if [ -n "$OBJECT_EMIT_FAILURE_SUMMARY" ]; then
    echo "--- [object] LLVM2 emit failure summary ---"
    echo "$OBJECT_EMIT_FAILURE_SUMMARY"
    echo "--- end [object] LLVM2 emit failure summary ---"
    echo
fi

if [ -n "$LINK_EMIT_FAILURE_SUMMARY" ]; then
    echo "--- [link] LLVM2 emit failure summary ---"
    echo "$LINK_EMIT_FAILURE_SUMMARY"
    echo "--- end [link] LLVM2 emit failure summary ---"
    echo
fi

if [ -n "$OBJECT_EMIT_FAILURE_SIGNATURE" ] && [ "$OBJECT_EMIT_FAILURE_SIGNATURE" = "$LINK_EMIT_FAILURE_SIGNATURE" ]; then
    echo "--- [checked-div] shared object/link emit failure signature ---"
    echo "$OBJECT_EMIT_FAILURE_SIGNATURE"
    echo "--- end [checked-div] shared object/link emit failure signature ---"
    echo
fi

run_case \
    "runtime-link" \
    "$RUNTIME_LINK_STDERR" \
    --crate-type=bin \
    --crate-name=llvm2_runtime_smoke \
    "$RUNTIME_INPUT" \
    --emit=link \
    -o "$RUNTIME_LINK_OUT"
RUNTIME_LINK_EXIT="$RUN_CASE_EXIT"
RUNTIME_LINK_OUTPUT="$RUN_CASE_OUTPUT"
RUNTIME_LINK_FAILURE_BRIEF=$(runtime_link_failure_brief "$RUNTIME_LINK_STDERR" || true)

run_case \
    "runtime-cf-link" \
    "$RUNTIME_CF_LINK_STDERR" \
    --crate-type=bin \
    --crate-name=llvm2_runtime_cf_smoke \
    "$RUNTIME_CF_INPUT" \
    --emit=link \
    -o "$RUNTIME_CF_LINK_OUT"
RUNTIME_CF_LINK_EXIT="$RUN_CASE_EXIT"
RUNTIME_CF_LINK_OUTPUT="$RUN_CASE_OUTPUT"
RUNTIME_CF_LINK_FAILURE_BRIEF=$(runtime_link_failure_brief "$RUNTIME_CF_LINK_STDERR" || true)

run_case \
    "runtime-abort-link" \
    "$RUNTIME_ABORT_LINK_STDERR" \
    --crate-type=bin \
    --crate-name=llvm2_runtime_abort_smoke \
    "$RUNTIME_ABORT_INPUT" \
    --emit=link \
    -o "$RUNTIME_ABORT_LINK_OUT"
RUNTIME_ABORT_LINK_EXIT="$RUN_CASE_EXIT"
RUNTIME_ABORT_LINK_OUTPUT="$RUN_CASE_OUTPUT"
RUNTIME_ABORT_LINK_FAILURE_BRIEF=$(runtime_link_failure_brief "$RUNTIME_ABORT_LINK_STDERR" || true)
RUNTIME_ABORT_LINK_EMIT_FAILURE_SIGNATURE=$(llvm2_emit_failure_signature "$RUNTIME_ABORT_LINK_STDERR" || true)
RUNTIME_ABORT_LINK_EMIT_FAILURE_BRIEF=$(llvm2_emit_failure_brief "$RUNTIME_ABORT_LINK_STDERR" || true)

run_case \
    "runtime-overflow-link" \
    "$RUNTIME_OVERFLOW_LINK_STDERR" \
    --crate-type=bin \
    --crate-name=llvm2_runtime_overflow_smoke \
    -C overflow-checks=yes \
    "$RUNTIME_OVERFLOW_INPUT" \
    --emit=link \
    -o "$RUNTIME_OVERFLOW_LINK_OUT"
RUNTIME_OVERFLOW_LINK_EXIT="$RUN_CASE_EXIT"
RUNTIME_OVERFLOW_LINK_OUTPUT="$RUN_CASE_OUTPUT"
RUNTIME_OVERFLOW_LINK_FAILURE_BRIEF=$(runtime_link_failure_brief "$RUNTIME_OVERFLOW_LINK_STDERR" || true)
RUNTIME_OVERFLOW_LINK_EMIT_FAILURE_SIGNATURE=$(llvm2_emit_failure_signature "$RUNTIME_OVERFLOW_LINK_STDERR" || true)
RUNTIME_OVERFLOW_LINK_EMIT_FAILURE_BRIEF=$(llvm2_emit_failure_brief "$RUNTIME_OVERFLOW_LINK_STDERR" || true)

RUNTIME_EXIT=125
RUNTIME_OUTPUT=""
RUNTIME_ERROR_OUTPUT=""
RUNTIME_DISASM_OUTPUT=""
RUNTIME_MAIN_ENTRY_ADDR=""
RUNTIME_MAIN_ENTRY_TARGETS=""
RUNTIME_MAIN_BRANCH_SUMMARY=""
RUNTIME_SELF_CALL_SIGNATURE=""
RUNTIME_FIRST_CALL_SITE=""
RUNTIME_SKIP_REASON=""
run_runtime_binary_case "runtime" "$RUNTIME_LINK_EXIT" "$RUNTIME_LINK_OUT" "$RUNTIME_STDOUT" "$RUNTIME_STDERR"
RUNTIME_EXIT="$RUNTIME_CASE_EXIT"
RUNTIME_OUTPUT="$RUNTIME_CASE_OUTPUT"
RUNTIME_ERROR_OUTPUT="$RUNTIME_CASE_ERROR_OUTPUT"
RUNTIME_DISASM_OUTPUT="$RUNTIME_CASE_DISASM_OUTPUT"
RUNTIME_MAIN_ENTRY_ADDR="$RUNTIME_CASE_MAIN_ENTRY_ADDR"
RUNTIME_MAIN_ENTRY_TARGETS="$RUNTIME_CASE_MAIN_ENTRY_TARGETS"
RUNTIME_MAIN_BRANCH_SUMMARY="$RUNTIME_CASE_MAIN_BRANCH_SUMMARY"
RUNTIME_SELF_CALL_SIGNATURE="$RUNTIME_CASE_SELF_CALL_SIGNATURE"
RUNTIME_FIRST_CALL_SITE="$RUNTIME_CASE_FIRST_CALL_SITE"
RUNTIME_SKIP_REASON="$RUNTIME_CASE_SKIP_REASON"

RUNTIME_CF_EXIT=125
RUNTIME_CF_OUTPUT=""
RUNTIME_CF_ERROR_OUTPUT=""
RUNTIME_CF_DISASM_OUTPUT=""
RUNTIME_CF_MAIN_ENTRY_ADDR=""
RUNTIME_CF_MAIN_ENTRY_TARGETS=""
RUNTIME_CF_MAIN_BRANCH_SUMMARY=""
RUNTIME_CF_SELF_CALL_SIGNATURE=""
RUNTIME_CF_FIRST_CALL_SITE=""
RUNTIME_CF_SKIP_REASON=""

run_runtime_binary_case "runtime-cf" "$RUNTIME_CF_LINK_EXIT" "$RUNTIME_CF_LINK_OUT" "$RUNTIME_CF_STDOUT" "$RUNTIME_CF_STDERR"
RUNTIME_CF_EXIT="$RUNTIME_CASE_EXIT"
RUNTIME_CF_OUTPUT="$RUNTIME_CASE_OUTPUT"
RUNTIME_CF_ERROR_OUTPUT="$RUNTIME_CASE_ERROR_OUTPUT"
RUNTIME_CF_DISASM_OUTPUT="$RUNTIME_CASE_DISASM_OUTPUT"
RUNTIME_CF_MAIN_ENTRY_ADDR="$RUNTIME_CASE_MAIN_ENTRY_ADDR"
RUNTIME_CF_MAIN_ENTRY_TARGETS="$RUNTIME_CASE_MAIN_ENTRY_TARGETS"
RUNTIME_CF_MAIN_BRANCH_SUMMARY="$RUNTIME_CASE_MAIN_BRANCH_SUMMARY"
RUNTIME_CF_SELF_CALL_SIGNATURE="$RUNTIME_CASE_SELF_CALL_SIGNATURE"
RUNTIME_CF_FIRST_CALL_SITE="$RUNTIME_CASE_FIRST_CALL_SITE"
RUNTIME_CF_SKIP_REASON="$RUNTIME_CASE_SKIP_REASON"

RUNTIME_ABORT_EXIT=125
RUNTIME_ABORT_OUTPUT=""
RUNTIME_ABORT_ERROR_OUTPUT=""
RUNTIME_ABORT_SKIP_REASON=""

run_runtime_abnormal_case "runtime-abort" "$RUNTIME_ABORT_LINK_EXIT" "$RUNTIME_ABORT_LINK_OUT" "$RUNTIME_ABORT_STDOUT" "$RUNTIME_ABORT_STDERR"
RUNTIME_ABORT_EXIT="$RUNTIME_ABNORMAL_EXIT"
RUNTIME_ABORT_OUTPUT="$RUNTIME_ABNORMAL_OUTPUT"
RUNTIME_ABORT_ERROR_OUTPUT="$RUNTIME_ABNORMAL_ERROR_OUTPUT"
RUNTIME_ABORT_SKIP_REASON="$RUNTIME_ABNORMAL_SKIP_REASON"
RUNTIME_ABORT_FAILURE_BRIEF=$(runtime_abnormal_exit_brief "$RUNTIME_ABORT_EXIT")

RUNTIME_OVERFLOW_EXIT=125
RUNTIME_OVERFLOW_OUTPUT=""
RUNTIME_OVERFLOW_ERROR_OUTPUT=""
RUNTIME_OVERFLOW_DISASM_OUTPUT=""
RUNTIME_OVERFLOW_MAIN_ENTRY_ADDR=""
RUNTIME_OVERFLOW_MAIN_ENTRY_TARGETS=""
RUNTIME_OVERFLOW_MAIN_BRANCH_SUMMARY=""
RUNTIME_OVERFLOW_SELF_CALL_SIGNATURE=""
RUNTIME_OVERFLOW_FIRST_CALL_SITE=""
RUNTIME_OVERFLOW_SKIP_REASON=""

run_runtime_binary_case "runtime-overflow" "$RUNTIME_OVERFLOW_LINK_EXIT" "$RUNTIME_OVERFLOW_LINK_OUT" "$RUNTIME_OVERFLOW_STDOUT" "$RUNTIME_OVERFLOW_STDERR"
RUNTIME_OVERFLOW_EXIT="$RUNTIME_CASE_EXIT"
RUNTIME_OVERFLOW_OUTPUT="$RUNTIME_CASE_OUTPUT"
RUNTIME_OVERFLOW_ERROR_OUTPUT="$RUNTIME_CASE_ERROR_OUTPUT"
RUNTIME_OVERFLOW_DISASM_OUTPUT="$RUNTIME_CASE_DISASM_OUTPUT"
RUNTIME_OVERFLOW_MAIN_ENTRY_ADDR="$RUNTIME_CASE_MAIN_ENTRY_ADDR"
RUNTIME_OVERFLOW_MAIN_ENTRY_TARGETS="$RUNTIME_CASE_MAIN_ENTRY_TARGETS"
RUNTIME_OVERFLOW_MAIN_BRANCH_SUMMARY="$RUNTIME_CASE_MAIN_BRANCH_SUMMARY"
RUNTIME_OVERFLOW_SELF_CALL_SIGNATURE="$RUNTIME_CASE_SELF_CALL_SIGNATURE"
RUNTIME_OVERFLOW_FIRST_CALL_SITE="$RUNTIME_CASE_FIRST_CALL_SITE"
RUNTIME_OVERFLOW_SKIP_REASON="$RUNTIME_CASE_SKIP_REASON"
RUNTIME_OVERFLOW_FAILURE_BRIEF=$(runtime_abnormal_exit_brief "$RUNTIME_OVERFLOW_EXIT")

if [ -n "$OBJECT_EMIT_FAILURE_SIGNATURE" ] || [ -n "$LINK_EMIT_FAILURE_SIGNATURE" ] || [ "$RUNTIME_EXIT" -ne 0 ] || [ -n "$RUNTIME_SKIP_REASON" ] || [ "$RUNTIME_CF_EXIT" -ne 0 ] || [ -n "$RUNTIME_CF_SKIP_REASON" ] || [ -n "$RUNTIME_ABORT_SKIP_REASON" ] || [ "$RUNTIME_ABORT_EXIT" -eq 0 ] || [ "$RUNTIME_ABORT_EXIT" -eq 124 ] || [ -n "$RUNTIME_OVERFLOW_SKIP_REASON" ] || [ "$RUNTIME_OVERFLOW_EXIT" -eq 0 ] || [ "$RUNTIME_OVERFLOW_EXIT" -eq 124 ]; then
    echo "--- [llvm2] failure mode summary ---"

    if [ -n "$OBJECT_EMIT_FAILURE_SIGNATURE" ]; then
        echo "phase=object kind=compile-time-emit exit=$OBJECT_EXIT ${OBJECT_EMIT_FAILURE_BRIEF:-signature=$OBJECT_EMIT_FAILURE_SIGNATURE}"
    fi
    if [ -n "$LINK_EMIT_FAILURE_SIGNATURE" ]; then
        echo "phase=link kind=compile-time-emit exit=$LINK_EXIT ${LINK_EMIT_FAILURE_BRIEF:-signature=$LINK_EMIT_FAILURE_SIGNATURE}"
    fi
    if [ -n "$OBJECT_EMIT_FAILURE_SIGNATURE" ] && [ "$OBJECT_EMIT_FAILURE_SIGNATURE" = "$LINK_EMIT_FAILURE_SIGNATURE" ]; then
        echo "compile-time shared-signature phases=object,link signature=$OBJECT_EMIT_FAILURE_SIGNATURE"
    fi

    if [ -n "$RUNTIME_LINK_FAILURE_BRIEF" ]; then
        echo "phase=runtime-link exit=$RUNTIME_LINK_EXIT $RUNTIME_LINK_FAILURE_BRIEF"
    fi
    if [ -n "$RUNTIME_CF_LINK_FAILURE_BRIEF" ]; then
        echo "phase=runtime-cf-link exit=$RUNTIME_CF_LINK_EXIT $RUNTIME_CF_LINK_FAILURE_BRIEF"
    fi
    if [ -n "$RUNTIME_ABORT_LINK_EMIT_FAILURE_SIGNATURE" ]; then
        echo "phase=runtime-abort-link kind=compile-time-emit exit=$RUNTIME_ABORT_LINK_EXIT ${RUNTIME_ABORT_LINK_EMIT_FAILURE_BRIEF:-signature=$RUNTIME_ABORT_LINK_EMIT_FAILURE_SIGNATURE}"
    elif [ -n "$RUNTIME_ABORT_LINK_FAILURE_BRIEF" ]; then
        echo "phase=runtime-abort-link exit=$RUNTIME_ABORT_LINK_EXIT $RUNTIME_ABORT_LINK_FAILURE_BRIEF"
    fi
    if [ -n "$RUNTIME_OVERFLOW_LINK_EMIT_FAILURE_SIGNATURE" ]; then
        echo "phase=runtime-overflow-link kind=compile-time-emit exit=$RUNTIME_OVERFLOW_LINK_EXIT ${RUNTIME_OVERFLOW_LINK_EMIT_FAILURE_BRIEF:-signature=$RUNTIME_OVERFLOW_LINK_EMIT_FAILURE_SIGNATURE}"
    elif [ -n "$RUNTIME_OVERFLOW_LINK_FAILURE_BRIEF" ]; then
        echo "phase=runtime-overflow-link exit=$RUNTIME_OVERFLOW_LINK_EXIT $RUNTIME_OVERFLOW_LINK_FAILURE_BRIEF"
    fi

    if [ -n "$RUNTIME_SKIP_REASON" ]; then
        echo "phase=runtime kind=not-entered detail=$RUNTIME_SKIP_REASON"
    elif [ -n "$RUNTIME_SELF_CALL_SIGNATURE" ]; then
        echo "phase=runtime kind=self-call-hang exit=$RUNTIME_EXIT signature=$RUNTIME_SELF_CALL_SIGNATURE"
    elif [ "$RUNTIME_EXIT" -eq 124 ]; then
        echo "phase=runtime kind=timeout exit=$RUNTIME_EXIT detail=timeout after 5 seconds"
    elif [ "$RUNTIME_EXIT" -ne 0 ]; then
        echo "phase=runtime kind=runtime-failure exit=$RUNTIME_EXIT"
    fi

    if [ -n "$RUNTIME_CF_SKIP_REASON" ]; then
        echo "phase=runtime-cf kind=not-entered detail=$RUNTIME_CF_SKIP_REASON"
    elif [ -n "$RUNTIME_CF_SELF_CALL_SIGNATURE" ]; then
        echo "phase=runtime-cf kind=self-call-hang exit=$RUNTIME_CF_EXIT signature=$RUNTIME_CF_SELF_CALL_SIGNATURE"
    elif [ "$RUNTIME_CF_EXIT" -eq 124 ]; then
        echo "phase=runtime-cf kind=timeout exit=$RUNTIME_CF_EXIT detail=timeout after 5 seconds"
    elif [ "$RUNTIME_CF_EXIT" -ne 0 ]; then
        echo "phase=runtime-cf kind=runtime-failure exit=$RUNTIME_CF_EXIT"
    fi

    if [ -n "$RUNTIME_ABORT_SKIP_REASON" ]; then
        echo "phase=runtime-abort kind=not-entered detail=$RUNTIME_ABORT_SKIP_REASON"
    elif [ -n "$RUNTIME_ABORT_FAILURE_BRIEF" ]; then
        echo "phase=runtime-abort $RUNTIME_ABORT_FAILURE_BRIEF"
    fi

    if [ -n "$RUNTIME_OVERFLOW_SKIP_REASON" ]; then
        echo "phase=runtime-overflow kind=not-entered detail=$RUNTIME_OVERFLOW_SKIP_REASON"
    elif [ -n "$RUNTIME_OVERFLOW_SELF_CALL_SIGNATURE" ]; then
        echo "phase=runtime-overflow kind=self-call-hang exit=$RUNTIME_OVERFLOW_EXIT signature=$RUNTIME_OVERFLOW_SELF_CALL_SIGNATURE"
    elif [ -n "$RUNTIME_OVERFLOW_FAILURE_BRIEF" ]; then
        echo "phase=runtime-overflow $RUNTIME_OVERFLOW_FAILURE_BRIEF"
    fi

    echo "--- end [llvm2] failure mode summary ---"
    echo
fi

# --- Assertions ---
PASS=0
FAIL=0

check() {
    local desc="$1"
    local haystack="$2"
    local pattern="$3"
    if echo "$haystack" | grep -qE "$pattern"; then
        echo "PASS: $desc"
        PASS=$((PASS + 1))
    else
        echo "FAIL: $desc (pattern not found: $pattern)"
        FAIL=$((FAIL + 1))
    fi
}

check_absent() {
    local desc="$1"
    local haystack="$2"
    local pattern="$3"
    if echo "$haystack" | grep -qE "$pattern"; then
        echo "FAIL: $desc (unexpected pattern found: $pattern)"
        FAIL=$((FAIL + 1))
    else
        echo "PASS: $desc"
        PASS=$((PASS + 1))
    fi
}

check_exit() {
    local desc="$1"
    local actual="$2"
    local expected="$3"
    if [ "$actual" -eq "$expected" ]; then
        echo "PASS: $desc (exit=$actual)"
        PASS=$((PASS + 1))
    else
        echo "FAIL: $desc (expected exit=$expected, got exit=$actual)"
        FAIL=$((FAIL + 1))
    fi
}

check_ne() {
    local desc="$1"
    local actual="$2"
    local unexpected="$3"
    if [ "$actual" -ne "$unexpected" ]; then
        echo "PASS: $desc (value=$actual != $unexpected)"
        PASS=$((PASS + 1))
    else
        echo "FAIL: $desc (value unexpectedly == $unexpected)"
        FAIL=$((FAIL + 1))
    fi
}

check_file() {
    local desc="$1"
    local path="$2"
    if [ -s "$path" ]; then
        echo "PASS: $desc ($path)"
        PASS=$((PASS + 1))
    else
        echo "FAIL: $desc ($path missing or empty)"
        FAIL=$((FAIL + 1))
    fi
}

check_missing_file() {
    local desc="$1"
    local path="$2"
    if [ ! -e "$path" ] || [ ! -s "$path" ]; then
        echo "PASS: $desc ($path)"
        PASS=$((PASS + 1))
    else
        echo "FAIL: $desc ($path unexpectedly exists and is non-empty)"
        FAIL=$((FAIL + 1))
    fi
}

check_object_outputs() {
    local desc="$1"
    local primary="$2"
    local split_glob="$3"
    local split_matches=()
    shopt -s nullglob
    split_matches=($split_glob)
    shopt -u nullglob
    if [ -s "$primary" ]; then
        echo "PASS: $desc ($primary)"
        PASS=$((PASS + 1))
    elif [ ${#split_matches[@]} -gt 0 ]; then
        echo "PASS: $desc (${#split_matches[@]} split object(s) matched $split_glob)"
        PASS=$((PASS + 1))
    else
        echo "FAIL: $desc ($primary missing and no split objects matched $split_glob)"
        FAIL=$((FAIL + 1))
    fi
}

# Numeric assertion: extract a number from output matching pattern, check >= threshold
check_ge() {
    local desc="$1"
    local haystack="$2"
    local pattern="$3"
    local threshold="$4"
    local value
    value=$(printf '%s\n' "$haystack" | grep -oE "$pattern" | grep -oE '[0-9]+' | head -1 || true)
    if [ -z "$value" ]; then
        echo "FAIL: $desc (pattern not found: $pattern)"
        FAIL=$((FAIL + 1))
    elif [ "$value" -ge "$threshold" ]; then
        echo "PASS: $desc (value=$value >= $threshold)"
        PASS=$((PASS + 1))
    else
        echo "FAIL: $desc (value=$value < threshold=$threshold)"
        FAIL=$((FAIL + 1))
    fi
}

check_eq() {
    local desc="$1"
    local haystack="$2"
    local pattern="$3"
    local expected="$4"
    local value
    value=$(printf '%s\n' "$haystack" | grep -oE "$pattern" | grep -oE '[0-9]+' | head -1 || true)
    if [ -z "$value" ]; then
        echo "FAIL: $desc (pattern not found: $pattern)"
        FAIL=$((FAIL + 1))
    elif [ "$value" -eq "$expected" ]; then
        echo "PASS: $desc (value=$value == $expected)"
        PASS=$((PASS + 1))
    else
        echo "FAIL: $desc (value=$value != expected=$expected)"
        FAIL=$((FAIL + 1))
    fi
}

# Core assertions
check_exit "Metadata compilation succeeds (exit 0)" "$METADATA_EXIT" 0
check_absent "Metadata path does not run LLVM2 MIR extraction" "$METADATA_OUTPUT" "\\[llvm2\\] MIR extraction complete"
check_absent "Metadata path does not run LLVM2 bridge lowering" "$METADATA_OUTPUT" "\\[llvm2\\] bridge lowering complete"
check_file "Metadata output is materialized" "$METADATA_OUT"

check_exit "Object compilation succeeds (exit 0)" "$OBJECT_EXIT" 0
check "Object MIR extraction diagnostic present" "$OBJECT_OUTPUT" "\\[llvm2\\] MIR extraction complete"
check_ge "Object path extracts at least 2 functions" "$OBJECT_OUTPUT" "extracted=[0-9]+" 2
check "Object bridge lowering diagnostic present" "$OBJECT_OUTPUT" "\\[llvm2\\] bridge lowering complete"
check_ge "Object path lowers at least 2 functions" "$OBJECT_OUTPUT" "lowered=[0-9]+" 2
check_eq "Object path reports zero lowering failures before emission" "$OBJECT_OUTPUT" "failures=[0-9]+" 0
check_object_outputs \
    "Object output is materialized" \
    "$OBJECT_OUT" \
    "${OBJECT_OUT%.o}".*.rcgu.o

check_exit "Link compilation succeeds (exit 0)" "$LINK_EXIT" 0
check "Link MIR extraction diagnostic present" "$LINK_OUTPUT" "\\[llvm2\\] MIR extraction complete"
check_ge "Link path extracts at least 2 functions" "$LINK_OUTPUT" "extracted=[0-9]+" 2
check "Link bridge lowering diagnostic present" "$LINK_OUTPUT" "\\[llvm2\\] bridge lowering complete"
check_ge "Link path lowers at least 2 functions" "$LINK_OUTPUT" "lowered=[0-9]+" 2
check_eq "Link path reports zero lowering failures before emission" "$LINK_OUTPUT" "failures=[0-9]+" 0
check_file "Linked binary is materialized" "$LINK_OUT"

check_exit "Runtime-link compilation succeeds (exit 0)" "$RUNTIME_LINK_EXIT" 0
check "Runtime-link MIR extraction diagnostic present" "$RUNTIME_LINK_OUTPUT" "\\[llvm2\\] MIR extraction complete"
check_ge "Runtime-link path extracts at least 1 function" "$RUNTIME_LINK_OUTPUT" "extracted=[0-9]+" 1
check "Runtime-link bridge lowering diagnostic present" "$RUNTIME_LINK_OUTPUT" "\\[llvm2\\] bridge lowering complete"
check_ge "Runtime-link path lowers at least 1 function" "$RUNTIME_LINK_OUTPUT" "lowered=[0-9]+" 1
check_eq "Runtime-link path reports zero lowering failures before emission" "$RUNTIME_LINK_OUTPUT" "failures=[0-9]+" 0
check_file "Runtime-linked binary is materialized" "$RUNTIME_LINK_OUT"
check_exit "Runtime-linked binary succeeds (exit 0)" "$RUNTIME_EXIT" 0

check_exit "Runtime-cf-link compilation succeeds (exit 0)" "$RUNTIME_CF_LINK_EXIT" 0
check "Runtime-cf-link MIR extraction diagnostic present" "$RUNTIME_CF_LINK_OUTPUT" "\\[llvm2\\] MIR extraction complete"
check_ge "Runtime-cf-link path extracts at least 4 functions" "$RUNTIME_CF_LINK_OUTPUT" "extracted=[0-9]+" 4
check "Runtime-cf-link bridge lowering diagnostic present" "$RUNTIME_CF_LINK_OUTPUT" "\\[llvm2\\] bridge lowering complete"
check_ge "Runtime-cf-link path lowers at least 4 functions" "$RUNTIME_CF_LINK_OUTPUT" "lowered=[0-9]+" 4
check_eq "Runtime-cf-link path reports zero lowering failures before emission" "$RUNTIME_CF_LINK_OUTPUT" "failures=[0-9]+" 0
check_file "Runtime-cf-linked binary is materialized" "$RUNTIME_CF_LINK_OUT"
check_exit "Runtime-cf-linked binary succeeds (exit 0)" "$RUNTIME_CF_EXIT" 0

check_exit "Runtime-abort-link compilation succeeds (exit 0)" "$RUNTIME_ABORT_LINK_EXIT" 0
check "Runtime-abort-link MIR extraction diagnostic present" "$RUNTIME_ABORT_LINK_OUTPUT" "\\[llvm2\\] MIR extraction complete"
check_ge "Runtime-abort-link path extracts at least 1 function" "$RUNTIME_ABORT_LINK_OUTPUT" "extracted=[0-9]+" 1
check "Runtime-abort-link bridge lowering diagnostic present" "$RUNTIME_ABORT_LINK_OUTPUT" "\\[llvm2\\] bridge lowering complete"
check_ge "Runtime-abort-link path lowers at least 1 function" "$RUNTIME_ABORT_LINK_OUTPUT" "lowered=[0-9]+" 1
check_eq "Runtime-abort-link path reports zero lowering failures before emission" "$RUNTIME_ABORT_LINK_OUTPUT" "failures=[0-9]+" 0
check_file "Runtime-abort-linked binary is materialized" "$RUNTIME_ABORT_LINK_OUT"
check_ne "Runtime-abort execution is entered" "$RUNTIME_ABORT_EXIT" 125
if [ "$RUNTIME_ABORT_EXIT" -ne 125 ]; then
    check_ne "Runtime-abort-linked binary terminates abnormally" "$RUNTIME_ABORT_EXIT" 0
    check_ne "Runtime-abort-linked binary does not time out" "$RUNTIME_ABORT_EXIT" 124
    check "Runtime-abort-linked binary is classified as abort signal" "$RUNTIME_ABORT_FAILURE_BRIEF" "kind=abort-signal"
    check "Runtime-abort-linked binary reports SIGABRT" "$RUNTIME_ABORT_FAILURE_BRIEF" "signal=SIGABRT"
fi

check_exit "Runtime-overflow-link compilation succeeds (exit 0)" "$RUNTIME_OVERFLOW_LINK_EXIT" 0
check "Runtime-overflow-link MIR extraction diagnostic present" "$RUNTIME_OVERFLOW_LINK_OUTPUT" "\\[llvm2\\] MIR extraction complete"
check_ge "Runtime-overflow-link path extracts at least 2 functions" "$RUNTIME_OVERFLOW_LINK_OUTPUT" "extracted=[0-9]+" 2
check "Runtime-overflow-link bridge lowering diagnostic present" "$RUNTIME_OVERFLOW_LINK_OUTPUT" "\\[llvm2\\] bridge lowering complete"
check_ge "Runtime-overflow-link path lowers at least 2 functions" "$RUNTIME_OVERFLOW_LINK_OUTPUT" "lowered=[0-9]+" 2
check_eq "Runtime-overflow-link path reports zero lowering failures before emission" "$RUNTIME_OVERFLOW_LINK_OUTPUT" "failures=[0-9]+" 0
check_file "Runtime-overflow-linked binary is materialized" "$RUNTIME_OVERFLOW_LINK_OUT"
check_ne "Runtime-overflow execution is entered" "$RUNTIME_OVERFLOW_EXIT" 125
if [ "$RUNTIME_OVERFLOW_EXIT" -ne 125 ]; then
    check_ne "Runtime-overflow-linked binary terminates abnormally" "$RUNTIME_OVERFLOW_EXIT" 0
    check_ne "Runtime-overflow-linked binary does not time out" "$RUNTIME_OVERFLOW_EXIT" 124
    check "Runtime-overflow-linked binary is classified as abort signal" "$RUNTIME_OVERFLOW_FAILURE_BRIEF" "kind=abort-signal"
    check "Runtime-overflow-linked binary reports SIGABRT" "$RUNTIME_OVERFLOW_FAILURE_BRIEF" "signal=SIGABRT"
fi

echo
echo "Results: $PASS passed, $FAIL failed"
echo

if [ $FAIL -gt 0 ]; then
    echo "FAILED"
    exit 1
fi

echo "ALL TESTS PASSED"
