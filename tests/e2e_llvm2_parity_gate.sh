#!/bin/bash
# Differential acceptance scaffold: default LLVM vs opt-in LLVM2.
#
# Contract:
# - The stage1 compiler's default backend remains the required baseline.
# - LLVM2 is evaluated against a small focused corpus that exercises current
#   object/link/runtime failure modes without pretending to cover the full
#   backend surface.
# - By default this script reports LLVM2 mismatches but only fails if the
#   default LLVM baseline is broken. Set TRUST_LLVM2_PARITY_MODE=enforce to
#   make LLVM2 mismatches fatal.
#
# Usage:
#   ./tests/e2e_llvm2_parity_gate.sh
#   ./tests/e2e_llvm2_parity_gate.sh runtime
#   TRUST_LLVM2_PARITY_MODE=enforce ./tests/e2e_llvm2_parity_gate.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
FILTER="${1:-}"
PARITY_MODE="${TRUST_LLVM2_PARITY_MODE:-report}"
KEEP_TMP="${TRUST_LLVM2_PARITY_KEEP_TMP:-0}"

case "$PARITY_MODE" in
    report|enforce)
        ;;
    *)
        echo "FAIL: TRUST_LLVM2_PARITY_MODE must be report or enforce (got: $PARITY_MODE)" >&2
        exit 2
        ;;
esac

echo "=== tRust E2E Test: LLVM default vs LLVM2 parity gate ==="
echo "mode: $PARITY_MODE"
if [ -n "$FILTER" ]; then
    echo "filter: $FILTER"
fi
echo

find_rustc() {
    if [ -n "${TRUSTC:-}" ] && [ -x "${TRUSTC}" ]; then
        echo "${TRUSTC}"
        return 0
    fi
    local candidates=(
        "$TRUST_ROOT/build/host/stage1/bin/trustc"
        "$TRUST_ROOT/build/aarch64-apple-darwin/stage1/bin/trustc"
        "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage1/bin/trustc"
        "$TRUST_ROOT/build/x86_64-apple-darwin/stage1/bin/trustc"
        "$TRUST_ROOT/build/host/stage1/bin/rustc"
        "$TRUST_ROOT/build/aarch64-apple-darwin/stage1/bin/rustc"
        "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage1/bin/rustc"
        "$TRUST_ROOT/build/x86_64-apple-darwin/stage1/bin/rustc"
    )
    local candidate
    for candidate in "${candidates[@]}"; do
        if [ -x "$candidate" ]; then
            echo "$candidate"
            return 0
        fi
    done

    return 1
}

find_llvm2_backend() {
    local backend_dir="$1"
    local candidate
    local candidates=()

    shopt -s nullglob
    candidates=(
        "$backend_dir"/librustc_codegen_llvm2*.dylib
        "$backend_dir"/librustc_codegen_llvm2*.so
        "$backend_dir"/rustc_codegen_llvm2*.dll
    )
    shopt -u nullglob

    for candidate in "${candidates[@]}"; do
        if [ -f "$candidate" ]; then
            echo "$candidate"
            return 0
        fi
    done

    return 1
}

matches_filter() {
    local case_id="$1"
    local label="$2"

    if [ -z "$FILTER" ]; then
        return 0
    fi

    case "$case_id $label" in
        *"$FILTER"*)
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}

append_line() {
    local var_name="$1"
    local line="$2"
    local current="${!var_name-}"

    if [ -n "$current" ]; then
        printf -v "$var_name" '%s\n%s' "$current" "$line"
    else
        printf -v "$var_name" '%s' "$line"
    fi
}

signal_name_for_exit() {
    local exit_code="$1"
    local signal_num

    if [ "$exit_code" -lt 128 ]; then
        return 1
    fi

    signal_num=$((exit_code - 128))
    case "$signal_num" in
        1) printf 'SIGHUP\n' ;;
        2) printf 'SIGINT\n' ;;
        3) printf 'SIGQUIT\n' ;;
        4) printf 'SIGILL\n' ;;
        5) printf 'SIGTRAP\n' ;;
        6) printf 'SIGABRT\n' ;;
        7) printf 'SIGEMT\n' ;;
        8) printf 'SIGFPE\n' ;;
        9) printf 'SIGKILL\n' ;;
        10) printf 'SIGBUS\n' ;;
        11) printf 'SIGSEGV\n' ;;
        12) printf 'SIGSYS\n' ;;
        13) printf 'SIGPIPE\n' ;;
        14) printf 'SIGALRM\n' ;;
        15) printf 'SIGTERM\n' ;;
        *) printf 'SIGUNKNOWN\n' ;;
    esac
}

emit_failure_brief() {
    local stderr_file="$1"
    local failure
    local codegen_unit
    local function_name
    local cause

    failure=$(sed -nE \
        's/.*failed to emit object\(s\) for `([^`]+)`: llvm2 pipeline failed for `([^`]+)`: (.*)$/\1|\2|\3/p' \
        "$stderr_file" | head -n1)
    [ -n "$failure" ] || return 0

    IFS='|' read -r codegen_unit function_name cause <<EOF
$failure
EOF

    cause=$(printf '%s\n' "$cause" | tr '\n' ' ' | sed -E 's/[[:space:]]+/ /g; s/[[:space:]]+$//')
    printf 'emit-failure function=%s codegen_unit=%s cause=%s\n' \
        "$function_name" "$codegen_unit" "$cause"
}

link_failure_brief() {
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

        printf 'link-failure symbol=%s bucket=%s' "$undef_symbol" "$native_bucket"
        [ -n "$linker" ] && printf ' linker=%s' "$linker"
        [ -n "$linker_exit" ] && printf ' linker_exit=%s' "$linker_exit"
        [ -n "$undef_arch" ] && printf ' arch=%s' "$undef_arch"
        [ -n "$ref_site" ] && printf ' ref_site=%s' "$ref_site"
        printf '\n'
        return 0
    fi

    if [ -n "$linker" ]; then
        printf 'link-failure linker=%s' "$linker"
        [ -n "$linker_exit" ] && printf ' linker_exit=%s' "$linker_exit"
        printf '\n'
    fi
}

compile_failure_brief() {
    local stderr_file="$1"
    local brief

    brief=$(emit_failure_brief "$stderr_file" || true)
    if [ -n "$brief" ]; then
        printf '%s\n' "$brief"
        return 0
    fi

    brief=$(link_failure_brief "$stderr_file" || true)
    if [ -n "$brief" ]; then
        printf '%s\n' "$brief"
        return 0
    fi

    brief=$(sed -nE 's/^[[:space:]]*error: (.*)$/\1/p' "$stderr_file" | head -n1)
    if [ -n "$brief" ]; then
        printf 'error=%s\n' "$brief"
    fi
}

run_compile() {
    local backend="$1"
    local stderr_file="$2"
    local out_path="$3"
    local split_glob="$4"
    shift 4

    local cmd=("$RUSTC")
    local split_matches=()

    if [ "$backend" = "llvm2" ]; then
        cmd+=(-Z codegen-backend=llvm2)
    fi
    cmd+=(--edition 2021 "$@" -o "$out_path")

    COMPILE_EXIT=0
    if [ "$backend" = "llvm2" ]; then
        RUSTC_LOG="rustc_codegen_llvm2=info" "${cmd[@]}" >/dev/null 2>"$stderr_file" || COMPILE_EXIT=$?
    else
        "${cmd[@]}" >/dev/null 2>"$stderr_file" || COMPILE_EXIT=$?
    fi

    COMPILE_STDERR_FILE="$stderr_file"
    COMPILE_STDERR=$(cat "$stderr_file")
    COMPILE_HAS_OUTPUT=0
    COMPILE_OUTPUT_DESC="$out_path"
    COMPILE_BRIEF=$(compile_failure_brief "$stderr_file" || true)

    if [ -s "$out_path" ]; then
        COMPILE_HAS_OUTPUT=1
    elif [ -n "$split_glob" ]; then
        shopt -s nullglob
        split_matches=($split_glob)
        shopt -u nullglob
        if [ "${#split_matches[@]}" -gt 0 ]; then
            COMPILE_HAS_OUTPUT=1
            COMPILE_OUTPUT_DESC="${#split_matches[@]} split output(s) matched $split_glob"
        fi
    fi

    if [ "$COMPILE_EXIT" -eq 0 ] && [ "$COMPILE_HAS_OUTPUT" -eq 1 ]; then
        COMPILE_CLASS="success"
    elif [ "$COMPILE_EXIT" -eq 0 ]; then
        COMPILE_CLASS="missing-output"
        if [ -z "$COMPILE_BRIEF" ]; then
            COMPILE_BRIEF="missing-output path=$out_path"
        fi
    else
        COMPILE_CLASS="failure"
        if [ -z "$COMPILE_BRIEF" ]; then
            COMPILE_BRIEF="compile-exit=$COMPILE_EXIT"
        fi
    fi
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

runtime_self_target_summary() {
    local disasm_file="$1"

    python3 - "$disasm_file" <<'PY'
import re
import sys

disasm_path = sys.argv[1]
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
        target_match = target_re.search(line[branch.end():])
        if not addr_match or not target_match:
            continue

        instr_addr = int(addr_match.group(1), 16)
        target_addr = int(target_match.group(1), 16)
        if instr_addr == target_addr:
            hits.append(f"self-targeting: {line.rstrip()}")

if hits:
    print("\n".join(hits))
PY
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

classify_runtime() {
    local exit_code="$1"
    local stderr_file="$2"
    local binary="$3"
    local disasm_file=""
    local signal_name=""
    local brief=""

    RUNTIME_CLASS=""
    RUNTIME_DETAIL=""
    RUNTIME_SELF_TARGET=""

    if [ "$exit_code" -eq 0 ]; then
        RUNTIME_CLASS="success"
        return 0
    fi

    if grep -q "panicked at " "$stderr_file"; then
        brief=$(sed -n '1,3p' "$stderr_file" | tr '\n' ' ' | sed -E 's/[[:space:]]+/ /g; s/[[:space:]]+$//')
        RUNTIME_CLASS="panic"
        RUNTIME_DETAIL="$brief"
        return 0
    fi

    if [ "$exit_code" -eq 124 ]; then
        disasm_file="$TMP_DIR/$(basename "$binary").main.disasm"
        runtime_main_disasm "$binary" >"$disasm_file" 2>/dev/null || true
        if [ -s "$disasm_file" ]; then
            RUNTIME_SELF_TARGET=$(runtime_self_target_summary "$disasm_file" || true)
        fi
        if [ -n "$RUNTIME_SELF_TARGET" ]; then
            RUNTIME_CLASS="timeout-self-target"
            RUNTIME_DETAIL=$(printf '%s\n' "$RUNTIME_SELF_TARGET" | head -n1)
        else
            RUNTIME_CLASS="timeout"
            RUNTIME_DETAIL="timeout after 5 seconds"
        fi
        return 0
    fi

    if [ "$exit_code" -ge 128 ]; then
        signal_name=$(signal_name_for_exit "$exit_code" || true)
        RUNTIME_CLASS="signal"
        if [ -n "$signal_name" ]; then
            RUNTIME_DETAIL="$signal_name"
        else
            RUNTIME_DETAIL="exit=$exit_code"
        fi
        return 0
    fi

    RUNTIME_CLASS="runtime-failure"
    RUNTIME_DETAIL="exit=$exit_code"
}

sanitize_name() {
    printf '%s\n' "$1" | tr -cs '[:alnum:]' '_'
}

record_baseline_failure() {
    local line="$1"
    BASELINE_FAIL=$((BASELINE_FAIL + 1))
    append_line BASELINE_FAILURES "$line"
}

record_parity_pass() {
    local line="$1"
    PARITY_PASS=$((PARITY_PASS + 1))
    append_line PARITY_PASSES "$line"
}

record_parity_mismatch() {
    local line="$1"
    PARITY_FAIL=$((PARITY_FAIL + 1))
    append_line PARITY_FAILURES "$line"
}

print_compile_state() {
    local prefix="$1"
    local compile_class="$2"
    local compile_exit="$3"
    local compile_has_output="$4"
    local compile_brief="$5"

    echo "  $prefix compile=$compile_class exit=$compile_exit output=$compile_has_output"
    if [ -n "$compile_brief" ]; then
        echo "    detail: $compile_brief"
    fi
}

print_runtime_state() {
    local prefix="$1"
    local runtime_class="$2"
    local runtime_exit="$3"
    local runtime_detail="$4"

    echo "  $prefix runtime=$runtime_class exit=$runtime_exit"
    if [ -n "$runtime_detail" ]; then
        echo "    detail: $runtime_detail"
    fi
}

run_object_case() {
    local case_id="$1"
    local label="$2"
    local source_path="$3"
    shift 3

    local baseline_out=""
    local baseline_err=""
    local baseline_split=""
    local baseline_compile_exit=0
    local baseline_compile_class=""
    local baseline_compile_has_output=0
    local baseline_compile_brief=""
    local llvm2_out=""
    local llvm2_err=""
    local llvm2_split=""
    local llvm2_compile_exit=0
    local llvm2_compile_class=""
    local llvm2_compile_has_output=0
    local llvm2_compile_brief=""
    local crate_stub=""

    if ! matches_filter "$case_id" "$label"; then
        return 0
    fi

    CASES_RUN=$((CASES_RUN + 1))
    crate_stub=$(sanitize_name "$case_id")

    echo "=== [$case_id] $label ==="

    baseline_out="$TMP_DIR/${case_id}.llvm.o"
    baseline_err="$TMP_DIR/${case_id}.llvm.stderr"
    baseline_split="${baseline_out%.o}".*.rcgu.o
    run_compile \
        "default" \
        "$baseline_err" \
        "$baseline_out" \
        "$baseline_split" \
        --crate-type=bin \
        --crate-name="${crate_stub}_llvm" \
        "$@" \
        "$source_path" \
        --emit=obj
    baseline_compile_exit="$COMPILE_EXIT"
    baseline_compile_class="$COMPILE_CLASS"
    baseline_compile_has_output="$COMPILE_HAS_OUTPUT"
    baseline_compile_brief="$COMPILE_BRIEF"
    print_compile_state "default llvm:" "$baseline_compile_class" "$baseline_compile_exit" "$baseline_compile_has_output" "$baseline_compile_brief"

    llvm2_out="$TMP_DIR/${case_id}.llvm2.o"
    llvm2_err="$TMP_DIR/${case_id}.llvm2.stderr"
    llvm2_split="${llvm2_out%.o}".*.rcgu.o
    run_compile \
        "llvm2" \
        "$llvm2_err" \
        "$llvm2_out" \
        "$llvm2_split" \
        --crate-type=bin \
        --crate-name="${crate_stub}_llvm2" \
        "$@" \
        "$source_path" \
        --emit=obj
    llvm2_compile_exit="$COMPILE_EXIT"
    llvm2_compile_class="$COMPILE_CLASS"
    llvm2_compile_has_output="$COMPILE_HAS_OUTPUT"
    llvm2_compile_brief="$COMPILE_BRIEF"
    print_compile_state "llvm2:" "$llvm2_compile_class" "$llvm2_compile_exit" "$llvm2_compile_has_output" "$llvm2_compile_brief"

    if [ "$baseline_compile_exit" -ne 0 ] || [ "$baseline_compile_has_output" -ne 1 ]; then
        record_baseline_failure \
            "case=$case_id backend=default-llvm expected=compile-success actual=${baseline_compile_class} detail=${baseline_compile_brief:-exit=$baseline_compile_exit}"
        echo "  BASELINE FAIL: default LLVM did not satisfy object acceptance"
        echo
        return 0
    fi

    if [ "$llvm2_compile_exit" -eq 0 ] && [ "$llvm2_compile_has_output" -eq 1 ]; then
        record_parity_pass "case=$case_id llvm2=compile-success"
        echo "  PARITY PASS: llvm2 matched object acceptance"
    else
        record_parity_mismatch \
            "case=$case_id expected=compile-success actual=${llvm2_compile_class} detail=${llvm2_compile_brief:-exit=$llvm2_compile_exit}"
        echo "  PARITY MISMATCH: llvm2 did not match object acceptance"
    fi
    echo
}

run_runtime_case() {
    local case_id="$1"
    local label="$2"
    local expected_class="$3"
    local source_path="$4"
    shift 4

    local crate_stub=""
    local baseline_out=""
    local baseline_err=""
    local baseline_stdout=""
    local baseline_runtime_stderr=""
    local baseline_compile_exit=0
    local baseline_compile_class=""
    local baseline_compile_has_output=0
    local baseline_compile_brief=""
    local baseline_runtime_exit=125
    local baseline_runtime_class="not-run"
    local baseline_runtime_detail=""
    local llvm2_out=""
    local llvm2_err=""
    local llvm2_stdout=""
    local llvm2_runtime_stderr=""
    local llvm2_compile_exit=0
    local llvm2_compile_class=""
    local llvm2_compile_has_output=0
    local llvm2_compile_brief=""
    local llvm2_runtime_exit=125
    local llvm2_runtime_class="not-run"
    local llvm2_runtime_detail=""

    if ! matches_filter "$case_id" "$label"; then
        return 0
    fi

    CASES_RUN=$((CASES_RUN + 1))
    crate_stub=$(sanitize_name "$case_id")

    echo "=== [$case_id] $label ==="

    baseline_out="$TMP_DIR/${case_id}.llvm.bin"
    baseline_err="$TMP_DIR/${case_id}.llvm.stderr"
    run_compile \
        "default" \
        "$baseline_err" \
        "$baseline_out" \
        "" \
        --crate-type=bin \
        --crate-name="${crate_stub}_llvm" \
        "$@" \
        "$source_path" \
        --emit=link
    baseline_compile_exit="$COMPILE_EXIT"
    baseline_compile_class="$COMPILE_CLASS"
    baseline_compile_has_output="$COMPILE_HAS_OUTPUT"
    baseline_compile_brief="$COMPILE_BRIEF"
    print_compile_state "default llvm:" "$baseline_compile_class" "$baseline_compile_exit" "$baseline_compile_has_output" "$baseline_compile_brief"

    if [ "$baseline_compile_exit" -eq 0 ] && [ "$baseline_compile_has_output" -eq 1 ] && [ -x "$baseline_out" ]; then
        baseline_stdout="$TMP_DIR/${case_id}.llvm.stdout"
        baseline_runtime_stderr="$TMP_DIR/${case_id}.llvm.runtime.stderr"
        run_binary_with_timeout "$baseline_out" "$baseline_stdout" "$baseline_runtime_stderr" 5
        baseline_runtime_exit="$RUN_BINARY_EXIT"
        classify_runtime "$baseline_runtime_exit" "$baseline_runtime_stderr" "$baseline_out"
        baseline_runtime_class="$RUNTIME_CLASS"
        baseline_runtime_detail="$RUNTIME_DETAIL"
    fi
    print_runtime_state "default llvm:" "$baseline_runtime_class" "$baseline_runtime_exit" "$baseline_runtime_detail"

    llvm2_out="$TMP_DIR/${case_id}.llvm2.bin"
    llvm2_err="$TMP_DIR/${case_id}.llvm2.stderr"
    run_compile \
        "llvm2" \
        "$llvm2_err" \
        "$llvm2_out" \
        "" \
        --crate-type=bin \
        --crate-name="${crate_stub}_llvm2" \
        "$@" \
        "$source_path" \
        --emit=link
    llvm2_compile_exit="$COMPILE_EXIT"
    llvm2_compile_class="$COMPILE_CLASS"
    llvm2_compile_has_output="$COMPILE_HAS_OUTPUT"
    llvm2_compile_brief="$COMPILE_BRIEF"
    print_compile_state "llvm2:" "$llvm2_compile_class" "$llvm2_compile_exit" "$llvm2_compile_has_output" "$llvm2_compile_brief"

    if [ "$llvm2_compile_exit" -eq 0 ] && [ "$llvm2_compile_has_output" -eq 1 ] && [ -x "$llvm2_out" ]; then
        llvm2_stdout="$TMP_DIR/${case_id}.llvm2.stdout"
        llvm2_runtime_stderr="$TMP_DIR/${case_id}.llvm2.runtime.stderr"
        run_binary_with_timeout "$llvm2_out" "$llvm2_stdout" "$llvm2_runtime_stderr" 5
        llvm2_runtime_exit="$RUN_BINARY_EXIT"
        classify_runtime "$llvm2_runtime_exit" "$llvm2_runtime_stderr" "$llvm2_out"
        llvm2_runtime_class="$RUNTIME_CLASS"
        llvm2_runtime_detail="$RUNTIME_DETAIL"
    fi
    print_runtime_state "llvm2:" "$llvm2_runtime_class" "$llvm2_runtime_exit" "$llvm2_runtime_detail"

    if [ "$baseline_compile_exit" -ne 0 ] || [ "$baseline_compile_has_output" -ne 1 ]; then
        record_baseline_failure \
            "case=$case_id backend=default-llvm expected=compile-success actual=${baseline_compile_class} detail=${baseline_compile_brief:-exit=$baseline_compile_exit}"
        echo "  BASELINE FAIL: default LLVM did not produce a runnable artifact"
        echo
        return 0
    fi

    if [ "$baseline_runtime_class" != "$expected_class" ]; then
        record_baseline_failure \
            "case=$case_id backend=default-llvm expected_runtime=$expected_class actual=${baseline_runtime_class} detail=${baseline_runtime_detail:-exit=$baseline_runtime_exit}"
        echo "  BASELINE FAIL: default LLVM runtime drifted from expected class $expected_class"
        echo
        return 0
    fi

    if [ "$llvm2_compile_exit" -ne 0 ] || [ "$llvm2_compile_has_output" -ne 1 ]; then
        record_parity_mismatch \
            "case=$case_id expected_runtime=$expected_class actual=compile-${llvm2_compile_class} detail=${llvm2_compile_brief:-exit=$llvm2_compile_exit}"
        echo "  PARITY MISMATCH: llvm2 failed before runtime acceptance"
        echo
        return 0
    fi

    if [ "$llvm2_runtime_class" = "$expected_class" ]; then
        record_parity_pass "case=$case_id llvm2_runtime=$llvm2_runtime_class"
        echo "  PARITY PASS: llvm2 matched runtime class $expected_class"
    else
        record_parity_mismatch \
            "case=$case_id expected_runtime=$expected_class actual=${llvm2_runtime_class} detail=${llvm2_runtime_detail:-exit=$llvm2_runtime_exit}"
        echo "  PARITY MISMATCH: llvm2 runtime diverged from $expected_class"
    fi
    echo
}

if ! RUSTC="$(find_rustc)"; then
    echo "SKIP: stage1 trustc not found (run ./x.py build first)"
    exit 0
fi

SYSROOT=$("$RUSTC" --print sysroot)
HOST_TRIPLE=$("$RUSTC" -vV | sed -n 's/^host: //p')
BACKEND_DIR="$SYSROOT/lib/rustlib/$HOST_TRIPLE/codegen-backends"
LLVM2_BACKEND=""

if [ -d "$BACKEND_DIR" ]; then
    LLVM2_BACKEND="$(find_llvm2_backend "$BACKEND_DIR" || true)"
fi

if [ -z "$LLVM2_BACKEND" ]; then
    echo "SKIP: llvm2 backend not present under $BACKEND_DIR"
    echo "  Build stage1 with codegen-backends = [\"llvm\", \"llvm2\"] to run parity evaluation."
    exit 0
fi

echo "rustc: $RUSTC"
echo "sysroot: $SYSROOT"
echo "llvm2 backend: $LLVM2_BACKEND"
echo

TMP_DIR="$(mktemp -d /tmp/llvm2_parity_gate_XXXXXX)"
if [ "$KEEP_TMP" = "1" ]; then
    trap 'echo "keeping temp dir: $TMP_DIR"' EXIT
else
    trap 'rm -rf "$TMP_DIR"' EXIT
fi

CHECKED_DIV_RS="$TMP_DIR/checked_div.rs"
RUNTIME_MIN_RS="$TMP_DIR/runtime_min.rs"
RUNTIME_CF_RS="$TMP_DIR/runtime_cf.rs"
RUNTIME_ABORT_RS="$TMP_DIR/runtime_abort.rs"
RUNTIME_OVERFLOW_RS="$TMP_DIR/runtime_overflow.rs"

cat > "$CHECKED_DIV_RS" <<'RUST'
pub fn checked_div(a: i32, b: i32) -> Option<i32> {
    if b == 0 { None } else { Some(a / b) }
}

fn main() {
    let _ = checked_div(10, 2);
}
RUST

cat > "$RUNTIME_MIN_RS" <<'RUST'
fn main() {
    std::process::exit(0);
}
RUST

cat > "$RUNTIME_CF_RS" <<'RUST'
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

cat > "$RUNTIME_ABORT_RS" <<'RUST'
#[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
compile_error!("runtime abort parity smoke requires aarch64 or x86_64");

fn main() {
    unsafe {
        #[cfg(target_arch = "aarch64")]
        core::arch::asm!("brk #0", options(noreturn));

        #[cfg(target_arch = "x86_64")]
        core::arch::asm!("ud2", options(noreturn));
    }
}
RUST

cat > "$RUNTIME_OVERFLOW_RS" <<'RUST'
#[inline(never)]
fn checked_add(x: i32, y: i32) -> i32 {
    x + y
}

fn main() {
    let _ = checked_add(i32::MAX, 1);
}
RUST

CASES_RUN=0
BASELINE_FAIL=0
PARITY_PASS=0
PARITY_FAIL=0
BASELINE_FAILURES=""
PARITY_PASSES=""
PARITY_FAILURES=""

run_object_case \
    "checked-div-obj" \
    "checked_div object emission acceptance" \
    "$CHECKED_DIV_RS"

run_runtime_case \
    "runtime-min-exit" \
    "std::process::exit link/run acceptance" \
    "success" \
    "$RUNTIME_MIN_RS"

run_runtime_case \
    "runtime-control-flow" \
    "branch/join plus direct-call acceptance" \
    "success" \
    "$RUNTIME_CF_RS"

run_runtime_case \
    "runtime-abort-trap" \
    "explicit native trap acceptance" \
    "signal" \
    "$RUNTIME_ABORT_RS"

run_runtime_case \
    "runtime-overflow-check" \
    "checked overflow runtime acceptance" \
    "panic" \
    "$RUNTIME_OVERFLOW_RS" \
    -C overflow-checks=yes

if [ "$CASES_RUN" -eq 0 ]; then
    echo "FAIL: no cases matched filter '${FILTER}'" >&2
    exit 2
fi

echo "=== Summary ==="
echo "cases run: $CASES_RUN"
echo "baseline failures: $BASELINE_FAIL"
echo "llvm2 parity passes: $PARITY_PASS"
echo "llvm2 parity mismatches: $PARITY_FAIL"
echo

if [ -n "$BASELINE_FAILURES" ]; then
    echo "--- baseline failures ---"
    printf '%s\n' "$BASELINE_FAILURES"
    echo
fi

if [ -n "$PARITY_FAILURES" ]; then
    echo "--- llvm2 parity mismatches ---"
    printf '%s\n' "$PARITY_FAILURES"
    echo
fi

if [ "$BASELINE_FAIL" -gt 0 ]; then
    echo "FAILED: default LLVM baseline drifted inside the LLVM2 acceptance corpus"
    exit 1
fi

if [ "$PARITY_FAIL" -gt 0 ]; then
    if [ "$PARITY_MODE" = "enforce" ]; then
        echo "FAILED: LLVM2 mismatches are fatal in enforce mode"
        exit 1
    fi

    echo "REPORT-ONLY: LLVM2 mismatches recorded; set TRUST_LLVM2_PARITY_MODE=enforce to gate on them"
    exit 0
fi

echo "LLVM2 parity gate passed."
