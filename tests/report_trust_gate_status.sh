#!/bin/bash
# Print a concise release-gate readiness matrix for the trust gates.
#
# This helper is evidence-only: it runs the existing gates, preserves each
# gate's exit code in the summary, and leaves the gate scripts as the source of
# truth for pass/fail behavior.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
ROBUST_SUITE="$SCRIPT_DIR/run_trust_robust_suite.sh"
LOG_DIR="$(mktemp -d "${TMPDIR:-/tmp}/trust-gate-status.XXXXXX")"
TAIL_LINES="${TRUST_GATE_STATUS_TAIL_LINES:-20}"

GATES=(
    launch
    prepublish
    installed
    installed-default
    stage0-lineage
)

gate_names=()
gate_statuses=()
gate_codes=()
gate_logs=()

status_for_code() {
    local code="$1"
    case "$code" in
        0) printf 'PASS' ;;
        2) printf 'SETUP/BLOCKED' ;;
        *) printf 'FAIL' ;;
    esac
}

mode_supported() {
    local mode="$1"
    [ -f "$ROBUST_SUITE" ] || return 1
    awk -v mode="$mode" '$1 == mode ")" { found = 1 } END { exit found ? 0 : 1 }' "$ROBUST_SUITE"
}

record_gate() {
    local name="$1"
    local code="$2"
    local log="$3"

    gate_names+=("$name")
    gate_codes+=("$code")
    gate_statuses+=("$(status_for_code "$code")")
    gate_logs+=("$log")
}

run_gate() {
    local gate="$1"
    local log="$LOG_DIR/$gate.log"
    local code

    if [ ! -f "$ROBUST_SUITE" ]; then
        {
            echo "ERROR: robust suite not found: $ROBUST_SUITE"
            echo "Expected tests/run_trust_robust_suite.sh to provide gate modes."
        } >"$log"
        record_gate "$gate" 2 "$log"
        return
    fi

    if ! mode_supported "$gate"; then
        {
            echo "ERROR: robust suite mode is missing: $gate"
            echo "Expected tests/run_trust_robust_suite.sh to support '$gate'."
        } >"$log"
        record_gate "$gate" 2 "$log"
        return
    fi

    set +e
    (
        cd "$TRUST_ROOT"
        RUSTUP_SELF_UPDATE=disable bash "$ROBUST_SUITE" "$gate"
    ) >"$log" 2>&1
    code=$?
    set -e

    record_gate "$gate" "$code" "$log"
}

print_summary() {
    local idx

    echo "=== tRust release-gate readiness ==="
    echo "Logs: $LOG_DIR"
    echo
    printf '%-16s %-14s %-6s %s\n' "Gate" "Status" "Exit" "Log"
    printf '%-16s %-14s %-6s %s\n' "----" "------" "----" "---"

    for idx in "${!gate_names[@]}"; do
        printf '%-16s %-14s %-6s %s\n' \
            "${gate_names[$idx]}" \
            "${gate_statuses[$idx]}" \
            "${gate_codes[$idx]}" \
            "${gate_logs[$idx]}"
    done
}

print_failure_tails() {
    local idx

    for idx in "${!gate_names[@]}"; do
        if [ "${gate_codes[$idx]}" -eq 0 ]; then
            continue
        fi

        echo
        echo "--- ${gate_names[$idx]} ${gate_statuses[$idx]} tail (${gate_logs[$idx]}) ---"
        tail -n "$TAIL_LINES" "${gate_logs[$idx]}" || true
    done
}

summary_exit_code() {
    local idx
    local saw_blocked=0

    for idx in "${!gate_codes[@]}"; do
        case "${gate_codes[$idx]}" in
            0) ;;
            2) saw_blocked=1 ;;
            *) return 1 ;;
        esac
    done

    if [ "$saw_blocked" -eq 1 ]; then
        return 2
    fi

    return 0
}

for gate in "${GATES[@]}"; do
    run_gate "$gate"
done

print_summary
print_failure_tails
summary_exit_code
