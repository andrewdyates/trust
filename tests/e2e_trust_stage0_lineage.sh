#!/bin/bash
# End-to-end gate: prove bootstrap stage0 lineage has moved from upstream Rust
# to an explicitly tRust-owned local dist root or dist server/channel.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
MODE="gate"
STAGE0_FILE="$TRUST_ROOT/src/stage0"

fail_setup() {
    echo "ERROR: $1"
    exit 2
}

fail_test() {
    echo "FAIL: $1"
    exit 1
}

usage() {
    cat <<'EOF'
Usage: tests/e2e_trust_stage0_lineage.sh [--rehearsal <stage0-file>]

Default mode is the release gate and reads src/stage0.
Rehearsal mode reads an explicit candidate stage0 file so a proposed
tRust-owned local dist root or dist server/channel can be validated before
replacing src/stage0.
EOF
}

trim() {
    local value="$1"
    value="${value#"${value%%[![:space:]]*}"}"
    value="${value%"${value##*[![:space:]]}"}"
    printf '%s' "$value"
}

while [ "$#" -gt 0 ]; do
    case "$1" in
        --rehearsal)
            if [ "$#" -lt 2 ]; then
                fail_setup "--rehearsal requires a stage0 file path"
            fi
            MODE="rehearsal"
            STAGE0_FILE="$2"
            shift 2
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            fail_setup "unknown argument: $1"
            ;;
    esac
done

if [ ! -f "$STAGE0_FILE" ]; then
    fail_setup "stage0 file not found: $STAGE0_FILE"
fi

echo "=== tRust E2E Test: stage0 bootstrap lineage ($MODE) ==="
echo

stage0_keys=()
stage0_values=()
rustc_checksum_keys=()

while IFS= read -r raw_line || [ -n "$raw_line" ]; do
    line="${raw_line%$'\r'}"
    line="$(trim "$line")"
    if [ -z "$line" ] || [[ "$line" == \#* ]]; then
        continue
    fi
    if [[ "$line" != *=* ]]; then
        continue
    fi

    key="$(trim "${line%%=*}")"
    value="$(trim "${line#*=}")"
    if [ -z "$key" ]; then
        continue
    fi

    stage0_keys+=("$key")
    stage0_values+=("$value")
    if [[ "$key" == dist/*/rustc-* ]]; then
        rustc_checksum_keys+=("$key")
    fi
done < "$STAGE0_FILE"

stage0_value() {
    local key="$1"
    local idx
    idx="${#stage0_keys[@]}"
    while [ "$idx" -gt 0 ]; do
        idx=$((idx - 1))
        if [ "${stage0_keys[$idx]}" = "$key" ]; then
            printf '%s' "${stage0_values[$idx]}"
            return 0
        fi
    done
    return 1
}

require_key() {
    local key="$1"
    local value
    if ! value="$(stage0_value "$key")"; then
        fail_test "$STAGE0_FILE is missing required key: $key"
    fi
    if [ -z "$value" ]; then
        fail_test "$STAGE0_FILE key has an empty value: $key"
    fi
}

require_key dist_server
require_key artifacts_server
require_key artifacts_with_llvm_assertions_server
require_key compiler_dist_channel
require_key rustfmt_dist_channel
require_key compiler_version

dist_server="$(stage0_value dist_server)"
artifacts_server="$(stage0_value artifacts_server)"
artifacts_with_llvm_assertions_server="$(stage0_value artifacts_with_llvm_assertions_server)"
compiler_channel="$(stage0_value compiler_dist_channel)"
rustfmt_channel="$(stage0_value rustfmt_dist_channel)"
compiler_version="$(stage0_value compiler_version)"
expected_rustc_prefix="dist/"
expected_rustc_name="rustc-$compiler_version-"

case "$dist_server" in
    https://static.rust-lang.org|http://static.rust-lang.org|*://static.rust-lang.org/*|*://*.rust-lang.org|*://*.rust-lang.org/*)
        fail_test "bootstrap lineage is still upstream Rust: dist_server=$dist_server

Action: create a tRust-owned local bootstrap dist snapshot and update
dist_server to that local file:// root or another explicitly owned endpoint.
Use --rehearsal <candidate-stage0> to validate the proposed file before
replacing src/stage0."
        ;;
esac

for artifact_server in "$artifacts_server" "$artifacts_with_llvm_assertions_server"; do
    case "$artifact_server" in
        https://ci-artifacts.rust-lang.org|http://ci-artifacts.rust-lang.org|*://ci-artifacts.rust-lang.org/*|*://*.rust-lang.org|*://*.rust-lang.org/*)
            fail_test "bootstrap artifact lineage is still upstream Rust: artifact_server=$artifact_server

Action: create a tRust-owned local bootstrap dist snapshot and update all
stage0 artifact roots to local file:// roots or another explicitly owned
endpoint."
            ;;
    esac
done

case "$dist_server" in
    *trust*|*tRust*|*TRUST*) ;;
    *)
        fail_test "dist_server does not look tRust-owned: $dist_server

Action: use a tRust-owned local dist root or endpoint whose URL includes the
tRust/trust lineage marker, then regenerate the stage0 file."
        ;;
esac

case "$compiler_channel" in
    trust|trust-*|tRust|tRust-*|TRUST|TRUST-*) ;;
    beta|nightly|stable)
        fail_test "compiler_dist_channel is still upstream Rust channel: $compiler_channel

Action: create and configure a tRust-owned compiler_dist_channel, then
regenerate compiler_version and checksums."
        ;;
    *)
        fail_test "compiler_dist_channel is not an accepted tRust channel: $compiler_channel

Action: use a channel named trust, trust-*, tRust, or tRust-* so bootstrap
lineage is explicit in the stage0 file."
        ;;
esac

case "$rustfmt_channel" in
    trust|trust-*|tRust|tRust-*|TRUST|TRUST-*) ;;
    beta|nightly|stable)
        fail_test "rustfmt_dist_channel is still upstream Rust channel: $rustfmt_channel

Action: create and configure a tRust-owned rustfmt_dist_channel, then
regenerate rustfmt metadata."
        ;;
    *)
        fail_test "rustfmt_dist_channel is not an accepted tRust channel: $rustfmt_channel

Action: use a channel named trust, trust-*, tRust, or tRust-* so bootstrap
lineage is explicit in the stage0 file."
        ;;
esac

if [ "${#rustc_checksum_keys[@]}" -eq 0 ]; then
    fail_test "$STAGE0_FILE has no rustc checksum entries

Action: regenerate the stage0 file from the tRust dist manifest so rustc tarball
checksums are recorded."
fi

matching_rustc_checksum=""
for checksum_key in "${rustc_checksum_keys[@]}"; do
    filename="${checksum_key##*/}"
    if [[ "$checksum_key" == "$expected_rustc_prefix"* ]] && [[ "$filename" == "$expected_rustc_name"* ]]; then
        matching_rustc_checksum="$checksum_key"
        break
    fi
done

if [ -z "$matching_rustc_checksum" ]; then
    fail_test "no rustc checksum path matches generated compiler_version=$compiler_version

Expected at least one key shaped like:
  dist/<date>/rustc-$compiler_version-<target>.tar.*

Observed first rustc checksum key:
  ${rustc_checksum_keys[0]}

Action: regenerate the stage0 file from the tRust dist manifest; stale upstream
rustc-beta/rustc-nightly checksum paths do not prove tRust bootstrap lineage."
fi

echo "Stage0 file:              $STAGE0_FILE"
echo "Dist server:              $dist_server"
echo "Compiler dist channel:    $compiler_channel"
echo "Rustfmt dist channel:     $rustfmt_channel"
echo "Generated compiler:       $compiler_version"
echo "Rustc checksum proof key: $matching_rustc_checksum"
echo
echo "=== stage0 bootstrap lineage: PASS ==="
