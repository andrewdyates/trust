#!/bin/bash
# End-to-end test: local `x dist` outputs contain the `cargo-trust` component
# and manifest wiring expected for the default-profile shipped toolchain.
#
# This is a pre-publish rehearsal gate. It is not the final `#1011` acceptance
# gate, which must still be satisfied by a rustup-installed toolchain on a
# fresh machine.

set -euo pipefail

echo "=== tRust E2E Test: dist artifacts for cargo-trust ==="
echo

fail_setup() {
    echo "ERROR: $1"
    exit 2
}

fail_test() {
    echo "FAIL: $1"
    exit 1
}

require_command() {
    local cmd="$1"
    local install_hint="$2"
    if ! command -v "$cmd" >/dev/null 2>&1; then
        fail_setup "$cmd not found on PATH. $install_hint"
    fi
}

require_python_tomllib() {
    require_command python3 "Install Python 3.11+ first."
    if ! python3 - <<'PY' >/dev/null 2>&1
import tomllib
PY
    then
        fail_setup "python3 does not provide tomllib. Install Python 3.11+ to parse channel manifests."
    fi
}

require_command rustc "Install Rust first."
require_python_tomllib
require_command tar "Install tar first."

DIST_DIR="build/dist"
MANIFEST="$DIST_DIR/channel-rust-nightly.toml"
HOST="$(rustc -vV | awk '/^host: / { print $2 }')"

if [ -z "$HOST" ]; then
    fail_setup "could not determine host triple from rustc -vV"
fi
if [ ! -d "$DIST_DIR" ]; then
    fail_setup "build/dist not found. Run ./x dist first."
fi
if [ ! -f "$MANIFEST" ]; then
    fail_setup "channel manifest not found at $MANIFEST. Run ./x dist first."
fi

XZ_TARBALL="$DIST_DIR/cargo-trust-nightly-$HOST.tar.xz"
GZ_TARBALL="$DIST_DIR/cargo-trust-nightly-$HOST.tar.gz"
RUSTC_XZ_TARBALL="$DIST_DIR/rustc-nightly-$HOST.tar.xz"
RUSTC_GZ_TARBALL="$DIST_DIR/rustc-nightly-$HOST.tar.gz"
SOURCE_TARBALLS=()

if [ ! -f "$XZ_TARBALL" ]; then
    fail_test "missing cargo-trust xz tarball: $XZ_TARBALL"
fi
if [ ! -f "$GZ_TARBALL" ]; then
    fail_test "missing cargo-trust gz tarball: $GZ_TARBALL"
fi
if [ ! -f "$RUSTC_XZ_TARBALL" ]; then
    fail_test "missing rustc xz tarball with trustc alias: $RUSTC_XZ_TARBALL"
fi
if [ ! -f "$RUSTC_GZ_TARBALL" ]; then
    fail_test "missing rustc gz tarball with trustc alias: $RUSTC_GZ_TARBALL"
fi

for source_tarball in \
    "$DIST_DIR/rustc-nightly-src.tar.gz" \
    "$DIST_DIR/rustc-nightly-src.tar.xz" \
    "$DIST_DIR/rustc-nightly-src-gpl.tar.gz" \
    "$DIST_DIR/rustc-nightly-src-gpl.tar.xz"
do
    if [ -f "$source_tarball" ]; then
        SOURCE_TARBALLS+=("$source_tarball")
    fi
done

if [ "${#SOURCE_TARBALLS[@]}" -eq 0 ]; then
    fail_test "missing rustc source tarball. Expected rustc-nightly-src.tar.gz/.xz from ./x dist."
fi

python3 - "$MANIFEST" "$HOST" <<'PY'
import pathlib
import re
import sys
import tomllib

manifest_path = pathlib.Path(sys.argv[1])
host = sys.argv[2]
manifest = tomllib.loads(manifest_path.read_text(encoding="utf-8"))

def require(condition, message):
    if not condition:
        raise SystemExit(f"FAIL: {message}")

def require_hash(pkg, key, label):
    value = pkg.get(key)
    require(value, f"cargo-trust package is missing {label}")
    require(
        re.fullmatch(r"[0-9a-f]{64}", value) is not None,
        f"cargo-trust package has invalid {label}: {value!r}",
    )

profiles = manifest.get("profiles")
require(isinstance(profiles, dict), "manifest profiles table is missing or malformed")
default_profile = profiles.get("default")
require(isinstance(default_profile, list), "default profile is missing or is not a TOML array")
for component in [
    "rustc",
    "cargo",
    "rust-std",
    "rust-docs",
    "cargo-trust",
    "rustfmt-preview",
    "clippy-preview",
    "rust-analyzer-preview",
    "rust-src",
    "llvm-tools-preview",
]:
    require(component in default_profile, f"default profile is missing {component}")

pkg = manifest["pkg"]["cargo-trust"]["target"][host]
require(pkg["available"] is True, "cargo-trust package is not available for host")
require("url" in pkg and pkg["url"], "cargo-trust package is missing url")
require(pkg["url"].endswith(".tar.gz"), f"cargo-trust url does not point at a gz tarball: {pkg['url']}")
require_hash(pkg, "hash", "gz hash")
require("xz_url" in pkg and pkg["xz_url"], "cargo-trust package is missing xz_url")
require(
    pkg["xz_url"].endswith(".tar.xz"),
    f"cargo-trust xz_url does not point at an xz tarball: {pkg['xz_url']}",
)
require_hash(pkg, "xz_hash", "xz hash")

extensions = manifest["pkg"]["rust"]["target"][host]["extensions"]
require(
    any(ext["pkg"] == "cargo-trust" and ext["target"] == host for ext in extensions),
    "rust package extensions are missing cargo-trust",
)
PY

python3 - "$XZ_TARBALL" "$GZ_TARBALL" "$RUSTC_XZ_TARBALL" "$RUSTC_GZ_TARBALL" "${SOURCE_TARBALLS[@]}" <<'PY'
import pathlib
import stat
import sys
import tarfile

cargo_trust_tarballs = [pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])]
rustc_tarballs = [pathlib.Path(sys.argv[3]), pathlib.Path(sys.argv[4])]
source_tarballs = [pathlib.Path(arg) for arg in sys.argv[5:]]

def fail(message):
    raise SystemExit(f"FAIL: {message}")

def names(tarball):
    try:
        with tarfile.open(tarball) as archive:
            return [member.name.rstrip("/") for member in archive.getmembers()]
    except (tarfile.TarError, OSError) as exc:
        fail(f"could not read {tarball}: {exc}")

def has_path(names, suffix):
    return any(name == suffix or name.endswith(f"/{suffix}") for name in names)

def require_path(names, suffix, tarball):
    if not has_path(names, suffix):
        fail(f"{tarball} is missing {suffix}")

def require_executable(tarball, suffix):
    try:
        with tarfile.open(tarball) as archive:
            for member in archive.getmembers():
                name = member.name.rstrip("/")
                if (name == suffix or name.endswith(f"/{suffix}")) and member.isfile():
                    if member.mode & (stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH):
                        return
                    fail(f"{tarball} contains {suffix}, but it is not executable")
    except (tarfile.TarError, OSError) as exc:
        fail(f"could not read {tarball}: {exc}")
    fail(f"{tarball} is missing executable {suffix}")

for tarball in cargo_trust_tarballs:
    entries = names(tarball)
    require_executable(tarball, "cargo-trust/bin/cargo-trust")
    require_path(entries, "cargo-trust/share/doc/cargo-trust/README.md", tarball)
    require_path(entries, "cargo-trust/share/doc/cargo-trust/LICENSE-APACHE", tarball)
    require_path(entries, "cargo-trust/manifest.in", tarball)
    require_path(entries, "components", tarball)

for tarball in rustc_tarballs:
    require_executable(tarball, "rustc/bin/trustc")
    require_executable(tarball, "rustc/bin/rustc")

for tarball in source_tarballs:
    entries = names(tarball)
    require_path(entries, "cargo-trust/Cargo.toml", tarball)
    require_path(entries, "cargo-trust/src/main.rs", tarball)
    require_path(entries, "cargo-trust/README.md", tarball)
    require_path(entries, "crates/Cargo.toml", tarball)
    require_path(entries, "crates/Cargo.lock", tarball)
PY

echo "Host triple: $HOST"
echo "Manifest:    $MANIFEST"
echo "Tarballs:    $GZ_TARBALL / $XZ_TARBALL"
echo "Compiler:    $RUSTC_GZ_TARBALL / $RUSTC_XZ_TARBALL"
echo "Sources:     ${SOURCE_TARBALLS[*]}"
echo
echo "=== dist artifact cargo-trust test: PASS ==="
