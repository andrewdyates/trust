#!/usr/bin/env python3
"""Prepare a repo-local tRust stage0 dist snapshot.

This converts an `x dist` output directory into a local dist tree whose channel
identity is `trust`, then writes a candidate `src/stage0` file for rehearsal.
It does not upload, publish, or contact any remote service.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import shutil
import sys
import tomllib
from pathlib import Path


DEFAULT_STAGE0_COMPONENTS = (
    "rustc",
    "rust-std",
    "cargo",
    "clippy-preview",
    "rustfmt-preview",
    "rust-docs",
    "cargo-trust",
    "rust-analyzer-preview",
    "rust-src",
    "llvm-tools-preview",
)
REQUIRED_MANIFEST_PACKAGES = ("rust", *DEFAULT_STAGE0_COMPONENTS)


def sha256_file(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(block)
    return hasher.hexdigest()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def quote_key(key: str) -> str:
    if key and all(ch.isalnum() or ch in "_-" for ch in key):
        return key
    return json.dumps(key)


def format_toml_value(value: object) -> str:
    if isinstance(value, str):
        return json.dumps(value)
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int | float):
        return str(value)
    if isinstance(value, dt.date):
        return json.dumps(value.isoformat())
    if isinstance(value, list):
        return "[" + ", ".join(format_toml_value(item) for item in value) + "]"
    raise TypeError(f"unsupported TOML value: {value!r}")


def dump_toml(data: dict[str, object]) -> str:
    lines: list[str] = []

    def emit_table(prefix: tuple[str, ...], table: dict[str, object]) -> None:
        for key, value in table.items():
            if not isinstance(value, dict):
                lines.append(f"{quote_key(key)} = {format_toml_value(value)}")

        for key, value in table.items():
            if isinstance(value, dict):
                if lines and lines[-1] != "":
                    lines.append("")
                child_prefix = (*prefix, key)
                lines.append("[" + ".".join(quote_key(part) for part in child_prefix) + "]")
                emit_table(child_prefix, value)

    emit_table((), data)
    return "\n".join(lines) + "\n"


def replace_channel_token(value: str, source_channel: str, owned_channel: str) -> str:
    return (
        value.replace(f"-{source_channel}-", f"-{owned_channel}-")
        .replace(f"-{source_channel}.", f"-{owned_channel}.")
        .replace(f"-{source_channel} ", f"-{owned_channel} ")
    )


def dist_url(dist_server: str, date: str, filename: str) -> str:
    return f"{dist_server.rstrip('/')}/dist/{date}/{filename}"


def source_tarball(input_dist: Path, filename: str, date: str) -> Path:
    candidates = [
        input_dist / filename,
        input_dist / date / filename,
    ]
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    raise FileNotFoundError(f"missing dist tarball referenced by manifest: {filename}")


def rewrite_target_urls(
    target: dict[str, object],
    *,
    input_dist: Path,
    output_date_dir: Path,
    date: str,
    dist_server: str,
    source_channel: str,
    owned_channel: str,
) -> None:
    for url_key, hash_key in (("url", "hash"), ("xz_url", "xz_hash")):
        value = target.get(url_key)
        if not isinstance(value, str) or not value:
            continue

        old_filename = Path(value).name
        new_filename = replace_channel_token(old_filename, source_channel, owned_channel)
        src = source_tarball(input_dist, old_filename, date)
        dst = output_date_dir / new_filename
        if not dst.exists():
            shutil.copy2(src, dst)

        target[url_key] = dist_url(dist_server, date, new_filename)
        target[hash_key] = sha256_file(dst)


def rewrite_manifest(
    manifest: dict[str, object],
    *,
    input_dist: Path,
    output_date_dir: Path,
    date: str,
    dist_server: str,
    source_channel: str,
    owned_channel: str,
) -> None:
    packages = manifest.get("pkg")
    if not isinstance(packages, dict):
        raise ValueError("manifest is missing [pkg] table")

    missing = [component for component in REQUIRED_MANIFEST_PACKAGES if component not in packages]
    if missing:
        raise ValueError("manifest is missing required trust components: " + ", ".join(missing))

    manifest["date"] = date
    for package in packages.values():
        if not isinstance(package, dict):
            continue
        version = package.get("version")
        if isinstance(version, str):
            package["version"] = replace_channel_token(version, source_channel, owned_channel)
        targets = package.get("target")
        if not isinstance(targets, dict):
            continue
        for target in targets.values():
            if isinstance(target, dict):
                rewrite_target_urls(
                    target,
                    input_dist=input_dist,
                    output_date_dir=output_date_dir,
                    date=date,
                    dist_server=dist_server,
                    source_channel=source_channel,
                    owned_channel=owned_channel,
                )


def checksum_entries(
    manifest: dict[str, object],
    *,
    dist_server: str,
    components: tuple[str, ...],
) -> dict[str, str]:
    prefix = f"{dist_server.rstrip('/')}/"
    packages = manifest["pkg"]
    assert isinstance(packages, dict)

    checksums: dict[str, str] = {}
    for component in components:
        package = packages[component]
        assert isinstance(package, dict)
        targets = package["target"]
        assert isinstance(targets, dict)
        for target in targets.values():
            if not isinstance(target, dict):
                continue
            for url_key, hash_key in (("url", "hash"), ("xz_url", "xz_hash")):
                url = target.get(url_key)
                digest = target.get(hash_key)
                if isinstance(url, str) and isinstance(digest, str):
                    if not url.startswith(prefix):
                        raise ValueError(f"url does not start with dist server: {url}")
                    checksums[url[len(prefix) :]] = digest
    return dict(sorted(checksums.items()))


def stage0_content(
    *,
    manifest: dict[str, object],
    manifest_hash: str,
    dist_server: str,
    owned_channel: str,
    checksums: dict[str, str],
) -> str:
    packages = manifest["pkg"]
    assert isinstance(packages, dict)
    rust_package = packages["rust"]
    assert isinstance(rust_package, dict)
    git_commit_hash = rust_package.get("git_commit_hash") or rust_package.get("git-commit-hash")
    if not isinstance(git_commit_hash, str) or not git_commit_hash:
        raise ValueError("manifest [pkg.rust] is missing git_commit_hash")

    date = manifest["date"]
    if isinstance(date, dt.date):
        date = date.isoformat()
    if not isinstance(date, str):
        raise ValueError("manifest date must be a string")

    dist_root = dist_server.rstrip("/")
    lines = [
        f"dist_server={dist_root}",
        f"artifacts_server={dist_root}/artifacts",
        f"artifacts_with_llvm_assertions_server={dist_root}/artifacts-with-llvm-assertions",
        "git_merge_commit_email=trust@local",
        "nightly_branch=main",
        f"compiler_dist_channel={owned_channel}",
        f"rustfmt_dist_channel={owned_channel}",
        "",
        "# The configuration above this comment is editable, and can be changed",
        "# by forks of the repository if they have alternate values.",
        "#",
        "# The section below was generated by src/tools/trust-stage0-dist/prepare.py",
        "# from a repo-local dist snapshot.",
        "",
        f"compiler_channel_manifest_hash={manifest_hash}",
        f"compiler_git_commit_hash={git_commit_hash}",
        f"compiler_date={date}",
        f"compiler_version={owned_channel}",
        f"rustfmt_channel_manifest_hash={manifest_hash}",
        f"rustfmt_git_commit_hash={git_commit_hash}",
        f"rustfmt_date={date}",
        f"rustfmt_version={owned_channel}",
        "",
    ]
    lines.extend(f"{key}={value}" for key, value in checksums.items())
    lines.append("")
    return "\n".join(lines)


def prepare(args: argparse.Namespace) -> None:
    input_dist = args.input_dist.resolve()
    output_root = args.output_root.resolve()
    dist_server = args.dist_server or output_root.as_uri()

    source_manifest_path = input_dist / f"channel-rust-{args.source_channel}.toml"
    if not source_manifest_path.is_file():
        raise FileNotFoundError(f"missing source manifest: {source_manifest_path}")

    manifest = tomllib.loads(source_manifest_path.read_text(encoding="utf-8"))
    raw_date = manifest.get("date")
    date = args.date or (raw_date.isoformat() if isinstance(raw_date, dt.date) else raw_date)
    if not isinstance(date, str) or not date:
        raise ValueError("manifest is missing a date; pass --date explicitly")

    output_dist = output_root / "dist"
    output_date_dir = output_dist / date
    output_date_dir.mkdir(parents=True, exist_ok=True)

    rewrite_manifest(
        manifest,
        input_dist=input_dist,
        output_date_dir=output_date_dir,
        date=date,
        dist_server=dist_server,
        source_channel=args.source_channel,
        owned_channel=args.owned_channel,
    )

    manifest_text = dump_toml(manifest)
    manifest_bytes = manifest_text.encode("utf-8")
    manifest_hash = sha256_bytes(manifest_bytes)

    latest_manifest = output_dist / f"channel-rust-{args.owned_channel}.toml"
    dated_manifest = output_date_dir / f"channel-rust-{args.owned_channel}.toml"
    latest_manifest.write_bytes(manifest_bytes)
    dated_manifest.write_bytes(manifest_bytes)
    latest_manifest.with_suffix(latest_manifest.suffix + ".sha256").write_text(
        manifest_hash + "\n",
        encoding="utf-8",
    )
    dated_manifest.with_suffix(dated_manifest.suffix + ".sha256").write_text(
        manifest_hash + "\n",
        encoding="utf-8",
    )

    checksums = checksum_entries(
        manifest,
        dist_server=dist_server,
        components=DEFAULT_STAGE0_COMPONENTS,
    )
    if args.stage0_output is not None:
        args.stage0_output.parent.mkdir(parents=True, exist_ok=True)
        args.stage0_output.write_text(
            stage0_content(
                manifest=manifest,
                manifest_hash=manifest_hash,
                dist_server=dist_server,
                owned_channel=args.owned_channel,
                checksums=checksums,
            ),
            encoding="utf-8",
        )

    print(f"trust dist root: {output_root}")
    print(f"trust channel:   {args.owned_channel}")
    print(f"manifest:        {latest_manifest}")
    if args.stage0_output is not None:
        print(f"stage0 candidate:{args.stage0_output}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dist", type=Path, default=Path("build/dist"))
    parser.add_argument("--output-root", type=Path, default=Path("build/trust-stage0"))
    parser.add_argument("--source-channel", default="nightly")
    parser.add_argument("--owned-channel", default="trust")
    parser.add_argument("--date")
    parser.add_argument("--dist-server")
    parser.add_argument("--stage0-output", type=Path, default=Path("build/trust-stage0/src-stage0"))
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    prepare(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
