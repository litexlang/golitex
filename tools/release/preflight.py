#!/usr/bin/env python3
"""Build, package, unpack, and smoke-test a Litex release artifact locally."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import zipfile
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence


SMOKE_SOURCE = (
    "import std basics\n"
    "by thm basics::prime_implies_prime_by_trial_division(2)\n"
)
PACKAGE_VERSION = re.compile(r'^version\s*=\s*"([^"]+)"\s*$')
HOST_TARGET = re.compile(r"^host:\s*(\S+)\s*$", re.MULTILINE)


class PreflightError(RuntimeError):
    """A release preflight contract failed."""


@dataclass(frozen=True)
class ReleasePlatform:
    target: str
    os_name: str
    arch: str
    binary_name: str
    archive_suffix: str


PLATFORMS = {
    "x86_64-unknown-linux-gnu": ReleasePlatform(
        "x86_64-unknown-linux-gnu", "linux", "amd64", "litex", ".tar.gz"
    ),
    "aarch64-unknown-linux-gnu": ReleasePlatform(
        "aarch64-unknown-linux-gnu", "linux", "arm64", "litex", ".tar.gz"
    ),
    "aarch64-apple-darwin": ReleasePlatform(
        "aarch64-apple-darwin", "darwin", "arm64", "litex", ".tar.gz"
    ),
    "x86_64-pc-windows-msvc": ReleasePlatform(
        "x86_64-pc-windows-msvc", "windows", "amd64", "litex.exe", ".zip"
    ),
}


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    repository_root = Path(__file__).resolve().parents[2]

    try:
        cargo_version = package_version(repository_root / "Cargo.toml")
        version = args.version or cargo_version
        if version != cargo_version:
            raise PreflightError(
                f"requested version {version!r} does not match Cargo.toml "
                f"version {cargo_version!r}"
            )

        private_root = repository_root / "private"
        private_root.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(
            prefix="release-preflight.", dir=private_root
        ) as temporary_directory:
            work_directory = Path(temporary_directory)
            if args.archive is not None:
                archive = args.archive.resolve()
                if not archive.is_file():
                    raise PreflightError(f"archive does not exist: {archive}")
                print(f"PREFLIGHT archive: {archive}", flush=True)
            else:
                target = args.target or rust_host_target(repository_root)
                host = rust_host_target(repository_root)
                if target != host:
                    raise PreflightError(
                        f"target {target!r} is not executable on this host {host!r}; "
                        "run this preflight on that target's native runner"
                    )
                platform = release_platform(target)
                archive = build_local_archive(
                    repository_root, work_directory, version, platform
                )

            check_archive(work_directory, archive, version)
        print(f"Temporary work directory cleaned: {work_directory}", flush=True)
        print("PREFLIGHT SUCCESS", flush=True)
        return 0
    except (OSError, PreflightError, subprocess.SubprocessError) as error:
        print(f"PREFLIGHT FAILED: {error}", file=sys.stderr)
        return 1


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Simulate the native GitHub release lane by building, packaging, "
            "unpacking, and smoke-testing the shipped binary and std directory."
        )
    )
    parser.add_argument(
        "--version",
        help="expected release version (default: the Cargo.toml package version)",
    )
    source = parser.add_mutually_exclusive_group()
    source.add_argument(
        "--target",
        help="native Rust target (default: rustc host; cross targets are rejected)",
    )
    source.add_argument(
        "--archive",
        type=Path,
        help="check an existing .tar.gz or .zip instead of building one",
    )
    return parser.parse_args(argv)


def package_version(cargo_toml: Path) -> str:
    in_package = False
    for raw_line in cargo_toml.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if line.startswith("[") and line.endswith("]"):
            if in_package:
                break
            in_package = line == "[package]"
            continue
        if not in_package:
            continue
        match = PACKAGE_VERSION.match(line)
        if match:
            return match.group(1)
    raise PreflightError(f"could not read [package] version from {cargo_toml}")


def rust_host_target(repository_root: Path) -> str:
    completed = subprocess.run(
        ["rustc", "-vV"],
        cwd=repository_root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if completed.returncode != 0:
        raise PreflightError(f"rustc -vV failed:\n{completed.stdout}")
    match = HOST_TARGET.search(completed.stdout)
    if not match:
        raise PreflightError("rustc -vV did not report a host target")
    return match.group(1)


def release_platform(target: str) -> ReleasePlatform:
    try:
        return PLATFORMS[target]
    except KeyError as error:
        supported = ", ".join(sorted(PLATFORMS))
        raise PreflightError(
            f"unsupported release target {target!r}; supported targets: {supported}"
        ) from error


def build_local_archive(
    repository_root: Path,
    work_directory: Path,
    version: str,
    platform: ReleasePlatform,
) -> Path:
    target_directory = work_directory / "target"
    command = [
        "cargo",
        "build",
        "--release",
        "--target",
        platform.target,
        "--target-dir",
        str(target_directory),
    ]
    print("PREFLIGHT build: " + " ".join(command), flush=True)
    completed = subprocess.run(command, cwd=repository_root, check=False)
    if completed.returncode != 0:
        raise PreflightError(f"release build exited with {completed.returncode}")

    built_binary = (
        target_directory / platform.target / "release" / platform.binary_name
    )
    if not built_binary.is_file():
        raise PreflightError(f"release binary is missing: {built_binary}")

    package_directory = work_directory / "package"
    package_directory.mkdir()
    shutil.copy2(built_binary, package_directory / platform.binary_name)
    standard_library = repository_root / "std"
    if not (standard_library / "basics" / "litex.config").is_file():
        raise PreflightError("std/basics/litex.config is missing")
    shutil.copytree(standard_library, package_directory / "std")

    archive = work_directory / (
        f"litex_{version}_{platform.os_name}_{platform.arch}"
        f"{platform.archive_suffix}"
    )
    create_archive(package_directory, archive)
    print(f"PREFLIGHT package: {archive.name}", flush=True)
    return archive


def create_archive(package_directory: Path, archive: Path) -> None:
    if archive.name.endswith(".tar.gz"):
        with tarfile.open(archive, "w:gz") as output:
            for child in sorted(package_directory.iterdir()):
                output.add(child, arcname=child.name)
        return
    if archive.suffix == ".zip":
        with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED) as output:
            for path in sorted(package_directory.rglob("*")):
                if path.is_file():
                    output.write(path, path.relative_to(package_directory))
        return
    raise PreflightError(f"unsupported archive format: {archive}")


def check_archive(
    work_directory: Path,
    archive: Path,
    version: str,
) -> None:
    extracted = work_directory / "extracted"
    extracted.mkdir()
    extract_archive(archive, extracted)

    binary_candidates = [extracted / "litex", extracted / "litex.exe"]
    binaries = [candidate for candidate in binary_candidates if candidate.is_file()]
    if len(binaries) != 1:
        raise PreflightError(
            "archive must contain exactly one root binary named litex or litex.exe"
        )
    binary = binaries[0]
    if os.name != "nt":
        binary.chmod(binary.stat().st_mode | 0o111)

    if not (extracted / "std" / "basics" / "litex.config").is_file():
        raise PreflightError("archive is missing std/basics/litex.config")
    if not (extracted / "std" / "basics" / "main.lit").is_file():
        raise PreflightError("archive is missing std/basics/main.lit")

    version_result = subprocess.run(
        [str(binary), "-version"],
        cwd=extracted,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    expected_version_output = f"Litex Kernel: litex {version}"
    if (
        version_result.returncode != 0
        or version_result.stdout.strip() != expected_version_output
    ):
        raise PreflightError(
            f"archive binary version check failed for {version!r}:\n"
            f"{version_result.stdout}"
        )

    smoke_file = extracted / "smoke.lit"
    smoke_file.write_text(SMOKE_SOURCE, encoding="utf-8")
    smoke_result = subprocess.run(
        [str(binary), "-runner", "-isolated", "-f", smoke_file.name],
        cwd=extracted,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    validate_runner_output(smoke_result.stdout, smoke_result.returncode)
    print(
        "PREFLIGHT smoke: import std basics + "
        "basics::prime_implies_prime_by_trial_division(2) -> ok",
        flush=True,
    )


def extract_archive(archive: Path, destination: Path) -> None:
    if archive.name.endswith(".tar.gz"):
        with tarfile.open(archive, "r:gz") as source:
            for member in source.getmembers():
                validate_archive_member(member.name, member.issym() or member.islnk())
            source.extractall(destination, filter="data")
        return
    if archive.suffix == ".zip":
        with zipfile.ZipFile(archive) as source:
            for member in source.infolist():
                validate_archive_member(member.filename, False)
            source.extractall(destination)
        return
    raise PreflightError(f"unsupported archive format: {archive}")


def validate_archive_member(name: str, is_link: bool) -> None:
    path = Path(name)
    if is_link or path.is_absolute() or ".." in path.parts:
        raise PreflightError(f"unsafe archive member: {name!r}")
    if any(part.startswith("._") or part == ".DS_Store" for part in path.parts):
        raise PreflightError(f"macOS metadata must not be shipped: {name!r}")


def validate_runner_output(output: str, returncode: int) -> None:
    try:
        envelope = json.loads(output)
    except json.JSONDecodeError as error:
        raise PreflightError(f"smoke test did not return runner JSON:\n{output}") from error
    if returncode != 0:
        raise PreflightError(f"smoke test exited with {returncode}:\n{output}")
    if not isinstance(envelope, dict):
        raise PreflightError("smoke test runner output is not an object")
    if envelope.get("runner") != "litex-runner":
        raise PreflightError("smoke test output is not a litex-runner envelope")
    if envelope.get("runner_version") != "0.1":
        raise PreflightError("smoke test returned an unsupported runner version")
    target = envelope.get("target")
    if not isinstance(target, dict) or target.get("kind") != "file":
        raise PreflightError("smoke test runner target is not a file")
    if envelope.get("result") != "success" or envelope.get("ok") is not True:
        raise PreflightError(f"smoke test did not verify successfully:\n{output}")


if __name__ == "__main__":
    raise SystemExit(main())
