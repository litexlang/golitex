#!/usr/bin/env python3
"""Validate an explicit manual release before any publishing job can run."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
from typing import Mapping

from preflight import package_version


REQUIRED_CREDENTIALS = (
    "CRATES_IO_TOKEN",
    "HOMEBREW_TAP_TOKEN",
    "SCOOP_BUCKET_TOKEN",
    "WEB_DEPLOY_HOST",
    "WEB_DEPLOY_USER",
    "WEB_DEPLOY_SSH_KEY",
)


def validate_request(version: str, environment: Mapping[str, str]) -> bool:
    requested = environment.get("PUBLISH_RELEASE", "false")
    if requested not in ("true", "false"):
        raise ValueError("PUBLISH_RELEASE must be true or false")
    if requested == "false":
        return False
    if environment.get("GITHUB_EVENT_NAME") != "workflow_dispatch":
        raise ValueError("publishing requires a manual workflow_dispatch run")
    if environment.get("GITHUB_REF") != "refs/heads/main":
        raise ValueError("publishing is allowed only from main")
    if environment.get("RELEASE_VERSION", "") != version:
        raise ValueError(f"release version must exactly match Cargo.toml: {version}")
    missing = [name for name in REQUIRED_CREDENTIALS if not environment.get(name)]
    if missing:
        raise ValueError("missing release secrets: " + ", ".join(missing))
    return True


def validate_tag(version: str, commit: str) -> None:
    if not commit:
        raise ValueError("GITHUB_SHA is required for publishing")
    tag = f"refs/tags/{version}"
    result = subprocess.run(
        ["git", "ls-remote", "--exit-code", "origin", tag, f"{tag}^{{}}"],
        capture_output=True,
        text=True,
        timeout=30,
    )
    if result.returncode == 2:
        return
    if result.returncode != 0:
        raise ValueError("could not verify the remote release tag; refusing to publish")
    refs = {ref: sha for sha, ref in (line.split() for line in result.stdout.splitlines())}
    target = refs.get(f"{tag}^{{}}", refs.get(tag))
    if target != commit:
        raise ValueError(f"tag {version} already points to a different commit; it will not be moved")


def main() -> int:
    root = Path(__file__).resolve().parents[3]
    version = package_version(root / "Cargo.toml")
    try:
        publishing = validate_request(version, os.environ)
        if publishing:
            validate_tag(version, os.environ.get("GITHUB_SHA", ""))
    except (ValueError, subprocess.SubprocessError) as error:
        print(f"::error::{error}", file=sys.stderr)
        return 1
    prerelease = "-" in version.split("+", 1)[0]
    with Path(os.environ["GITHUB_OUTPUT"]).open("a", encoding="utf-8") as output:
        output.write(f"version={version}\nprerelease={str(prerelease).lower()}\n")
    mode = "publish to all configured channels" if publishing else "validate only; no publishing"
    print(f"Release {version}: {mode}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
