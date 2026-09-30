#!/usr/bin/env python3
"""Run unskipped ```litex``` fences in README.md and docs/**/*.md.

Skip a fence when the previous non-empty line is exactly:
  <!-- litex:skip-test -->

Usage (from repo root, after `cargo build --release`):
  python3 tests/tooling/run_docs_markdown_files.py
  python3 tests/tooling/run_docs_markdown_files.py --litex target/release/litex
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

SKIP_MARKER = "<!-- litex:skip-test -->"


def extract_litex_fenced_blocks(markdown: str) -> list[tuple[int, str]]:
    blocks: list[tuple[int, str]] = []
    in_litex = False
    skip_this = False
    current: list[str] = []
    prev_non_empty: str | None = None
    fence_open_line = 0

    for line_index, line in enumerate(markdown.splitlines(), start=1):
        trimmed_start = line.lstrip()
        if trimmed_start.startswith("```"):
            info = trimmed_start[3:].strip()
            if in_litex:
                if not skip_this:
                    body = "\n".join(current).strip()
                    if body:
                        blocks.append((fence_open_line, body))
                current = []
                in_litex = False
                skip_this = False
                prev_non_empty = None
            elif info == "litex":
                in_litex = True
                fence_open_line = line_index
                skip_this = prev_non_empty == SKIP_MARKER
                current = []
        elif in_litex:
            if not skip_this:
                current.append(line)
        else:
            t = line.strip()
            if t:
                prev_non_empty = t
    return blocks


def collect_markdown_files(repo: Path) -> list[Path]:
    files: list[Path] = []
    readme = repo / "README.md"
    if readme.is_file():
        files.append(readme)
    docs = repo / "docs"
    if docs.is_dir():
        files.extend(sorted(docs.rglob("*.md")))
    return files


def run_block(litex: Path, code: str, cwd: Path) -> tuple[bool, str]:
    with tempfile.NamedTemporaryFile(
        mode="w",
        suffix=".lit",
        delete=False,
        encoding="utf-8",
    ) as tmp:
        tmp.write(code)
        if not code.endswith("\n"):
            tmp.write("\n")
        path = Path(tmp.name)
    try:
        proc = subprocess.run(
            [str(litex), "-f", str(path)],
            cwd=str(cwd),
            capture_output=True,
            text=True,
        )
        out = (proc.stdout or "") + (proc.stderr or "")
        if proc.returncode != 0:
            return False, out.strip() or f"exit {proc.returncode}"
        try:
            data = json.loads(proc.stdout)
        except json.JSONDecodeError as err:
            return False, f"non-JSON stdout ({err}): {proc.stdout[:500]}"
        if data.get("kind") != "run":
            return False, f"unexpected kind: {data.get('kind')!r}\n{proc.stdout[:500]}"
        if data.get("success") is not True:
            return False, proc.stdout.strip()
        if data.get("session_error") is not None:
            return False, proc.stdout.strip()
        return True, "ok"
    finally:
        path.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--litex",
        type=Path,
        default=Path("target/release/litex"),
        help="path to litex binary",
    )
    parser.add_argument(
        "--repo",
        type=Path,
        default=Path("."),
        help="repository root",
    )
    args = parser.parse_args()
    repo = args.repo.resolve()
    litex = args.litex if args.litex.is_absolute() else (repo / args.litex)
    if not litex.is_file():
        print(f"missing litex binary: {litex}", file=sys.stderr)
        print("run: cargo build --release", file=sys.stderr)
        return 2

    failures: list[str] = []
    total = 0
    for md_path in collect_markdown_files(repo):
        rel = md_path.relative_to(repo)
        text = md_path.read_text(encoding="utf-8")
        blocks = extract_litex_fenced_blocks(text)
        for index, (line, code) in enumerate(blocks):
            total += 1
            label = f"{rel} ```litex```#{index} (md line {line})"
            ok, detail = run_block(litex, code, repo)
            if ok:
                print(f"PASS {label}")
            else:
                print(f"FAIL {label}")
                print(detail)
                print("---")
                failures.append(label)

    print()
    print(f"ran {total} blocks; {len(failures)} failed")
    if failures:
        print("failed:")
        for label in failures:
            print(f"  - {label}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
