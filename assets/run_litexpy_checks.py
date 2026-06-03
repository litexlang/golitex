#!/usr/bin/env python3
"""Run Litex example and markdown checks through litexpy.

This is a lightweight Python analogue of `cargo test run_examples`: it keeps
one interactive `litexpy.Runner`, runs independent files/snippets one by one,
and clears the runner between items.
"""

from __future__ import annotations

import argparse
import json
import os
import shlex
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
SKIP_MARKER = "<!-- litex:skip-test -->"
STD_IMPORT_EXAMPLES = ROOT / "examples" / "_internal" / "std_imports"
MANUAL_DIR = ROOT / "docs" / "Manual"
MECHANICS_DIR = ROOT / "scripts" / "The-Mechanics-of-Litex-Proof"


@dataclass(frozen=True)
class CheckItem:
    label: str
    kind: str
    path: Path
    source: str | None = None


def main() -> None:
    args = parse_args()
    litexpy = import_litexpy()
    command = default_litex_command(args.litex_command)
    items = collect_items(args)
    if args.limit is not None:
        items = items[: args.limit]

    if not items:
        print("no Litex check items selected")
        return

    print(f"litex command: {shlex.join(command)}")
    print(f"selected {len(items)} item(s)")

    failed: list[tuple[CheckItem, str]] = []
    durations: list[tuple[str, float]] = []
    start_all = time.perf_counter()

    with litexpy.Runner(command=command, run_timeout=args.timeout) as runner:
        for index, item in enumerate(items, start=1):
            print(f"[{index}/{len(items)}] {item.label}")
            start_item = time.perf_counter()
            ok, output = run_item(runner, item, args.timeout)
            duration_ms = elapsed_ms(start_item)
            durations.append((item.label, duration_ms))

            if ok:
                print(f"  OK {duration_ms:.2f} ms")
                continue

            print(f"  FAILED {duration_ms:.2f} ms")
            print(output)
            failed.append((item, output))
            if not args.keep_going:
                break

    print_slowest(durations)
    print(f"wall: {elapsed_ms(start_all):.2f} ms")

    if failed:
        print("--- failed items ---")
        for item, _ in failed:
            print(item.label)
        raise SystemExit(1)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--target",
        choices=["tmp", "run-examples", "mechanics"],
        default="tmp",
        help="Built-in check set. Use --lit/--md to add explicit paths.",
    )
    parser.add_argument(
        "--include-std",
        action="store_true",
        help="Include examples/_internal/std_imports in --target run-examples.",
    )
    parser.add_argument(
        "--lit",
        action="append",
        default=[],
        help="Additional .lit file or directory to check. Can be repeated.",
    )
    parser.add_argument(
        "--md",
        action="append",
        default=[],
        help="Additional markdown file or directory whose ```litex``` blocks are checked.",
    )
    parser.add_argument("--limit", type=int, help="Run only the first N selected items.")
    parser.add_argument(
        "--keep-going",
        action="store_true",
        help="Continue after a failing file or snippet.",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=30,
        help="Per-run litexpy timeout in seconds.",
    )
    parser.add_argument(
        "--litex-command",
        help="Command for litexpy.Runner, for example 'litex' or 'cargo run --quiet --'.",
    )
    return parser.parse_args()


def collect_items(args: argparse.Namespace) -> list[CheckItem]:
    items: list[CheckItem] = []
    if args.target == "tmp":
        items.extend(collect_tmp_lit_items())
    elif args.target == "run-examples":
        items.extend(collect_run_examples_items(include_std=args.include_std))
    elif args.target == "mechanics":
        items.extend(collect_markdown_items([MECHANICS_DIR]))

    items.extend(collect_lit_items(resolve_paths(args.lit)))
    items.extend(collect_markdown_items(resolve_paths(args.md)))
    return dedupe_items(items)


def collect_tmp_lit_items() -> list[CheckItem]:
    paths: list[Path] = []
    for pattern in (
        "examples/tmp.lit",
        "examples/_internal/regression/tmp*.lit",
        "examples/_internal/scratch/tmp*.lit",
        "examples/_internal/std_imports/tmp*.lit",
    ):
        paths.extend(sorted(ROOT.glob(pattern)))
    return [lit_item(path) for path in paths if path.is_file()]


def collect_run_examples_items(include_std: bool) -> list[CheckItem]:
    lit_paths = collect_lit_files(ROOT / "examples")
    if not include_std:
        lit_paths = [path for path in lit_paths if not path.is_relative_to(STD_IMPORT_EXAMPLES)]

    items = [lit_item(path) for path in lit_paths]
    manual_markdown = collect_markdown_files(MANUAL_DIR)
    items.extend(collect_markdown_items(manual_markdown))

    docs_dir = ROOT / "docs"
    remaining_markdown: list[Path] = []
    readme_path = ROOT / "README.md"
    if readme_path.is_file():
        remaining_markdown.append(readme_path)
    for path in collect_markdown_files(docs_dir):
        if not path.is_relative_to(MANUAL_DIR):
            remaining_markdown.append(path)
    items.extend(collect_markdown_items(remaining_markdown))
    return items


def collect_lit_items(paths: Iterable[Path]) -> list[CheckItem]:
    out: list[CheckItem] = []
    for path in paths:
        if path.is_dir():
            out.extend(lit_item(child) for child in collect_lit_files(path))
        elif path.is_file() and path.suffix == ".lit":
            out.append(lit_item(path))
    return out


def collect_markdown_items(paths: Iterable[Path]) -> list[CheckItem]:
    out: list[CheckItem] = []
    for path in paths:
        md_paths = collect_markdown_files(path) if path.is_dir() else [path]
        for md_path in md_paths:
            if not md_path.is_file() or md_path.suffix != ".md":
                continue
            markdown = md_path.read_text(encoding="utf-8")
            for block_index, (line_number, block) in enumerate(
                extract_litex_fenced_blocks(markdown)
            ):
                label = (
                    f"{relative_label(md_path)} ```litex```#{block_index} "
                    f"(md line {line_number})"
                )
                out.append(CheckItem(label=label, kind="markdown", path=md_path, source=block))
    return out


def lit_item(path: Path) -> CheckItem:
    return CheckItem(label=relative_label(path), kind="lit", path=path)


def run_item(runner: Any, item: CheckItem, timeout: float) -> tuple[bool, str]:
    try:
        safe_clear(runner)
        if item.kind == "lit":
            item.path.read_text(encoding="utf-8")
            results = runner.run(run_file_command(item.path), timeout=timeout)
        else:
            assert item.source is not None
            results = run_markdown_snippet(runner, item.path, item.source, timeout)
        ok = results_are_successful(results)
        return ok, "" if ok else format_results(results)
    except Exception as error:  # noqa: BLE001 - harness output should preserve verifier failures.
        return False, f"{type(error).__name__}: {error}"
    finally:
        safe_clear(runner)


def run_markdown_snippet(runner: Any, markdown_path: Path, source: str, timeout: float) -> Any:
    with tempfile.NamedTemporaryFile(
        mode="w",
        suffix=".lit",
        prefix=".litexpy-snippet-",
        dir=markdown_path.parent,
        delete=False,
        encoding="utf-8",
    ) as tmp_file:
        tmp_path = Path(tmp_file.name)
        tmp_file.write(source)
        if not source.endswith("\n"):
            tmp_file.write("\n")

    try:
        return runner.run(run_file_command(tmp_path), timeout=timeout)
    finally:
        try:
            tmp_path.unlink()
        except OSError:
            pass


def run_file_command(path: Path) -> str:
    return 'run_file "{}"'.format(str(path.resolve()).replace('"', '\\"'))


def safe_clear(runner: Any) -> None:
    try:
        runner.clear()
    except Exception:
        pass


def results_are_successful(results: Any) -> bool:
    seen = False
    for result in walk_result_dicts(results):
        seen = True
        if result.get("result") != "success":
            return False
    return seen


def walk_result_dicts(value: Any) -> Iterable[dict[str, Any]]:
    if isinstance(value, dict):
        yield value
        for nested in value.get("inside_results", []):
            yield from walk_result_dicts(nested)
        previous_error = value.get("previous_error")
        if previous_error is not None:
            yield from walk_result_dicts(previous_error)
    elif isinstance(value, list):
        for item in value:
            yield from walk_result_dicts(item)


def format_results(results: Any) -> str:
    return json.dumps(results, indent=2, ensure_ascii=False)


def extract_litex_fenced_blocks(markdown: str) -> list[tuple[int, str]]:
    blocks: list[tuple[int, str]] = []
    in_litex = False
    skip_this_block = False
    current: list[str] = []
    prev_non_empty_outside_block: str | None = None
    fence_open_line = 0

    for line_index, line in enumerate(markdown.splitlines(), start=1):
        trimmed_start = line.lstrip()
        if trimmed_start.startswith("```"):
            info = trimmed_start[3:].strip()
            if in_litex:
                if not skip_this_block:
                    block = "\n".join(current).strip()
                    if block:
                        blocks.append((fence_open_line, block))
                in_litex = False
                skip_this_block = False
                current = []
                prev_non_empty_outside_block = None
            elif info == "litex":
                in_litex = True
                fence_open_line = line_index
                skip_this_block = prev_non_empty_outside_block == SKIP_MARKER
                current = []
        elif in_litex:
            if not skip_this_block:
                current.append(line)
        else:
            stripped = line.strip()
            if stripped:
                prev_non_empty_outside_block = stripped
    return blocks


def collect_lit_files(root: Path) -> list[Path]:
    if not root.is_dir():
        return []
    return sorted(path for path in root.rglob("*.lit") if path.is_file())


def collect_markdown_files(root: Path) -> list[Path]:
    if not root.is_dir():
        return []
    return sorted(path for path in root.rglob("*.md") if path.is_file())


def resolve_paths(raw_paths: Iterable[str]) -> list[Path]:
    out: list[Path] = []
    for raw_path in raw_paths:
        path = Path(raw_path)
        if not path.is_absolute():
            path = ROOT / path
        out.append(path)
    return out


def dedupe_items(items: list[CheckItem]) -> list[CheckItem]:
    seen: set[tuple[str, str]] = set()
    out: list[CheckItem] = []
    for item in items:
        key = (item.kind, item.label)
        if key in seen:
            continue
        seen.add(key)
        out.append(item)
    return out


def relative_label(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


def print_slowest(durations: list[tuple[str, float]]) -> None:
    if not durations:
        return
    count = min(10, len(durations))
    print(f"--- slowest runs: top {count} of {len(durations)} ---")
    for index, (label, duration_ms) in enumerate(
        sorted(durations, key=lambda item: item[1], reverse=True)[:count],
        start=1,
    ):
        print(f"  {index:>2}. {duration_ms:.2f} ms  {label}")


def elapsed_ms(start: float) -> float:
    return (time.perf_counter() - start) * 1000.0


def import_litexpy() -> Any:
    candidates = [
        ROOT.parent / "litexpy" / "src",
        ROOT / "litexpy" / "src",
    ]
    for candidate in candidates:
        if candidate.is_dir():
            sys.path.insert(0, str(candidate))
            import litexpy  # type: ignore

            return litexpy

    import litexpy  # type: ignore

    if not hasattr(litexpy.Runner, "sandbox_run"):
        raise RuntimeError(
            "installed litexpy is too old; expected Runner.sandbox_run. "
            "Use ../litexpy/src or upgrade litexpy."
        )
    return litexpy


def default_litex_command(override: str | None) -> list[str]:
    if override:
        return shlex.split(override)
    env_command = os.environ.get("LITEXPY_LITEX_COMMAND")
    if env_command:
        return shlex.split(env_command)
    cargo_toml = ROOT / "Cargo.toml"
    if cargo_toml.is_file():
        return ["cargo", "run", "--quiet", "--manifest-path", str(cargo_toml), "--"]
    return ["litex"]


if __name__ == "__main__":
    main()
