#!/usr/bin/env python3
"""Generate wix/std.wxs so the MSI installs the whole std/ tree.

cargo-wix compiles every .wxs under wix/. File/@Source paths must be relative
to the package root (Cargo.toml), not relative to wix/std.wxs. A FeatureRef to
Binaries attaches the harvested components to the default application feature.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

SCRIPT_DIRECTORY = Path(__file__).resolve().parent
REPOSITORY_ROOT = SCRIPT_DIRECTORY.parents[2]
DEFAULT_STD = REPOSITORY_ROOT / "std"
DEFAULT_OUTPUT = REPOSITORY_ROOT / "wix" / "std.wxs"

SKIP_NAMES = {"todo.md", ".DS_Store"}


def wix_id(prefix: str, relative: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9_.]", "_", relative.replace("\\", "/"))
    cleaned = cleaned.strip("._") or "root"
    if cleaned[0].isdigit():
        cleaned = f"_{cleaned}"
    return f"{prefix}_{cleaned}"


def collect_files(std_root: Path) -> list[Path]:
    files: list[Path] = []
    for path in sorted(std_root.rglob("*")):
        if not path.is_file():
            continue
        relative_parts = path.relative_to(std_root).parts
        if any(part.startswith(".") for part in relative_parts):
            continue
        if path.name in SKIP_NAMES:
            continue
        files.append(path)
    return files


def build_tree(std_root: Path, files: list[Path]) -> dict:
    root: dict = {"__files__": [], "__dirs__": {}}
    for path in files:
        relative = path.relative_to(std_root)
        node = root
        for part in relative.parts[:-1]:
            node = node["__dirs__"].setdefault(
                part, {"__files__": [], "__dirs__": {}}
            )
        node["__files__"].append(path)
    return root


def emit_components(
    lines: list[str], std_root: Path, files: list[Path], indent: str
) -> None:
    for file_path in files:
        file_rel = file_path.relative_to(std_root).as_posix()
        source = ("std/" + file_rel).replace("/", "\\")
        component_id = wix_id("StdComp", file_rel)
        file_id = wix_id("StdFile", file_rel)
        lines.append(f'{indent}<Component Id="{component_id}" Guid="*">')
        lines.append(
            f'{indent}  <File Id="{file_id}" Source="{source}" KeyPath="yes" />'
        )
        lines.append(f"{indent}</Component>")


def directory_tree_xml(std_root: Path, files: list[Path], indent: str = "      ") -> str:
    tree = build_tree(std_root, files)
    lines: list[str] = []

    def walk(node: dict, prefix_rel: str, level: int) -> None:
        pad = indent + ("  " * level)
        for name in sorted(node["__dirs__"]):
            child = node["__dirs__"][name]
            rel = f"{prefix_rel}/{name}" if prefix_rel else name
            child_id = wix_id("StdDir", rel)
            lines.append(f'{pad}<Directory Id="{child_id}" Name="{name}">')
            walk(child, rel, level + 1)
            lines.append(f"{pad}</Directory>")
        emit_components(lines, std_root, node["__files__"], pad)

    lines.append(f'{indent}<Directory Id="StandardLibrary" Name="std">')
    walk(tree, "", 1)
    lines.append(f"{indent}</Directory>")
    return "\n".join(lines)


def component_ids(std_root: Path, files: list[Path]) -> list[str]:
    return [wix_id("StdComp", path.relative_to(std_root).as_posix()) for path in files]


def render_wxs(std_root: Path, files: list[Path]) -> str:
    if not files:
        raise SystemExit(f"no files to package under {std_root}")
    tree = directory_tree_xml(std_root, files)
    refs = "\n".join(
        f'      <ComponentRef Id="{component_id}" />'
        for component_id in component_ids(std_root, files)
    )
    return f"""<?xml version="1.0" encoding="UTF-8"?>
<Wix xmlns="http://schemas.microsoft.com/wix/2006/wi">
  <Fragment>
    <DirectoryRef Id="APPLICATIONFOLDER">
{tree}
    </DirectoryRef>
  </Fragment>

  <Fragment>
    <FeatureRef Id="Binaries">
{refs}
    </FeatureRef>
  </Fragment>
</Wix>
"""


def generate(std_root: Path, output: Path) -> int:
    files = collect_files(std_root)
    text = render_wxs(std_root, files)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text, encoding="utf-8", newline="\n")
    return len(files)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--std",
        type=Path,
        default=DEFAULT_STD,
        help="path to the std directory (default: repository std/)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="path to write std.wxs (default: wix/std.wxs)",
    )
    args = parser.parse_args(argv)
    std_root = args.std.resolve()
    if not std_root.is_dir():
        print(f"std directory not found: {std_root}", file=sys.stderr)
        return 1
    count = generate(std_root, args.output.resolve())
    print(f"wrote {args.output} with {count} file(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
