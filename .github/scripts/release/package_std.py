#!/usr/bin/env python3
"""Copy distributable std source without local journals or knowledge caches."""

import argparse
from pathlib import Path
import shutil


def source_files(root: Path) -> list[Path]:
    files = []
    for path in sorted(root.rglob("*")):
        if not path.is_file():
            continue
        parts = path.relative_to(root).parts
        if any(part.startswith(".") or part == "__litex_knowledge_base__" for part in parts):
            continue
        if path.name == "todo.md":
            continue
        files.append(path)
    return files


def copy_std(source: Path, destination: Path) -> None:
    if not (source / "basics/litex.config").is_file():
        raise ValueError(f"missing std/basics/litex.config under {source}")
    destination.mkdir(parents=True)
    for path in source_files(source):
        output = destination / path.relative_to(source)
        output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    arguments = parser.parse_args()
    copy_std(arguments.source, arguments.destination)
