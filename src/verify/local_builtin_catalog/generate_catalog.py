#!/usr/bin/env python3
"""Generate and check the embedded local-builtin Litex schema catalog."""

from __future__ import annotations

import argparse
import hashlib
import re
from dataclasses import dataclass
from pathlib import Path


CATALOG_ROOT = Path(__file__).resolve().parent
GENERATED_CATALOG = CATALOG_ROOT / "generated_catalog.rs"
RULE_PART = re.compile(r"[a-z][a-z0-9_]*\Z")
FORBIDDEN_LITEX = re.compile(
    r"(?m)^\s*(?:trust|axiom|theorem|claim|prop|have|import|use)\b"
)


@dataclass(frozen=True)
class RuleSource:
    relative: Path
    rule_id: str
    theorem_name: str
    fingerprint: str


def schema_fingerprint(source: str) -> str:
    canonical = " ".join(source.split())
    payload = ("litex-local-schema-v1\0" + canonical).encode()
    return hashlib.sha256(payload).hexdigest()


def load_sources() -> list[RuleSource]:
    sources: list[RuleSource] = []
    seen_fingerprints: set[str] = set()
    for path in sorted(CATALOG_ROOT.rglob("*.lit")):
        relative = path.relative_to(CATALOG_ROOT)
        parts = relative.with_suffix("").parts
        if not parts or any(RULE_PART.fullmatch(part) is None for part in parts):
            raise ValueError(f"invalid local builtin path {relative}")
        source = path.read_text()
        lines = [line.strip() for line in source.splitlines() if line.strip()]
        if not lines or not lines[0].startswith("forall "):
            raise ValueError(f"{relative}: schema must start with forall")
        if FORBIDDEN_LITEX.search(source):
            raise ValueError(f"{relative}: schema contains an executable declaration")
        fingerprint = schema_fingerprint(source)
        if fingerprint in seen_fingerprints:
            raise ValueError(f"{relative}: duplicate semantic fingerprint {fingerprint}")
        seen_fingerprints.add(fingerprint)
        sources.append(
            RuleSource(
                relative=relative,
                rule_id=".".join(parts),
                theorem_name="_".join(parts),
                fingerprint=fingerprint,
            )
        )
    return sources


def render(sources: list[RuleSource]) -> str:
    lines = [
        "// @generated local builtin catalog; do not edit.",
        "pub(super) const GENERATED_LOCAL_BUILTIN_RULES: &[GeneratedLocalBuiltinRuleSource] = &[",
    ]
    for source in sources:
        include_path = source.relative.as_posix()
        lines.extend(
            [
                "    GeneratedLocalBuiltinRuleSource {",
                f'        id: "{source.rule_id}",',
                f'        semantic_fingerprint: "{source.fingerprint}",',
                f'        litex_source: include_str!("{include_path}"),',
                f'        lean_theorem_name: "{source.theorem_name}",',
                "    },",
            ]
        )
    lines.extend(["];", ""])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    generated = render(load_sources())
    if args.write:
        GENERATED_CATALOG.write_text(generated)
        print(f"wrote {GENERATED_CATALOG.relative_to(CATALOG_ROOT.parent.parent.parent)}")
        return 0
    if not GENERATED_CATALOG.exists() or GENERATED_CATALOG.read_text() != generated:
        print("local builtin catalog is stale")
        return 1
    print("local builtin catalog is current")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
