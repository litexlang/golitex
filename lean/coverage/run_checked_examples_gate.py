#!/usr/bin/env python3
"""Kernel-check all registered checked-in Lean examples without the Rust compiler."""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import sys
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo


COVERAGE_DIR = Path(__file__).resolve().parent
ROOT = COVERAGE_DIR.parents[1]
LEAN_ROOT = ROOT / "lean"
REPORT = COVERAGE_DIR / "checked_example_kernel_evidence.json"
sys.path.insert(0, str(COVERAGE_DIR))
import kernel_check_examples as matrix  # noqa: E402


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(source: Path) -> dict[str, object]:
    checked = source.with_suffix(".lean")
    exit_code, output = matrix.run(["lake", "env", "lean", str(checked)], LEAN_ROOT)
    return {
        "example": source.name,
        "source_sha256": sha256(source),
        "checked_in_path": checked.relative_to(ROOT).as_posix(),
        "checked_in_sha256": sha256(checked),
        "kernel_exit": exit_code,
        "kernel_class": matrix.kernel_class(exit_code, output),
        "kernel_first_error": matrix.first_error(output),
        "forbidden_hits": matrix.forbidden_output_hits(checked),
    }


def totals(rows: list[dict[str, object]]) -> dict[str, int]:
    return {
        "registered": len(rows),
        "pass": sum(row["kernel_class"] == "pass" for row in rows),
        "kernel_reject": sum(row["kernel_class"] == "kernel_reject" for row in rows),
        "infrastructure_failure": sum(row["kernel_class"] == "infrastructure_failure" for row in rows),
        "forbidden_rows": sum(bool(row["forbidden_hits"]) for row in rows),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1 or args.jobs > 8:
        parser.error("--jobs must be between 1 and 8")
    olean_before = matrix.lean_olean_precondition_errors()
    if olean_before:
        parser.error("Lean dependencies are not freshly built: " + olean_before[0])

    sources = matrix.registered_sources()
    inputs_before = matrix.example_input_fingerprint(sources)
    lean_before = matrix.lean_dependency_fingerprint()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        rows = list(executor.map(check, sources))
    rows.sort(key=lambda row: str(row["example"]))
    inputs_after = matrix.example_input_fingerprint(sources)
    lean_after = matrix.lean_dependency_fingerprint()
    olean_after = matrix.lean_olean_precondition_errors()
    stable = inputs_before == inputs_after and lean_before == lean_after and not olean_after
    counts = totals(rows)
    report = {
        "schema_version": 1,
        "recorded_at": datetime.now(ZoneInfo("Asia/Shanghai")).strftime("%Y-%m-%d %H:%M:%S %Z"),
        "command": "python3 lean/coverage/run_checked_examples_gate.py --jobs " + str(args.jobs),
        "current_valid": stable,
        "example_input_fingerprint_before": inputs_before,
        "example_input_fingerprint_after": inputs_after,
        "lean_dependency_fingerprint_before": lean_before,
        "lean_dependency_fingerprint_after": lean_after,
        "olean_precondition_errors_before": olean_before,
        "olean_precondition_errors_after": olean_after,
        "totals": counts,
        "rows": rows,
    }
    REPORT.write_text(json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(counts, sort_keys=True))
    if not stable:
        print("checked-example snapshot changed during the gate")
    for row in rows:
        if row["kernel_class"] != "pass" or row["forbidden_hits"]:
            print(f"{row['example']}: {row['kernel_class']}: {row['kernel_first_error']}")
    return 0 if stable and counts["pass"] == counts["registered"] and counts["forbidden_rows"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
