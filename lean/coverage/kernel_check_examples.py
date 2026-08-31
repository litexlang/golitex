#!/usr/bin/env python3
"""Compile every registered Lean example into tmp and kernel-check both copies."""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import subprocess
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo


ROOT = Path(__file__).resolve().parents[2]
EXAMPLES = ROOT / "lean/examples"
LEAN_ROOT = ROOT / "lean"
TMP_ROOT = ROOT / "tmp"
COMPILER = ROOT / "target/release/stmt_result_to_lean_compiler"
DEFAULT_REPORT = ROOT / "lean/coverage/example_kernel_matrix.json"


def sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_dependency_fingerprint() -> str:
    digest = hashlib.sha256()
    paths = list((LEAN_ROOT / "Litex").rglob("*.lean"))
    paths.extend(
        path
        for path in (
            LEAN_ROOT / "Litex.lean",
            LEAN_ROOT / "lakefile.lean",
            LEAN_ROOT / "lean-toolchain",
        )
        if path.exists()
    )
    for path in sorted(set(paths)):
        digest.update(path.relative_to(ROOT).as_posix().encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def lean_olean_precondition_errors() -> list[str]:
    pairs = [(LEAN_ROOT / "Litex.lean", LEAN_ROOT / ".lake/build/lib/lean/Litex.olean")]
    for source in sorted((LEAN_ROOT / "Litex").rglob("*.lean")):
        relative = source.relative_to(LEAN_ROOT).with_suffix(".olean")
        pairs.append((source, LEAN_ROOT / ".lake/build/lib/lean" / relative))
    errors: list[str] = []
    for source, olean in pairs:
        if not olean.exists():
            errors.append(f"missing {olean.relative_to(ROOT).as_posix()}")
        elif olean.stat().st_mtime_ns < source.stat().st_mtime_ns:
            errors.append(
                f"stale {olean.relative_to(ROOT).as_posix()} for "
                f"{source.relative_to(ROOT).as_posix()}"
            )
    return errors


def first_error(output: str) -> str | None:
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    for line in lines:
        if "error:" in line.lower() or "failed" in line.lower():
            return line[:500]
    return lines[0][:500] if lines else None


def kernel_class(exit_code: int | None, output: str) -> str:
    if exit_code is None:
        return "not_run"
    if exit_code == 0:
        return "pass"
    if "object file" in output and "does not exist" in output:
        return "infrastructure_failure"
    return "kernel_reject"


def run(command: list[str], cwd: Path) -> tuple[int, str]:
    completed = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    return completed.returncode, completed.stdout


def registered_sources() -> list[Path]:
    config = (EXAMPLES / "litex.config").read_text(encoding="utf-8")
    return [
        source
        for source in sorted(EXAMPLES.glob("*.lit"))
        if f'"./{source.name}"' in config
    ]


def check_example(source: Path, output_dir: Path) -> dict[str, object]:
    checked = source.with_suffix(".lean")
    generated = output_dir / checked.name
    compiler_exit, compiler_output = run(
        [str(COMPILER), "compile", str(source), str(generated)], ROOT
    )
    if compiler_exit == 0:
        generated_kernel_exit, generated_kernel_output = run(
            ["lake", "env", "lean", str(generated)], LEAN_ROOT
        )
    else:
        generated_kernel_exit = None
        generated_kernel_output = ""
    checked_kernel_exit, checked_kernel_output = run(
        ["lake", "env", "lean", str(checked)], LEAN_ROOT
    )
    generated_hash = sha256(generated)
    checked_hash = sha256(checked)
    return {
        "example": source.name,
        "source_sha256": sha256(source),
        "checked_in_path": checked.relative_to(ROOT).as_posix(),
        "checked_in_sha256": checked_hash,
        "compiler_exit": compiler_exit,
        "generated_path": generated.relative_to(ROOT).as_posix(),
        "generated_sha256": generated_hash,
        "generated_kernel_exit": generated_kernel_exit,
        "generated_kernel_class": kernel_class(
            generated_kernel_exit, generated_kernel_output
        ),
        "generated_kernel_first_error": first_error(generated_kernel_output),
        "checked_in_kernel_exit": checked_kernel_exit,
        "checked_in_kernel_class": kernel_class(
            checked_kernel_exit, checked_kernel_output
        ),
        "checked_in_kernel_first_error": first_error(checked_kernel_output),
        "matches_checked_in": bool(generated_hash and generated_hash == checked_hash),
        "compiler_first_error": first_error(compiler_output),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--report", type=Path, default=DEFAULT_REPORT)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()

    output_dir = args.output_dir.resolve()
    tmp_root = TMP_ROOT.resolve()
    if output_dir != tmp_root and tmp_root not in output_dir.parents:
        parser.error("--output-dir must be inside the workspace tmp/ directory")
    if args.jobs < 1 or args.jobs > 8:
        parser.error("--jobs must be between 1 and 8")
    if not COMPILER.exists():
        parser.error(f"release compiler does not exist: {COMPILER}")
    olean_errors_before = lean_olean_precondition_errors()
    if olean_errors_before:
        parser.error(
            "Lean dependencies are not freshly built; run `cd lean && lake build`: "
            + olean_errors_before[0]
        )
    output_dir.mkdir(parents=True, exist_ok=True)

    sources = registered_sources()
    dependency_fingerprint_before = lean_dependency_fingerprint()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        rows = list(executor.map(lambda source: check_example(source, output_dir), sources))
    dependency_fingerprint_after = lean_dependency_fingerprint()
    olean_errors_after = lean_olean_precondition_errors()
    rows.sort(key=lambda row: str(row["example"]))
    totals = {
        "registered": len(rows),
        "compiler_pass": sum(row["compiler_exit"] == 0 for row in rows),
        "matches_checked_in": sum(row["matches_checked_in"] for row in rows),
    }
    for prefix in ("generated_kernel", "checked_in_kernel"):
        for classification in (
            "pass",
            "kernel_reject",
            "infrastructure_failure",
            "not_run",
        ):
            totals[f"{prefix}_{classification}"] = sum(
                row[f"{prefix}_class"] == classification for row in rows
            )
    report = {
        "schema_version": 2,
        "recorded_at": datetime.now(ZoneInfo("Asia/Shanghai")).strftime(
            "%Y-%m-%d %H:%M:%S %Z"
        ),
        "command": (
            "python3 lean/coverage/kernel_check_examples.py "
            f"--output-dir {output_dir.relative_to(ROOT).as_posix()} --jobs {args.jobs}"
        ),
        "compiler_path": COMPILER.relative_to(ROOT).as_posix(),
        "compiler_sha256": sha256(COMPILER),
        "lean_dependency_fingerprint_before": dependency_fingerprint_before,
        "lean_dependency_fingerprint_after": dependency_fingerprint_after,
        "lean_dependency_stable_during_run": (
            dependency_fingerprint_before == dependency_fingerprint_after
        ),
        "core_olean_present_after_run": (
            LEAN_ROOT / ".lake/build/lib/lean/Litex/Core.olean"
        ).exists(),
        "olean_precondition_errors_before": olean_errors_before,
        "olean_precondition_errors_after": olean_errors_after,
        "totals": totals,
        "rows": rows,
    }
    args.report.write_text(
        json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(totals, sort_keys=True))
    if dependency_fingerprint_before != dependency_fingerprint_after:
        print("Lean dependency sources changed during the matrix run")
    if olean_errors_after:
        print("Lean object dependencies became missing or stale during the matrix run")
    failures = [
        row
        for row in rows
        if row["compiler_exit"] != 0
        or row["generated_kernel_class"] != "pass"
        or row["checked_in_kernel_class"] != "pass"
    ]
    for row in failures:
        print(
            f"{row['example']}: compiler={row['compiler_exit']} "
            f"generated_kernel={row['generated_kernel_class']} "
            f"checked_kernel={row['checked_in_kernel_class']} "
            f"compiler_error={row['compiler_first_error']} "
            f"generated_error={row['generated_kernel_first_error']} "
            f"checked_error={row['checked_in_kernel_first_error']}"
        )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
