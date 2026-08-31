#!/usr/bin/env python3
"""Bind the compiler integration baseline to one Rust source/test binary snapshot."""

from __future__ import annotations

import argparse
import collections
import csv
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo


COVERAGE_DIR = Path(__file__).resolve().parent
ROOT = COVERAGE_DIR.parents[1]
sys.path.insert(0, str(COVERAGE_DIR))
import build_inventory as coverage  # noqa: E402


TEST_NAME = "stmt_result_to_lean_compiler_tracers"
TEST_SOURCE = ROOT / "tests/integration/stmt_result_to_lean_compiler_tracers.rs"
FAILURE_LEDGER = COVERAGE_DIR / "integration_failure_families.tsv"
DEFAULT_REPORT = COVERAGE_DIR / "integration_gate_evidence.json"
RESULT_RE = re.compile(
    r"test result: (?:ok|FAILED)\. "
    r"(?P<passed>\d+) passed; (?P<failed>\d+) failed; "
    r"(?P<ignored>\d+) ignored; (?:\d+) measured; "
    r"(?P<filtered>\d+) filtered out; finished in (?P<seconds>[0-9.]+)s"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def cargo_test_binary(output: str) -> Path:
    executables: list[Path] = []
    for line in output.splitlines():
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            continue
        if message.get("reason") != "compiler-artifact":
            continue
        target = message.get("target", {})
        executable = message.get("executable")
        if target.get("name") == TEST_NAME and executable:
            executables.append(Path(str(executable)))
    if len(executables) != 1:
        raise ValueError(
            f"cargo identified {len(executables)} integration test executables"
        )
    path = executables[0]
    if not path.is_absolute():
        path = ROOT / path
    if not path.is_file():
        raise ValueError(f"cargo test executable is missing: {path}")
    return path.resolve()


def cargo_first_error(stdout: str, stderr: str) -> str:
    for line in stdout.splitlines():
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            continue
        if message.get("reason") != "compiler-message":
            continue
        diagnostic = message.get("message", {})
        if diagnostic.get("level") != "error":
            continue
        rendered = str(diagnostic.get("rendered") or "").strip()
        if rendered:
            lines = [line.strip() for line in rendered.splitlines() if line.strip()]
            return " | ".join(lines[:3])[:500]
        plain = str(diagnostic.get("message") or "").strip()
        if plain:
            return plain[:500]
    return next(
        (
            line.strip()[:500]
            for line in (stdout + "\n" + stderr).splitlines()
            if "error" in line.lower()
        ),
        "cargo integration build failed",
    )


def parse_test_totals(output: str) -> dict[str, int | float]:
    matches = list(RESULT_RE.finditer(output))
    if not matches:
        raise ValueError("integration output has no final test-result totals")
    match = matches[-1]
    return {
        "passed": int(match.group("passed")),
        "failed": int(match.group("failed")),
        "ignored": int(match.group("ignored")),
        "filtered": int(match.group("filtered")),
        "duration_seconds": float(match.group("seconds")),
    }


def parse_failure_names(output: str) -> list[str]:
    result_at = output.rfind("\ntest result:")
    failures_at = output.rfind("\nfailures:\n", 0, result_at)
    if failures_at < 0:
        return []
    section = output[failures_at:result_at]
    return sorted(
        re.findall(r"^    ([a-z][a-z0-9_]*)$", section, flags=re.MULTILINE)
    )


def failure_rows() -> list[dict[str, str]]:
    with FAILURE_LEDGER.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, default=DEFAULT_REPORT)
    args = parser.parse_args()
    report = args.report.resolve()
    if report != DEFAULT_REPORT.resolve():
        parser.error(f"--report must be {DEFAULT_REPORT.relative_to(ROOT)}")

    fingerprint_before = coverage.rust_source_fingerprint()
    cargo_command = [
        "cargo",
        "test",
        "--release",
        "--test",
        TEST_NAME,
        "--no-run",
        "--message-format=json",
    ]
    cargo = run(cargo_command)
    fingerprint_after_build = coverage.rust_source_fingerprint()
    if cargo.returncode != 0:
        print(cargo_first_error(cargo.stdout, cargo.stderr), file=sys.stderr)
        return 1
    if fingerprint_before != fingerprint_after_build:
        print("Rust sources changed while Cargo bound the test binary", file=sys.stderr)
        return 1

    try:
        binary = cargo_test_binary(cargo.stdout)
    except ValueError as error:
        print(error, file=sys.stderr)
        return 1
    binary_hash_before = sha256(binary)
    listed = run([str(binary), "--list"])
    listed_tests = sum(line.endswith(": test") for line in listed.stdout.splitlines())
    if listed.returncode != 0:
        print("integration test binary --list failed", file=sys.stderr)
        return 1

    executed = run([str(binary), "--nocapture"])
    combined_output = executed.stdout + executed.stderr
    try:
        totals = parse_test_totals(combined_output)
    except ValueError as error:
        print(error, file=sys.stderr)
        return 1
    failures = parse_failure_names(combined_output)
    ledger = failure_rows()
    ledger_failures = sorted(row["test"] for row in ledger)
    fingerprint_after_run = coverage.rust_source_fingerprint()
    binary_hash_after = sha256(binary)
    if fingerprint_after_run != fingerprint_before:
        print("Rust sources changed while the integration binary ran", file=sys.stderr)
        return 1
    if binary_hash_after != binary_hash_before:
        print("integration test binary changed while it ran", file=sys.stderr)
        return 1
    total = int(totals["passed"]) + int(totals["failed"]) + int(totals["ignored"])
    if listed_tests != total:
        print(f"--list reported {listed_tests} tests but the run reported {total}", file=sys.stderr)
        return 1
    if failures != ledger_failures:
        print("integration failures do not match the maintained ledger", file=sys.stderr)
        return 1

    classes = collections.Counter(row["current_class"] for row in ledger)
    relative_binary = binary.relative_to(ROOT).as_posix()
    evidence = {
        "schema_version": 1,
        "recorded_at": datetime.now(ZoneInfo("Asia/Shanghai")).strftime(
            "%Y-%m-%d %H:%M:%S %Z"
        ),
        "current_valid": True,
        "invalidation": None,
        "rust_source_fingerprint_sha256": fingerprint_before,
        "test_source": {
            "path": TEST_SOURCE.relative_to(ROOT).as_posix(),
            "sha256": sha256(TEST_SOURCE),
        },
        "test_binary": {"path": relative_binary, "sha256": binary_hash_after},
        "cargo_binding": {
            "command": " ".join(cargo_command),
            "exit": cargo.returncode,
            "source_fingerprint_before": fingerprint_before,
            "source_fingerprint_after": fingerprint_after_build,
        },
        "failure_ledger": {
            "path": FAILURE_LEDGER.relative_to(ROOT).as_posix(),
            "sha256": sha256(FAILURE_LEDGER),
        },
        "run": {
            "command": f"{relative_binary} --nocapture",
            "exit": executed.returncode,
            "duration_seconds": totals["duration_seconds"],
            "passed": totals["passed"],
            "failed": totals["failed"],
            "ignored": totals["ignored"],
            "total": total,
            "source_fingerprint_before": fingerprint_after_build,
            "source_fingerprint_after": fingerprint_after_run,
            "binary_sha256_before": binary_hash_before,
            "binary_sha256_after": binary_hash_after,
            "failure_names": failures,
        },
        "classification_counts": dict(sorted(classes.items())),
    }
    report.write_text(
        json.dumps(evidence, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(
        f"bound {total} integration tests: {totals['passed']} passed, "
        f"{totals['failed']} classified failures"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
