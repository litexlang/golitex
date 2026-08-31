#!/usr/bin/env python3
"""Bind the primary Example 54 verifier/compiler/Lean tracer atomically."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo


COVERAGE_DIR = Path(__file__).resolve().parent
ROOT = COVERAGE_DIR.parents[1]
LEAN_ROOT = ROOT / "lean"
sys.path.insert(0, str(COVERAGE_DIR))
import build_inventory as coverage  # noqa: E402
import kernel_check_examples as matrix  # noqa: E402


REPORT = COVERAGE_DIR / "tracer_gate_evidence.json"
TRACER = ROOT / "lean/examples/54_ComplexAlgebraicCalculation.lit"
CHECKED = TRACER.with_suffix(".lean")
CONFIG = TRACER.parent / "litex.config"
OUTPUT = ROOT / "tmp/2026-08-30/one-week-tolean-day1/54_ComplexAlgebraicCalculation.generated.lean"
VERIFIER = ROOT / "target/release/litex"
COMPILER = ROOT / "target/release/stmt_result_to_lean_compiler"
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom)\b|LitexObject|Litex\.Object|Set\.univ")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def run_envelope(output: str) -> dict[str, object]:
    try:
        value = json.loads(output)
    except json.JSONDecodeError as error:
        raise ValueError("verifier output is not one JSON document") from error
    if not isinstance(value, dict) or value.get("kind") != "run":
        raise ValueError("verifier output is not a run envelope")
    return value


def fail(message: str) -> int:
    print(message, file=sys.stderr)
    return 1


def main() -> int:
    olean_errors = matrix.lean_olean_precondition_errors()
    if olean_errors:
        return fail("Lean dependencies are not freshly built: " + olean_errors[0])
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    rust_before = coverage.rust_source_fingerprint()
    lean_before = coverage.lean_dependency_fingerprint()
    source_hash = sha256(TRACER)
    checked_hash = sha256(CHECKED)
    config_hash = sha256(CONFIG)

    build_started = time.monotonic()
    build = run(
        ["cargo", "build", "--release", "--bin", "litex", "--bin", "stmt_result_to_lean_compiler"],
        ROOT,
    )
    build_seconds = time.monotonic() - build_started
    rust_after_build = coverage.rust_source_fingerprint()
    if build.returncode != 0:
        return fail(str(matrix.first_error(build.stdout) or "release build failed"))
    if rust_before != rust_after_build:
        return fail("Rust sources changed while binding release binaries")
    verifier_hash = sha256(VERIFIER)
    compiler_hash = sha256(COMPILER)

    isolated_command = [
        str(VERIFIER),
        "-strict",
        "-isolated",
        "-f",
        str(TRACER),
    ]
    project_command = [str(VERIFIER), "-strict", "-f", str(TRACER)]
    isolated = run(isolated_command, ROOT)
    project = run(project_command, ROOT)
    try:
        isolated_run = run_envelope(isolated.stdout)
        project_run = run_envelope(project.stdout)
    except ValueError as error:
        return fail(str(error))
    if (
        isolated.returncode != 0
        or isolated_run.get("ok") is not True
        or isolated_run.get("error") is not None
    ):
        return fail("isolated strict verifier did not report success")
    if (
        project.returncode != 1
        or project_run.get("ok") is not False
        or not isinstance(project_run.get("error"), dict)
    ):
        return fail("project-mode trust-boundary negative gate changed behavior")
    if "25_ExplicitSourceAxioms.lit" not in project.stdout:
        return fail("project-mode negative gate did not stop at Example 25")

    compile_gate = run([str(COMPILER), "compile", str(TRACER), str(OUTPUT)], ROOT)
    if compile_gate.returncode != 0:
        return fail(str(matrix.first_error(compile_gate.stdout) or "compiler failed"))
    generated_gate = run(["lake", "env", "lean", str(OUTPUT)], LEAN_ROOT)
    if generated_gate.returncode != 0:
        return fail(str(matrix.first_error(generated_gate.stdout) or "generated Lean failed"))
    checked_gate = run(["lake", "env", "lean", str(CHECKED)], LEAN_ROOT)
    if checked_gate.returncode != 0:
        return fail(str(matrix.first_error(checked_gate.stdout) or "checked Lean failed"))

    rust_after = coverage.rust_source_fingerprint()
    lean_after = coverage.lean_dependency_fingerprint()
    if not rust_before == rust_after_build == rust_after:
        return fail("Rust sources changed during the primary tracer chain")
    if lean_before != lean_after:
        return fail("Lean dependencies changed during the primary tracer chain")
    if sha256(VERIFIER) != verifier_hash or sha256(COMPILER) != compiler_hash:
        return fail("release binary changed during the primary tracer chain")
    if sha256(TRACER) != source_hash or sha256(CHECKED) != checked_hash or sha256(CONFIG) != config_hash:
        return fail("primary tracer inputs changed during the gate")
    forbidden_paths = [CHECKED, OUTPUT]
    if any(FORBIDDEN.search(path.read_text(encoding="utf-8")) for path in forbidden_paths):
        return fail("primary tracer contains a forbidden construct")

    now = datetime.now(ZoneInfo("Asia/Shanghai")).strftime("%Y-%m-%d %H:%M:%S %Z")
    generated_hash = sha256(OUTPUT)
    evidence = {
        "schema_version": 2,
        "recorded_at": now,
        "updated_at": now,
        "lean_dependency_fingerprint_sha256": lean_before,
        "rust_source_fingerprint_sha256": rust_before,
        "current_valid": True,
        "invalidation": None,
        "verifier_binary": {"path": VERIFIER.relative_to(ROOT).as_posix(), "sha256": verifier_hash},
        "release_build": {"command": "cargo build --release --bin litex --bin stmt_result_to_lean_compiler", "exit": 0, "duration_seconds": round(build_seconds, 3)},
        "tracer": TRACER.relative_to(ROOT).as_posix(),
        "source_sha256": source_hash,
        "checked_in_lean": {"recorded_at": now, "path": CHECKED.relative_to(ROOT).as_posix(), "sha256": checked_hash, "kernel_command": "cd lean && lake env lean examples/54_ComplexAlgebraicCalculation.lean", "kernel_exit": 0},
        "project_mode_verifier": {"recorded_at": now, "command": "target/release/litex -strict -f lean/examples/54_ComplexAlgebraicCalculation.lit", "exit": project.returncode, "top_level_ok": False, "config_path": CONFIG.relative_to(ROOT).as_posix(), "config_sha256": config_hash, "first_failure": "lean/examples/25_ExplicitSourceAxioms.lit:10 strict mode rejects the explicit trust statement", "classification": "test_gap", "boundary": "Project mode loads the registered trust-boundary example; isolated strict mode is the primary positive envelope."},
        "isolated_verifier": {"recorded_at": now, "command": "target/release/litex -strict -isolated -f lean/examples/54_ComplexAlgebraicCalculation.lit", "exit": isolated.returncode, "top_level_ok": True, "strict_contract": True},
        "compiler": {"recorded_at": now, "binary_path": COMPILER.relative_to(ROOT).as_posix(), "binary_sha256": compiler_hash, "command": "target/release/stmt_result_to_lean_compiler compile lean/examples/54_ComplexAlgebraicCalculation.lit tmp/2026-08-30/one-week-tolean-day1/54_ComplexAlgebraicCalculation.generated.lean", "exit": 0, "generated_path": OUTPUT.relative_to(ROOT).as_posix(), "generated_sha256": generated_hash},
        "generated_drift": {"recorded_at": now, "command": "cmp generated checked-in", "exit": 0 if generated_hash == checked_hash else 1, "matches_checked_in": generated_hash == checked_hash},
        "generated_kernel": {"recorded_at": now, "command": "cd lean && lake env lean ../tmp/2026-08-30/one-week-tolean-day1/54_ComplexAlgebraicCalculation.generated.lean", "exit": 0},
        "forbidden_construct_scan": {"paths": [path.relative_to(ROOT).as_posix() for path in forbidden_paths], "forbidden": "sorry|admit|axiom|LitexObject|Litex.Object|Set.univ", "clean": True},
        "workspace_kernel": {"recorded_at": now, "command": "olean freshness precondition", "exit": 0},
    }
    REPORT.write_text(json.dumps(evidence, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print("bound primary Example 54 verifier/compiler/Lean tracer")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
