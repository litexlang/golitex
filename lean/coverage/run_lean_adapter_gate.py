#!/usr/bin/env python3
"""Bind the generated literal-adapter #check gate to one coherent source snapshot."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo


COVERAGE_DIR = Path(__file__).resolve().parent
ROOT = COVERAGE_DIR.parents[1]
LEAN_ROOT = ROOT / "lean"
sys.path.insert(0, str(COVERAGE_DIR))
import build_inventory as coverage  # noqa: E402
import kernel_check_examples as matrix  # noqa: E402


REPORT = COVERAGE_DIR / "lean_adapter_gate_evidence.json"
CHECKS = COVERAGE_DIR / "LeanAdapterSymbols.lean"
LEDGER = COVERAGE_DIR / "lean_adapter_symbols.tsv"
INVENTORY = COVERAGE_DIR / "inventory.json"


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


def fail(message: str) -> int:
    print(message, file=sys.stderr)
    return 1


def main() -> int:
    source_before = coverage.inventory_source_fingerprint()
    generated = run(
        [sys.executable, "lean/coverage/build_inventory.py", "generate"], ROOT
    )
    if generated.returncode != 0:
        return fail("coverage inventory generation failed; evidence was not replaced")

    inventory = json.loads(INVENTORY.read_text(encoding="utf-8"))
    stored_source = inventory["source_fingerprint_sha256"]
    source_after_generate = coverage.inventory_source_fingerprint()
    if not source_before == stored_source == source_after_generate:
        return fail("source changed while generating the adapter surface")

    olean_errors = matrix.lean_olean_precondition_errors()
    if olean_errors:
        return fail("Lean dependencies are not freshly built: " + olean_errors[0])

    lean_before = coverage.lean_dependency_fingerprint()
    rust_before = coverage.rust_source_fingerprint()
    checks_hash_before = sha256(CHECKS)
    ledger_hash_before = sha256(LEDGER)
    symbol_count = int(inventory["summary"]["lean_literal_adapter_symbols"])
    gate = run(["lake", "env", "lean", "coverage/LeanAdapterSymbols.lean"], LEAN_ROOT)
    source_after_gate = coverage.inventory_source_fingerprint()
    lean_after = coverage.lean_dependency_fingerprint()
    rust_after = coverage.rust_source_fingerprint()
    if gate.returncode != 0:
        return fail(str(matrix.first_error(gate.stdout) or "Lean gate failed"))
    if source_after_gate != stored_source:
        return fail("source changed while Lean checked the adapter surface")
    if lean_after != lean_before or rust_after != rust_before:
        return fail("Lean or Rust dependency fingerprint changed during the adapter gate")
    if sha256(CHECKS) != checks_hash_before or sha256(LEDGER) != ledger_hash_before:
        return fail("generated adapter artifacts changed during the Lean gate")

    recorded_at = datetime.now(ZoneInfo("Asia/Shanghai")).strftime(
        "%Y-%m-%d %H:%M:%S %Z"
    )
    evidence = {
        "schema_version": 2,
        "recorded_at": recorded_at,
        "lean_dependency_fingerprint_sha256": lean_before,
        "rust_source_fingerprint_sha256": rust_before,
        "inventory_source_fingerprint_sha256": stored_source,
        "current_valid": True,
        "literal_symbol_count": symbol_count,
        "checks_path": CHECKS.relative_to(ROOT).as_posix(),
        "checks_sha256": checks_hash_before,
        "ledger_path": LEDGER.relative_to(ROOT).as_posix(),
        "ledger_sha256": ledger_hash_before,
        "ledger_updated_at": datetime.fromtimestamp(
            LEDGER.stat().st_mtime, ZoneInfo("Asia/Shanghai")
        ).strftime("%Y-%m-%d %H:%M:%S %Z"),
        "command": "cd lean && lake env lean coverage/LeanAdapterSymbols.lean",
        "exit": gate.returncode,
        "scope": "Every literal Litex.* symbol found in src/stmt_result_to_lean_compiler; namespace-only dynamic prefixes excluded.",
        "boundary": "Name/type availability is kernel-checked. Rule-ID dispatch, certificate validation, dynamic theorem families, and generated proof terms still require Result-driven tracers.",
    }
    REPORT.write_text(
        json.dumps(evidence, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(
        f"bound {symbol_count} literal Lean adapters at source {stored_source[:12]}..."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
