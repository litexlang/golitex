"""Audit existing Algebra interfaces against the original LADR 3A/3B hypotheses."""

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
USE = HERE / "existing"
spec = importlib.util.spec_from_file_location("linear_checks", HERE / "check.py")
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
base = checks.base
common = checks.common
IDS = ["3.1", "3.4", "3.7", "3.10", "3.11", "3.13", "3.14", "3.15",
       "3.16", "3.18", "3.19", "3.21", "3.22", "3.24"]


def boundaries():
    journal = json.loads((USE / "session.json").read_text())
    prefix = [r["source"] for r in journal["runs"]
              if r["response"]["run_result"] == "success"]
    assert len(prefix) == journal["accepted_statements"] == 33
    canonical = "# Original-hypothesis reuse for LADR 3A and 3B.\n\n"
    canonical += "\n\n".join(prefix)
    assert (USE / "main.lit").read_text().strip() == canonical.strip()
    expected = [(r["source"], r["expected_success"]) for r in journal["boundaries"]]
    assert len(expected) == 6 and sum(not success for _, success in expected) == 3
    digest = hashlib.sha256(json.dumps([prefix, expected]).encode()).hexdigest()
    before = base.checks.snapshot(USE)
    receipt = USE / "boundaries.json"
    if receipt.exists():
        old = json.loads(receipt.read_text())
        if (old.get("snapshot") == before and old["context_retained"]
                and old.get("case_source_sha256") == digest):
            return old
    command = [str(common.BINARY), "-lang", "en", "-strict",
               "-f", str(USE / "main.lit"), "-session"]
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    records = []
    try:
        for source, success in [(s, True) for s in prefix] + expected:
            process.stdin.write(source + "\n\n")
            process.stdin.flush()
            data = common.read_response(process)
            assert data["kind"] == "run" and data["target"] == "repl", data
            assert not data["session_terminated"] and data["termination"] is None, data
            assert (data["run_result"] == "success") == success, {
                "source": source, "result": data["run_result"], "errors": data["errors"]}
            assert len(data["statement_results"]) == 1, data
            assert len(data["errors"]) == (0 if success else 1), data
            if not success:
                assert data["errors"][0]["phase"] == "premise", data
            records.append({"source": source, "expected_success": success,
                            "errors": data["errors"]})
        process.stdin.write("exit\n")
        process.stdin.flush()
        tail, _ = process.communicate(timeout=60)
        final = json.loads(tail)
        assert process.returncode in (0, 1)
        assert final["run_result"] == "failure" and len(final["errors"]) == 3, final
        assert not final["session_terminated"] and final["termination"] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    assert before == base.checks.snapshot(USE)
    data = {"command": command, "checks": records, "expected_refusals": 3,
            "context_retained": True, "case_source_sha256": digest, "snapshot": before}
    receipt.write_text(json.dumps(data, indent=2) + "\n")
    return data


def main():
    imported = base.file_gate(USE / "main.lit", USE / "imported_gate.json", USE)
    boundary = boundaries()
    data = {"new_public_source_statements": 0, "reused_module": "Algebra",
            "selected_ids": IDS, "imported_consumer": imported, "boundaries": boundary}
    (HERE / "existing_acceptance.json").write_text(json.dumps(data, indent=2) + "\n")
    print("Existing linear maps: 33 imported statements / 3 refusal controls passed")


if __name__ == "__main__":
    main()

