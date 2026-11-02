"""Check supplied-field matrix spaces and exact R/C native compatibility."""

import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
MODULE = ROOT / "std/linear_matrices"
USE = HERE / "use"
spec = importlib.util.spec_from_file_location(
    "matrix_base", ROOT / "std/polynomials/validation/.ladr/check_degree.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
common = base.common


def boundaries():
    journal = json.loads((USE / "session.json").read_text())
    prefix = journal["canonical_positive_sources"]
    assert len(prefix) == journal["accepted_statements"]
    canonical = "# Independent supplied-field matrix-space consumers.\n\n"
    canonical += "\n\n".join(prefix)
    assert (USE / "main.lit").read_text().strip() == canonical.strip()
    expected = [(r["source"], r["expected_success"])
                for r in journal["boundaries"]]
    assert len(expected) == 10 and sum(not success for _, success in expected) == 5
    digest = hashlib.sha256(json.dumps([prefix, expected]).encode()).hexdigest()
    before = base.checks.snapshot(USE)
    receipt = USE / "boundaries.json"
    if receipt.exists():
        old = json.loads(receipt.read_text())
        if (old.get("snapshot") == before and old["context_retained"]
                and old.get("case_source_sha256") == digest):
            return old
    declaration = re.compile(r"^have (?:fn )?([A-Za-z][A-Za-z0-9_]*)")
    names = [declaration.match(s).group(1) for s in prefix if declaration.match(s)]
    assert len(names) == len(set(names)) == journal["global_declarations"], names
    pattern = re.compile(r"\b(" + "|".join(sorted(names, key=len, reverse=True)) + r")\b")
    def qualify(source):
        return pattern.sub(lambda match: "main::" + match.group(), source)
    cases = []
    for source in prefix:
        match = declaration.match(source)
        cases.append(("release obj def main::" + match.group(1), True) if match
                     else (qualify(source), True))
    cases += [(qualify(source), success) for source, success in expected]
    command = [str(common.BINARY), "-lang", "en", "-strict",
               "-f", str(USE / "main.lit"), "-session"]
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    records = []
    try:
        for source, success in cases:
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
                assert data["errors"][0]["phase"] in (
                    "argument_type", "goal_wd", "search_proof"), data
            records.append({"source": source, "expected_success": success,
                            "errors": data["errors"]})
        process.stdin.write("exit\n")
        process.stdin.flush()
        tail, _ = process.communicate(timeout=60)
        final = json.loads(tail)
        assert process.returncode in (0, 1)
        assert final["run_result"] == "failure" and len(final["errors"]) == 5, final
        assert not final["session_terminated"] and final["termination"] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    assert before == base.checks.snapshot(USE)
    data = {"command": command, "checks": records, "expected_refusals": 5,
            "context_retained": True, "case_source_sha256": digest, "snapshot": before}
    receipt.write_text(json.dumps(data, indent=2) + "\n")
    return data


def main():
    space = base.file_gate(MODULE / "space.lit",
                           HERE / "space_26_source_gate.json", MODULE)
    native = base.file_gate(MODULE / "native_compatibility.lit",
                            HERE / "native_38_source_gate.json", MODULE)
    assert space["statements"] == 26 and native["statements"] == 12
    imported = base.file_gate(USE / "main.lit", USE / "imported_gate.json", USE)
    boundary = boundaries()
    data = {"source": {"space": space, "native_compatibility": native},
            "total_module_statements": 38,
            "selected_ids": ["3.29", "3.34", "3.36", "3.39"],
            "imported_consumer": imported, "boundaries": boundary}
    (HERE / "acceptance.json").write_text(json.dumps(data, indent=2) + "\n")
    print(f"Field matrices: 38 source / {imported['statements']} imported / "
          "5 refusal controls passed")


if __name__ == "__main__":
    main()
