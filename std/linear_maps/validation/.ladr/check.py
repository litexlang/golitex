"""Check original-hypothesis inverse and isomorphism source interfaces."""

import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
MODULE = ROOT / "std/linear_maps"
USE = HERE / "use"
spec = importlib.util.spec_from_file_location("degree_checks",
    ROOT / "std/polynomials/validation/.ladr/check_degree.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
common = base.common


def boundaries():
    journal = json.loads((USE / "session.json").read_text())
    prefix = [r["source"] for r in journal["runs"]
              if r["response"]["run_result"] == "success"]
    assert len(prefix) == journal["accepted_statements"] == 72
    canonical = "# Independent two-sided inverse and isomorphism consumers.\n\n"
    canonical += "\n\n".join(prefix)
    assert (USE / "main.lit").read_text().strip() == canonical.strip()
    expected = [(r["source"], r["expected_success"]) for r in journal["boundaries"]]
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
    assert len(names) == len(set(names)) == 6, names
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
        for source, expected_success in cases:
            process.stdin.write(source + "\n\n")
            process.stdin.flush()
            data = common.read_response(process)
            assert data["kind"] == "run" and data["target"] == "repl", data
            assert not data["session_terminated"] and data["termination"] is None, data
            assert (data["run_result"] == "success") == expected_success, {
                "source": source, "result": data["run_result"], "errors": data["errors"]}
            assert len(data["statement_results"]) == 1, data
            assert len(data["errors"]) == (0 if expected_success else 1), data
            if not expected_success:
                assert data["errors"][0]["phase"] == "premise", data
            records.append({"source": source, "expected_success": expected_success,
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
    source = base.file_gate(MODULE / "identity_compositions.lit",
                           HERE / "source_gate.json", MODULE)
    imported = base.file_gate(USE / "main.lit", USE / "imported_gate.json", USE)
    boundary = boundaries()
    result = {"source": source, "registered_predecessor_statements":
              {"inverse": 10, "dimension": 5}, "total_module_statements": 19,
              "imported_consumer": imported, "boundaries": boundary}
    (HERE / "acceptance.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Linear inverses: {source['statements']} final source / "
          f"{imported['statements']} imported / 5 refusal controls passed")


if __name__ == "__main__":
    main()

