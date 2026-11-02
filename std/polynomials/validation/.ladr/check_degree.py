"""Check total polynomial degrees, legacy bounded spaces and strict domains."""

import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
USE = HERE / "degree_use"
spec = importlib.util.spec_from_file_location("coefficient_checks",
    HERE / "check_coefficients.py")
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
common = checks.common


def file_gate(path, receipt, module):
    before = checks.snapshot(module)
    if receipt.exists():
        data = json.loads(receipt.read_text())
        if (data.get("snapshot") == before and data["run_result"] == "success"
                and data["all_statements_accepted"]):
            return data
    command = [str(common.BINARY), "-lang", "en", "-strict", "-f", str(path)]
    result = subprocess.run(command, cwd=ROOT, env=common.ENV, text=True,
                            capture_output=True, timeout=1800)
    data = json.loads(result.stdout)
    assert result.returncode == 0 and data["kind"] == "run", {
        "exit_code": result.returncode, "result": data.get("run_result"),
        "errors": data.get("errors"), "termination": data.get("termination")}
    assert data["run_result"] == "success" and not data["errors"]
    assert not data["session_terminated"] and data["termination"] is None
    assert all(s["statement_result"] == "accepted" for s in data["statement_results"])
    assert before == checks.snapshot(module), "Consumed sources changed during verification"
    record = {"command": command, "exit_code": result.returncode, "kind": "run",
              "run_result": "success", "session_terminated": False, "termination": None,
              "statements": len(data["statement_results"]), "all_statements_accepted": True,
              "errors": [], "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
              "binary_sha256": before["binary"], "snapshot": before}
    receipt.write_text(json.dumps(record, indent=2) + "\n")
    print(f"{path.relative_to(ROOT)}: {record['statements']} accepted", flush=True)
    return record


def boundaries():
    journal = json.loads((USE / "consumer_session.json").read_text())
    prefix = [r["source"] for r in journal["runs"]
              if r["response"]["run_result"] == "success"
              and r["response"]["target"] == "repl"
              and len(r["response"]["statement_results"]) == 1]
    assert len(prefix) == journal["accepted_statements"] == 163
    canonical = "# Independent exact-degree and bounded-polynomial consumers.\n\n"
    canonical += "\n\n".join(prefix)
    assert (USE / "main.lit").read_text().strip() == canonical.strip()
    expected = [(r["source"], r["expected_success"]) for r in journal["boundaries"]]
    assert len(expected) == 20 and sum(not success for _, success in expected) == 10
    plan_digest = hashlib.sha256(json.dumps([prefix, expected]).encode()).hexdigest()
    receipt = USE / "boundaries.json"
    before = checks.snapshot(USE)
    if receipt.exists():
        data = json.loads(receipt.read_text())
        if (data.get("snapshot") == before and data["context_retained"]
                and data.get("case_source_sha256") == plan_digest):
            return data
    names = [re.match(r"have (?:fn )?([A-Za-z][A-Za-z0-9_]*)", source).group(1)
             for source in prefix if source.startswith("have ")]
    assert len(names) == len(set(names)) == 16, names
    pattern = re.compile(r"\b(" + "|".join(sorted(names, key=len, reverse=True)) + r")\b")
    def qualify(source):
        return pattern.sub(lambda match: "main::" + match.group(), source)
    cases = [("release obj def main::" + name, True) for name in names]
    cases += [(qualify(source), True) for source in prefix
              if not source.startswith("have ")]
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
                assert data["errors"][0]["phase"] == "search_proof", data
            records.append({"source": source, "expected_success": success,
                            "errors": data["errors"]})
        process.stdin.write("exit\n")
        process.stdin.flush()
        tail, _ = process.communicate(timeout=60)
        final = json.loads(tail)
        assert process.returncode in (0, 1)
        assert final["run_result"] == "failure" and len(final["errors"]) == 10, final
        assert not final["session_terminated"] and final["termination"] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    assert before == checks.snapshot(USE), "Consumed sources changed during Session"
    data = {"command": command, "checks": records, "expected_refusals": 10,
            "context_retained": True, "case_source_sha256": plan_digest, "snapshot": before}
    receipt.write_text(json.dumps(data, indent=2) + "\n")
    return data


def main():
    source = file_gate(checks.MODULE / "degree.lit", HERE / "degree_source_gate.json", checks.MODULE)
    imported = file_gate(USE / "main.lit", USE / "imported_gate.json", USE)
    boundary = boundaries()
    result = {"source": source, "registered_prefix_statements":
              {"coefficients": 9, "truncation": 5, "finite_degree": 13,
               "bounded_degree": 6, "degree_value": 21},
              "total_registered_source_statements": 87,
              "imported_consumer": imported, "boundaries": boundary}
    (HERE / "degree_acceptance.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Polynomial degrees: {source['statements']} source / "
          f"{imported['statements']} imported / 10 refusal controls passed")


if __name__ == "__main__":
    main()

