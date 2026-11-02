"""Verify isolated linear-algebra planning prototypes, not public delivery."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
USE = HERE / "use"
spec = importlib.util.spec_from_file_location(
    "planning_base", ROOT / "std/polynomials/validation/.ladr/check_degree.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
common = base.common

def boundaries():
    journal = json.loads((USE / "session.json").read_text())
    prefix = [r["source"] for r in journal["runs"] if r["response"]["run_result"] == "success"]
    assert len(prefix) == journal["accepted_statements"] == 14
    assert (USE / "main.lit").read_text().strip() == (
        "# Independent use of isolated core-planning interface prototypes.\n\n"
        + "\n\n".join(prefix)).strip()
    cases = [(s, True) for s in prefix]
    cases += [
        ("release obj def p::planning_bad_real_pair", True),
        ("p::planning_bad_real_pair(1,1)=-1", True),
        ("release obj def p::planning_test_matrix", True),
        ("p::planning_test_matrix $in matrix(R,2,3)", True),
        ("release obj def Algebra::field::real_field", True),
        ("release thm Algebra::vector_space::scalar_space_carrier(R,Algebra::field::real_field)", True)]
    cases += [(r["source"], r["expected_success"]) for r in journal["boundaries"]]
    assert len(journal["boundaries"]) == 8
    before = base.checks.snapshot(USE)
    digest = hashlib.sha256(json.dumps(cases).encode()).hexdigest()
    path = USE / "boundaries.json"
    if path.exists():
        data = json.loads(path.read_text())
        if data["snapshot"] == before and data["case_source_sha256"] == digest:
            return data
    command = [str(common.BINARY), "-lang", "en", "-strict",
               "-f", str(USE / "main.lit"), "-session"]
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    checks = []
    try:
        for source, success in cases:
            process.stdin.write(source + "\n\n")
            process.stdin.flush()
            response = common.read_response(process)
            assert response["target"] == "repl" and response["kind"] == "run", response
            assert response["session_terminated"] is False and response["termination"] is None, response
            assert len(response["statement_results"]) == 1, response
            assert (response["run_result"] == "success") == success, {
                "source": source, "response": response}
            assert len(response["errors"]) == (0 if success else 1), response
            if not success:
                assert response["errors"][0]["phase"] in (
                    "goal_wd", "well_defined", "requirement", "search_proof"), response
                if "planning_matrix_column" in source:
                    assert "0" in response["errors"][0].get("obligation", ""), response
            checks.append({"source": source, "expected_success": success, "errors": response["errors"]})
        process.stdin.write("exit\n")
        process.stdin.flush()
        tail, _ = process.communicate(timeout=60)
        final = json.loads(tail)
        assert process.returncode in (0,1)
        assert final["run_result"] == "failure" and len(final["errors"]) == 4, final
        assert final["session_terminated"] is False and final["termination"] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    assert before == base.checks.snapshot(USE)
    data = {"snapshot": before, "case_source_sha256": digest, "checks": checks,
            "expected_refusals": 4, "context_retained": True, "command": command}
    path.write_text(json.dumps(data, indent=2) + "\n")
    print("Planning boundaries: four mathematical/WD refusals, retained context", flush=True)
    return data

def main():
    source = base.file_gate(HERE/"main.lit", HERE/"source_gate.json", HERE)
    imported = base.file_gate(USE/"main.lit", USE/"imported_gate.json", USE)
    assert source["statements"] == 54 and imported["statements"] == 14
    boundary = boundaries()
    result = {"scope": "Isolated planning evidence; no public std or LADR item acceptance.",
              "source": source, "independent_use": imported, "boundaries": boundary}
    (HERE/"acceptance.json").write_text(json.dumps(result,indent=2)+"\n")
    print("Planning prototypes: 54 source / 14 imported / 4 refusal controls passed", flush=True)

if __name__ == "__main__":
    main()
