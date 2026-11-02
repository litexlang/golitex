"""Validate finite subspace family sums and their family/index guards."""

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
spec = importlib.util.spec_from_file_location("sum_checks", HERE / "check_sums.py")
sums = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sums)
common = sums.common


def boundaries():
    command = [str(common.BINARY), "-lang", "en", "-strict", "-f", str(HERE / "family_use.lit"), "-session"]
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    args = "R,Algebra::field::real_field,finite_seq(R,2),main::plane"
    valid = "main::plane.zero $in family_use::empty_sum"
    cases = [(s, True) for s in [
        "release obj def Algebra::field::real_field",
        "release struct def Algebra::field::real_field",
        "release obj def main::plane",
        "release struct def main::plane",
        "release obj def main::u",
        "main::u(2)=2",
        "release obj def family_use::empty_family",
        "release obj def family_use::empty_sum",
        "release thm Algebra::subspace_sums::empty_is_subspace_family(" + args + ",family_use::empty_family)",
        "release thm Algebra::subspace_sums::finite_subspace_sum_zero(" + args + ",0,family_use::empty_family)",
        valid,
    ]] + [
        ("let invalid_family_sum=\\Algebra::subspace_sums::finite_subspace_sum<" + args + ",1,family_use::invalid_family>", False), (valid, True),
        ("main::u $in family_use::empty_sum", False), (valid, True),
        ("release thm Algebra::subspace_sums::finite_subspace_sum_contains_summand(" + args + ",3,family_use::whole_family,0)", False), (valid, True),
    ]
    records = []
    try:
        for source, expected in cases:
            process.stdin.write(source + "\n\n"); process.stdin.flush()
            data = common.read_response(process)
            assert data["kind"] == "run" and data["target"] == "repl", data
            assert not data["session_terminated"] and data["termination"] is None, data
            assert (data["run_result"] == "success") == expected, (source, data)
            assert len(data["statement_results"]) == 1, data
            assert data["statement_results"][0]["statement_result"] == ("accepted" if expected else "rejected"), data
            assert len(data["errors"]) == (0 if expected else 1), data
            if not expected:
                error = data["errors"][0]
                assert error["phase"] in ("premise", "search_proof", "requirement", "argument_type"), data
                if "invalid_family_sum" in source:
                    assert "is_subspace_family" in error.get("obligation", ""), data
                elif "contains_summand" in source:
                    assert "0 $in closed_range(1, 3)" in error.get("obligation", ""), data
            records.append({"source": source, "expected_success": expected, "errors": data["errors"]})
        process.stdin.write("exit\n"); process.stdin.flush()
        tail, _ = process.communicate(timeout=60); final = json.loads(tail)
        assert process.returncode in (0, 1), process.returncode
        assert final["run_result"] == "failure" and len(final["errors"]) == 3, final
        assert not final["session_terminated"] and final["termination"] is None, final
    finally:
        if process.poll() is None:
            process.kill(); process.wait()
    print("Subspace-family Session: 3 expected refusals; context retained", flush=True)
    return {"command": command, "checks": records, "expected_refusals": 3, "context_retained": True}


def main():
    gates = {
        "source": sums.file_gate(ROOT / "std/algebra/subspace_sums.lit", HERE / "family_source_gate.json"),
        "imported_consumer": sums.file_gate(HERE / "family_use.lit", HERE / "family_imported_gate.json"),
        "boundaries": boundaries(),
        "binary_sha256": hashlib.sha256(common.BINARY.read_bytes()).hexdigest(),
    }
    assert gates["source"]["binary_sha256"] == gates["imported_consumer"]["binary_sha256"] == gates["binary_sha256"]
    (HERE / "family_gates.json").write_text(json.dumps(gates, indent=2) + "\n")


if __name__ == "__main__":
    main()
