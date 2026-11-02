"""Validate Field-to-VectorSpace scalar lines and their field/sign boundaries."""

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
    command = [str(common.BINARY), "-lang", "en", "-strict", "-f", str(HERE / "scalar_use.lit"), "-session"]
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    valid = "scalar_marker+1=3"
    cases = [(s, True) for s in [
        "release obj def Algebra::field::real_field",
        "release struct def Algebra::field::real_field",
        "release obj def Algebra::field::complex_field",
        "release struct def Algebra::field::complex_field",
        "release obj def scalar_use::real_scalars",
        "release struct def scalar_use::real_scalars",
        "release obj def scalar_use::complex_scalars",
        "release struct def scalar_use::complex_scalars",
        "have scalar_marker R=2",
    ]] + [
        ("let wrong_real_scalar=scalar_use::real_scalars.smul(i,3)", False), (valid, True),
        ("scalar_use::complex_scalars.smul(i,i)=1", False), (valid, True),
        ("\\Algebra::vector_space::vector_neg<R,Algebra::field::real_field,R,scalar_use::real_scalars>(3)=3", False), (valid, True),
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
                assert data["errors"][0]["phase"] in ("search_proof", "argument_type"), data
                if "wrong_real_scalar" in source:
                    assert "i $in R" in data["errors"][0].get("obligation", ""), data
            records.append({"source": source, "expected_success": expected, "errors": data["errors"]})
        process.stdin.write("exit\n"); process.stdin.flush()
        tail, _ = process.communicate(timeout=60); final = json.loads(tail)
        assert process.returncode in (0, 1), process.returncode
        assert final["run_result"] == "failure" and len(final["errors"]) == 3, final
        assert not final["session_terminated"] and final["termination"] is None, final
    finally:
        if process.poll() is None:
            process.kill(); process.wait()
    print("Scalar-space Session: 3 expected field/sign refusals; context retained", flush=True)
    return {"command": command, "checks": records, "expected_refusals": 3, "context_retained": True}


def main():
    gates = {
        "source": sums.file_gate(ROOT / "std/algebra/vector_space.lit", HERE / "scalar_source_gate.json"),
        "imported_consumer": sums.file_gate(HERE / "scalar_use.lit", HERE / "scalar_imported_gate.json"),
        "boundaries": boundaries(),
        "binary_sha256": hashlib.sha256(common.BINARY.read_bytes()).hexdigest(),
    }
    assert gates["source"]["binary_sha256"] == gates["imported_consumer"]["binary_sha256"] == gates["binary_sha256"]
    (HERE / "scalar_gates.json").write_text(json.dumps(gates, indent=2) + "\n")


if __name__ == "__main__":
    main()
