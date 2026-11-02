"""Check same-bound polynomial evaluation laws and missing premises."""

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
    command = [str(common.BINARY), "-lang", "en", "-strict", "-f", str(HERE / "poly_laws_use.lit"), "-session"]
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    valid = "poly_use::nonreal_polynomial(2)=5+3*i"
    cases = [(s, True) for s in [
        "release obj def Algebra::field::complex_field",
        "release struct def Algebra::field::complex_field",
        "release obj def Algebra::field::complex_mul",
        "release obj def Algebra::field::real_field",
        "release struct def Algebra::field::real_field",
        "release obj def Algebra::field::real_mul",
        "release obj def poly_use::nonreal_coefficients",
        "release obj def poly_use::nonreal_polynomial",
        "release thm Algebra::polynomial::complex_polynomial_function_carrier(poly_use::nonreal_polynomial)",
        "release thm poly_use::nonreal_value",
        "release obj def poly_laws_use::doubled_coefficients",
        "release obj def poly_laws_use::zeroed_coefficients",
        valid,
    ]] + [
        ("release thm Algebra::polynomial::complex_polynomial_value_smul(1,poly_use::nonreal_coefficients,poly_use::nonreal_coefficients,2,2)", False), (valid, True),
        ("\\Algebra::polynomial::complex_polynomial_value<1>(poly_laws_use::doubled_coefficients,2)=10-6*i", False), (valid, True),
        ("\\Algebra::polynomial::real_polynomial_value<1>(poly_laws_use::zeroed_coefficients,2)=1", False), (valid, True),
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
                if source.startswith("release thm"):
                    assert error["phase"] == "premise", data
                else:
                    assert error["phase"] == "search_proof", data
            records.append({"source": source, "expected_success": expected, "errors": data["errors"]})
        process.stdin.write("exit\n"); process.stdin.flush()
        tail, _ = process.communicate(timeout=60); final = json.loads(tail)
        assert process.returncode in (0, 1), process.returncode
        assert final["run_result"] == "failure" and len(final["errors"]) == 3, final
        assert not final["session_terminated"] and final["termination"] is None, final
    finally:
        if process.poll() is None:
            process.kill(); process.wait()
    print("Polynomial-law Session: missing relation and two false values rejected; context retained", flush=True)
    return {"command": command, "checks": records, "expected_refusals": 3, "context_retained": True}


def main():
    source_before = hashlib.sha256((HERE / "poly_laws_use.lit").read_bytes()).hexdigest()
    before = hashlib.sha256(common.BINARY.read_bytes()).hexdigest()
    polynomial_before = hashlib.sha256((ROOT / "std/algebra/polynomial.lit").read_bytes()).hexdigest()
    gates = {
        "source": sums.file_gate(ROOT / "std/algebra/polynomial.lit", HERE / "polynomial_laws_source_gate.json"),
        "imported_consumer": sums.file_gate(HERE / "poly_laws_use.lit", HERE / "polynomial_laws_imported_gate.json"),
        "boundaries": boundaries(), "binary_sha256": before, "source_sha256": source_before,
    }
    assert hashlib.sha256(common.BINARY.read_bytes()).hexdigest() == before
    assert hashlib.sha256((HERE / "poly_laws_use.lit").read_bytes()).hexdigest() == source_before, "Consumer changed during verification"
    assert hashlib.sha256((ROOT / "std/algebra/polynomial.lit").read_bytes()).hexdigest() == polynomial_before, "Polynomial source changed during verification"
    assert gates["source"]["binary_sha256"] == gates["imported_consumer"]["binary_sha256"] == before
    (HERE / "polynomial_laws_gates.json").write_text(json.dumps(gates, indent=2) + "\n")



if __name__ == "__main__":
    main()
