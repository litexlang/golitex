"""Check finite complex-sum bounds, inclusive endpoints and required hypotheses."""

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
spec = importlib.util.spec_from_file_location("sum_checks",
    ROOT / "std/algebra/validation/.ladr_ab/check_sums.py")
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
common = checks.common


def main():
    paths = [common.BINARY, ROOT / "std/complex_sums/main.lit", HERE / "main.lit"]
    before = [hashlib.sha256(p.read_bytes()).hexdigest() for p in paths]
    source_gate = checks.file_gate(paths[1], HERE / "source_gate.json")
    imported_gate = checks.file_gate(paths[2], HERE / "imported_gate.json")
    command = [str(common.BINARY), "-lang", "en", "-strict", "-f", str(paths[2]), "-session"]
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    valid = "sum(0,4,main::sum_check_terms)=1+2*i"
    tail = """claim:
    ? forall k N:
        k>1
        =>:
            main::sum_check_terms(k)=0
    main::sum_check_terms(k)=0"""
    cases = [(s, True) for s in [
        "release obj def main::sum_check_terms",
        "sum(0,1,main::sum_check_terms)=sum(0,0,main::sum_check_terms)+main::sum_check_terms(1)=main::sum_check_terms(0)+main::sum_check_terms(1)=i+(1+i)=1+2*i",
        tail,
        "release thm ComplexSums::main::complex_natural_sum_zero_tail(main::sum_check_terms,1,4)",
        "release obj def main::bound_check_coefficients",
        "release thm ComplexSums::main::complex_finite_sequence_moduli_carrier(2,main::bound_check_coefficients)",
        valid,
    ]]
    for negative in [
        "release thm ComplexSums::main::complex_natural_sum_uniform_bound(main::sum_check_terms,1,0)",
        "release thm ComplexSums::main::complex_natural_sum_zero_tail(main::sum_check_terms,0,1)",
        "sum(0,4,main::sum_check_terms)=3",
        r"let invalid_norm_index=\ComplexSums::main::complex_finite_sequence_moduli<2,main::bound_check_coefficients>(0)",
    ]:
        cases.extend([(negative, False), (valid, True)])
    records = []
    try:
        for source, expected in cases:
            process.stdin.write(source + "\n\n")
            process.stdin.flush()
            data = common.read_response(process)
            assert data["kind"] == "run" and data["target"] == "repl", data
            assert not data["session_terminated"] and data["termination"] is None, data
            assert (data["run_result"] == "success") == expected, (source, data)
            assert len(data["statement_results"]) == 1, data
            assert len(data["errors"]) == (0 if expected else 1), data
            if not expected:
                assert data["errors"][0]["phase"] in ("premise", "search_proof", "requirement"), data
            records.append({"source": source, "expected_success": expected,
                            "errors": data["errors"]})
        process.stdin.write("exit\n")
        process.stdin.flush()
        output, _ = process.communicate(timeout=60)
        final = json.loads(output)
        assert process.returncode in (0, 1)
        assert final["run_result"] == "failure" and len(final["errors"]) == 4, final
        assert not final["session_terminated"] and final["termination"] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    assert before == [hashlib.sha256(p.read_bytes()).hexdigest() for p in paths]
    result = {"source": source_gate, "imported_consumer": imported_gate,
              "boundaries": {"command": command, "exit_code": process.returncode,
                             "checks": records, "expected_refusals": 4, "context_retained": True}}
    (HERE / "acceptance.json").write_text(json.dumps(result, indent=2) + "\n")
    print("Complex finite sums: 10 source / 45 imported / 4 refusal controls passed")


if __name__ == "__main__":
    main()

