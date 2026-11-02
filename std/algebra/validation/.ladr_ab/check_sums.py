"""Check finite vector-list sums, actual coordinates and missing premises."""

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
spec = importlib.util.spec_from_file_location("std_checks", HERE.parent / ".standard_fields/check.py")
common = importlib.util.module_from_spec(spec)
spec.loader.exec_module(common)


def file_gate(path, record):
    if record.exists():
        data = json.loads(record.read_text())
        if (data["source_sha256"] == hashlib.sha256(path.read_bytes()).hexdigest()
                and data["binary_sha256"] == hashlib.sha256(common.BINARY.read_bytes()).hexdigest()
                and data["run_result"] == "success" and data["all_statements_accepted"]):
            return data
    data = common.successful_file(path)
    record.write_text(json.dumps(data, indent=2) + "\n")
    return data


def boundaries():
    command = [str(common.BINARY), "-lang", "en", "-strict", "-f", str(HERE / "sum_use.lit"), "-session"]
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    valid = "sum_use::sum_trace(3)(2)=6"
    cases = [(s, True) for s in [
        "release obj def sum_use::sum_trace",
        "release obj def sum_use::sum_value",
        valid,
    ]] + [
        ("sum_use::sum_value(2)=7", False), (valid, True),
        ("release thm Algebra::finite_span::vector_list_sum_add(R,Algebra::field::real_field,finite_seq(R,2),main::plane,3,sum_use::repeated,sum_use::repeated,sum_use::repeated)", False), (valid, True),
        ("let invalid_trace_point=sum_use::sum_trace(4)", False), (valid, True),
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
                assert data["errors"][0]["phase"] in ("premise", "search_proof"), data
            records.append({"source": source, "expected_success": expected, "errors": data["errors"]})
        process.stdin.write("exit\n"); process.stdin.flush()
        tail, _ = process.communicate(timeout=60); final = json.loads(tail)
        assert process.returncode in (0, 1), process.returncode
        assert final["run_result"] == "failure" and len(final["errors"]) == 3, final
        assert not final["session_terminated"] and final["termination"] is None, final
    finally:
        if process.poll() is None:
            process.kill(); process.wait()
    print("Vector-list sum Session: 3 expected refusals; context retained", flush=True)
    return {"command": command, "checks": records, "expected_refusals": 3, "context_retained": True}


def main():
    gates = {
        "source": file_gate(ROOT / "std/algebra/finite_span.lit", HERE / "sum_source_gate.json"),
        "imported_consumer": file_gate(HERE / "sum_use.lit", HERE / "sum_imported_gate.json"),
        "boundaries": boundaries(),
        "binary_sha256": hashlib.sha256(common.BINARY.read_bytes()).hexdigest(),
    }
    assert gates["source"]["binary_sha256"] == gates["imported_consumer"]["binary_sha256"] == gates["binary_sha256"]
    (HERE / "sum_gates.json").write_text(json.dumps(gates, indent=2) + "\n")


if __name__ == "__main__":
    main()
