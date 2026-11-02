"""Check standard coordinate bases, including empty and nonreal coordinates."""

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("sum_checks", HERE / "check_sums.py")
sums = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sums)
common = sums.common
ROOT = sums.ROOT


def boundaries():
    command = [str(common.BINARY), "-lang", "en", "-strict", "-f",
               str(HERE / "coordinate_basis/main.lit"), "-session"]
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    valid = r"\Algebra::coordinate_basis::coordinate_projection<C,2,2>(main::coordinate_check_complex)=2+i"
    cases = [(source, True) for source in [
        "release obj def main::coordinate_check_complex", valid,
    ]] + [
        (r"let invalid_coordinate_projection=\Algebra::coordinate_basis::coordinate_projection<C,2,0>", False),
        (valid, True),
        (r"\Algebra::coordinate_basis::coordinate_projection<C,2,2>(main::coordinate_check_complex)=1+i", False),
        (valid, True),
        (r"\Algebra::dimension::finite_dimension<R,Algebra::field::real_field,finite_seq(R,2)>(\Algebra::finite_span::coordinate_space<R,Algebra::field::real_field,2>)=3", False),
        (valid, True),
    ]
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
                assert data["errors"][0]["phase"] in ("requirement", "search_proof", "premise"), data
            records.append({"source": source, "expected_success": expected,
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
    return {"command": command, "checks": records, "expected_refusals": 3,
            "context_retained": True}


def main():
    paths = [common.BINARY, ROOT / "std/algebra/coordinate_basis.lit",
             HERE / "coordinate_basis/main.lit"]
    hashes = [hashlib.sha256(p.read_bytes()).hexdigest() for p in paths]
    data = {"source": sums.file_gate(paths[1], HERE / "coordinate_basis_source_gate.json"),
            "imported_consumer": sums.file_gate(paths[2], HERE / "coordinate_basis_imported_gate.json"),
            "boundaries": boundaries(), "binary_sha256": hashes[0]}
    assert hashes == [hashlib.sha256(p.read_bytes()).hexdigest() for p in paths]
    (HERE / "coordinate_basis_gates.json").write_text(json.dumps(data, indent=2) + "\n")
    print("Coordinate basis: source/import gates and three refusals passed", flush=True)


if __name__ == "__main__":
    main()

