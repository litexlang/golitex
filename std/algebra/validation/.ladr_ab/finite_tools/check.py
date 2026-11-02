"""Verify finite-space additions and their independent use against one module snapshot."""

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tomllib

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("sum_checks", HERE.parent / "check_sums.py")
sums = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sums)
common = sums.common
ROOT = sums.ROOT
MODULE = ROOT / "std/algebra"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot():
    manifest = MODULE / "litex.config"
    exports = tomllib.loads(manifest.read_text())["export"]
    paths = [common.BINARY, manifest, HERE / "litex.config", HERE / "main.lit",
             HERE / "subspaces.lit"] + [MODULE / value for value in exports.values()]
    return {str(p.relative_to(ROOT)): digest(p) for p in paths}


def clean_file(path, label):
    complete = snapshot()
    fixtures = {str((HERE / name).relative_to(ROOT))
                for name in ("litex.config", "main.lit", "subspaces.lit")}
    excluded = fixtures if label == "source" else (
        {str((HERE / "main.lit").relative_to(ROOT))} if label == "subspaces" else set())
    before = {key: value for key, value in complete.items() if key not in excluded}
    record_path = HERE / (label + "_gate.json")
    if record_path.exists():
        cached = json.loads(record_path.read_text())
        recorded = cached.get("module_snapshot", {})
        if ({key: recorded.get(key) for key in before} == before
                and cached["run_result"] == "success"):
            cached["cache_validated_dependencies"] = before
            return cached
    print("Checking " + label + " with strict source verification", flush=True)
    command = [str(common.BINARY), "-lang", "en", "-strict", "-f", str(path)]
    result = subprocess.run(command, cwd=ROOT, env=common.ENV, text=True,
                            capture_output=True, timeout=1800)
    data = json.loads(result.stdout)
    good = (result.returncode == 0 and data["kind"] == "run"
            and data["run_result"] == "success" and not data["errors"]
            and not data["session_terminated"] and data["termination"] is None
            and all(s["statement_result"] == "accepted" for s in data["statement_results"]))
    if not good:
        (HERE / (label + "_failure.json")).write_text(json.dumps(data, indent=2) + "\n")
        failures = [{k: e.get(k) for k in ("phase", "obligation", "message")}
                    for e in data.get("errors", [])]
        raise AssertionError(json.dumps(failures))
    current = {key: value for key, value in snapshot().items() if key not in excluded}
    assert before == current, "Source or executable changed during verification"
    record = {"command": command, "exit_code": result.returncode, "kind": data["kind"],
              "run_result": data["run_result"], "statements": len(data["statement_results"]),
              "all_statements_accepted": True, "session_terminated": False,
              "termination": None, "errors": [], "module_snapshot": before,
              "source_sha256": digest(path), "binary_sha256": digest(common.BINARY)}
    record_path.write_text(json.dumps(record, indent=2) + "\n")
    print(label + ": " + str(record["statements"]) + " accepted", flush=True)
    return record


def boundaries():
    command = [str(common.BINARY), "-lang", "en", "-strict", "-f",
               str(HERE / "main.lit"), "-session"]
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    valid = r"\Algebra::infinite_dimension::coordinate_zero_extension<C,Algebra::field::complex_field,2>(main::extension_check_nonreal)(3)=0"
    prefix = [
        "release obj def Algebra::field::real_field",
        "release struct def Algebra::field::real_field",
        "release obj def Algebra::field::complex_field",
        "release struct def Algebra::field::complex_field",
        "release obj def main::extension_check_nonreal",
        "release obj def main::removal_check_space",
        "release obj def main::removal_check_empty",
        "release thm Algebra::finite_span::coordinate_space_carrier(R,Algebra::field::real_field,2)",
        "release thm Algebra::coordinate_basis::coordinate_space_is_finite_dimensional(R,Algebra::field::real_field,2)",
        "release thm Algebra::dependence::empty_list_is_independent(R,Algebra::field::real_field,R,main::removal_check_space,main::removal_check_empty)",
        "release thm Algebra::infinite_dimension::coordinate_zero_extension_tail(C,Algebra::field::complex_field,2,main::extension_check_nonreal,3)",
        valid,
    ]
    negatives = [
        "release thm Algebra::dependent_removal::dependent_list_has_redundant_predecessor(R,Algebra::field::real_field,R,main::removal_check_space,0,main::removal_check_empty)",
        r"$Algebra::direct_sum::is_internal_direct_sum(R,Algebra::field::real_field,finite_seq(R,2),\Algebra::finite_span::coordinate_space<R,Algebra::field::real_field,2>,finite_seq(R,2),finite_seq(R,2))",
        r"$Algebra::infinite_dimension::is_infinite_dimensional(R,Algebra::field::real_field,finite_seq(R,2),\Algebra::finite_span::coordinate_space<R,Algebra::field::real_field,2>)",
        r"\Algebra::infinite_dimension::coordinate_zero_extension<C,Algebra::field::complex_field,2>(main::extension_check_nonreal)(3)=1",
    ]
    cases = [(s, True) for s in prefix]
    for negative in negatives:
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
                assert data["errors"][0]["phase"] in ("premise", "search_proof"), data
            records.append({"source": source, "expected_success": expected,
                            "errors": data["errors"]})
        process.stdin.write("exit\n")
        process.stdin.flush()
        tail, _ = process.communicate(timeout=60)
        final = json.loads(tail)
        assert process.returncode in (0, 1)
        assert final["run_result"] == "failure" and len(final["errors"]) == 4, final
        assert not final["session_terminated"] and final["termination"] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    return {"command": command, "exit_code": process.returncode, "checks": records,
            "expected_refusals": 4, "context_retained": True}


def main():
    before = snapshot()
    data = {"canonical_source": clean_file(MODULE / "infinite_dimension.lit", "source"),
            "subspace_reuse": clean_file(HERE / "subspaces.lit", "subspaces"),
            "imported_consumer": clean_file(HERE / "main.lit", "imported")}
    print("Checking four Session refusals with the same source snapshot", flush=True)
    data["boundaries"] = boundaries()
    assert before == snapshot()
    data["module_snapshot"] = before
    (HERE / "acceptance.json").write_text(json.dumps(data, indent=2) + "\n")
    print("Finite-space tools and infinite scalar sequences: all gates passed", flush=True)


if __name__ == "__main__":
    main()

