"""Check native complex power coefficients and the exact hypotheses they require."""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
spec = importlib.util.spec_from_file_location(
    "std_checks", ROOT / "std/algebra/validation/.standard_fields/check.py")
common = importlib.util.module_from_spec(spec)
spec.loader.exec_module(common)
MODULE = ROOT / "std/complex_sums"
SOURCE_PATHS = [MODULE / name for name in
                ("litex.config", "main.lit", "growth.lit", "coefficients.lit")]
USE_PATHS = SOURCE_PATHS + [HERE / "litex.config", HERE / "main.lit"]


def snapshot(paths):
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in paths} | {
                "binary": hashlib.sha256(common.BINARY.read_bytes()).hexdigest()}


def file_gate(path, receipt, paths):
    before = snapshot(paths)
    if receipt.exists():
        data = json.loads(receipt.read_text())
        if (data.get("snapshot") == before and data["run_result"] == "success"
                and data["all_statements_accepted"]):
            return data
    data = common.successful_file(path)
    assert snapshot(paths) == before, "Consumed sources changed during verification"
    data["snapshot"] = before
    receipt.write_text(json.dumps(data, indent=2) + "\n")
    return data


def boundaries(force=False):
    receipt = HERE / "boundaries.json"
    before = snapshot(USE_PATHS)
    if receipt.exists() and not force:
        data = json.loads(receipt.read_text())
        if data.get("snapshot") == before and data["context_retained"]:
            return data
    journal = json.loads((HERE / "session.json").read_text())
    prefix = [r["source"] for r in journal["runs"]
              if r["response"]["run_result"] == "success"]
    assert len(prefix) == journal["accepted_statements"]
    names = ("linear_coefficients", "linear_value", "padded_coefficients",
             "padded_for_representation", "empty_coefficients", "zero_value",
             "zero_terms", "zero_coefficients")
    pattern = re.compile(r"\b(" + "|".join(names) + r")\b")
    def qualify(source):
        return pattern.sub(lambda match: "main::" + match.group(), source)
    cases = [("release obj def main::" + name, True) for name in names[:-1]]
    cases += [(qualify(s), True) for s in prefix
              if not s.startswith(("have ", "template<"))]
    cases += [(qualify(r["source"]), r["expected_success"])
              for r in journal["boundaries"]]
    command = [str(common.BINARY), "-lang", "en", "-strict",
               "-f", str(HERE / "main.lit"), "-session"]
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
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
        assert final["run_result"] == "failure" and len(final["errors"]) == 7, final
        assert not final["session_terminated"] and final["termination"] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    assert snapshot(USE_PATHS) == before, "Consumed sources changed during Session"
    data = {"origin": "clean_retained_session", "command": command,
            "checks": records, "expected_refusals": 7,
            "context_retained": True, "snapshot": before}
    receipt.write_text(json.dumps(data, indent=2) + "\n")
    return data


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--refresh-boundaries", action="store_true")
    args = parser.parse_args()
    source = file_gate(MODULE / "coefficients.lit", HERE / "source_gate.json", SOURCE_PATHS)
    imported = file_gate(HERE / "main.lit", HERE / "imported_gate.json", USE_PATHS)
    boundary = boundaries(args.refresh_boundaries)
    result = {"source": source, "imported_consumer": imported, "boundaries": boundary}
    (HERE / "acceptance.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Complex power coefficients: {source['statements']} source / "
          f"{imported['statements']} imported / 7 refusal controls passed")


if __name__ == "__main__":
    main()

