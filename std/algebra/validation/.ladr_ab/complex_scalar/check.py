"""Replay complex scalar concordance and reject invalid inverse/coordinate laws."""

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("sum_checks", HERE.parent / "check_sums.py")
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
common = checks.common


def main():
    paths = [common.BINARY, HERE / "main.lit"]
    before = [hashlib.sha256(p.read_bytes()).hexdigest() for p in paths]
    gate = checks.file_gate(paths[1], HERE / "file_gate.json")
    command = [str(common.BINARY), "-lang", "en", "-strict", "-f", str(paths[1]), "-session"]
    process = subprocess.Popen(command, cwd=checks.ROOT, env=common.ENV, text=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    valid = "(1+i)*(1-i)=2"
    cases = [(valid, True), ("let invalid_inverse=1/0", False), (valid, True),
             ("img(1+i)=i", False), (valid, True),
             ("(1+i)*(1-i)=0", False), (valid, True)]
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
                assert data["errors"][0]["phase"] in ("requirement", "search_proof"), data
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
    assert before == [hashlib.sha256(p.read_bytes()).hexdigest() for p in paths]
    receipt = {"source": gate, "boundaries": {"command": command, "exit_code": process.returncode, "checks": records,
               "expected_refusals": 3, "context_retained": True},
               "source_items": ["1.1", "1.3", "1.5"],
               "classification": "Reuse of native complex coordinates and arithmetic; no new interface."}
    (HERE / "acceptance.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("Complex scalars: 9 source claims and 3 retained-context refusals passed")


if __name__ == "__main__":
    main()

