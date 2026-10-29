"""Check positive finite limit-comparison consumers and premise boundaries."""

from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BINARY = ROOT / "target/release/litex"
ENV = {**os.environ, "LITEX_STD_PATH": str(ROOT / "std")}
CASES = [
    (HERE / "main.lit", True),
    (HERE / "negative/missing_limit.lit", False),
    (HERE / "negative/missing_denominator.lit", False),
    (HERE / "negative/zero_limit.lit", False),
]


def check(case):
    path, expected_success = case
    result = subprocess.run(
        [str(BINARY), "-lang", "en", "-strict", "-f", str(path)],
        cwd=ROOT, env=ENV, text=True, capture_output=True, timeout=240,
    )
    data = json.loads(result.stdout)
    assert data["kind"] == "run", data
    assert data["session_terminated"] is False and data["termination"] is None, data
    statements = data["statement_results"]
    assert statements, data
    if expected_success:
        assert result.returncode == 0 and data["run_result"] == "success", data
        assert not data["errors"], data
        assert all(item["statement_result"] == "accepted" for item in statements), data
    else:
        assert result.returncode == 1 and data["run_result"] == "failure", data
        assert all(item["statement_result"] == "accepted" for item in statements[:-1]), data
        assert statements[-1]["statement_result"] == "rejected", data
        assert len(data["errors"]) == 1, data
        assert data["errors"][0]["statement_index"] == len(statements) - 1, data
        assert data["errors"][0]["phase"] == "premise", data
    return f"{path.relative_to(HERE)}: {'accepted' if expected_success else 'premise rejected'}"


def main():
    with ThreadPoolExecutor(max_workers=3) as pool:
        for result in pool.map(check, CASES):
            print(result, flush=True)


if __name__ == "__main__":
    main()
