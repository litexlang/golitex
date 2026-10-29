"""Check full std ring consumers and focused source refusal boundaries."""

import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BINARY = ROOT / "target/release/litex"
ENV = {**os.environ, "LITEX_STD_PATH": str(ROOT / "std")}
CASES = [
    (HERE / "main.lit", None),
    (HERE / "negative/nonunital_zero_map.lit", "definition_requirement"),
    (HERE / "negative/kernel_without_homomorphism.lit", "premise"),
    (HERE / "negative/zero_ideal_need_not_contain_one.lit", "search_proof"),
    (HERE / "negative/full_kernel_not_injective.lit", "premise"),
    (HERE / "negative/zero_ring_is_not_field.lit", "membership"),
]


def check(case):
    path, expected_phase = case
    expected_success = expected_phase is None
    result = subprocess.run(
        [str(BINARY), "-lang", "en", "-strict", "-f", str(path)],
        cwd=ROOT, env=ENV, text=True, capture_output=True, timeout=600,
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
        assert data["errors"][0]["phase"] == expected_phase, data
    return f"{path.relative_to(HERE)}: {'accepted' if expected_success else expected_phase + ' rejected'}"


def main():
    for case in CASES:
        print(check(case), flush=True)


if __name__ == "__main__":
    main()
